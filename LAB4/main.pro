implement main
open core, console

constants
    className = "main".
    classVersion = "".


/* МЕТОД ИТЕРАЦИЙ */

class facts
	итер: (integer, real) determ.  /* n, z */
class predicates
	квадрат_итер: (real, integer, integer, real) determ (i, i, i, o).
    итерация: (real, integer, integer, real) determ (i, i, i, o).
	repeat:() multi.

clauses
	repeat().
	repeat():- repeat().

	квадрат_итер(X, A, N, Q):-
		asserta(итер(0, X)),
		repeat,
		retract(итер(K, R)),
		K1 = K + 1,
		R1 = (R + A) * (R + A),
		asserta(итер(K1, R1)),
		K1 = N, !,
		retract(итер(N, Q)).

    итерация(X, A, N, Z):-
        квадрат_итер(X, A, N, Q),
		asserta(итер(0, Q + A)),
		repeat,
		retract(итер(K, R)),
		K1 = K + 1,
		R1 = R + A * A,
		asserta(итер(K1, R1)),
		K1 = N, !,
		retract(итер(N, Z)).


/* НИСХОДЯЩАЯ РЕКУРСИЯ */

class predicates
    квадрат_нисх:(real, integer, integer, real) nondeterm (i,i,i,o).
    нисходящая:(real, integer, integer, integer, real) nondeterm (i,i,i,i,o).
    нисходящая:(real, integer, integer, real) nondeterm (i,i,i,o).

clauses
	квадрат_нисх(X, _, 0, X):- !.
	квадрат_нисх(X, A, N, Q):-
		N1 = N - 1,
		квадрат_нисх(X, A, N1, Q1),
		Q = (Q1 + A) * (Q1 + A).

    нисходящая(X, A, N, 0, Z):-
        квадрат_нисх(X, A, N, Q),
        Z = Q + A, !.
	нисходящая(X, A, N, K, Z):-
		K1 = K - 1,
		нисходящая(X, A, N, K1, Z1),
		Z = Z1 + A * A.

    нисходящая(X, A, N, Z):-
        нисходящая(X, A, N, N, Z).


/* ВОСХОДЯЩАЯ РЕКУРСИЯ */

class predicates
	квадрат_восх:(integer, integer, real, integer, real) nondeterm (i,i,o,i,i).
    квадрат_восх:(real, integer, integer, real) nondeterm (i,i,i,o).
    восходящая:(integer, integer, real, integer, real) nondeterm (i,i,o,i,i).
    восходящая:(real, integer, integer, real) nondeterm (i,i,i,o).

clauses
	квадрат_восх(_, N, Q, N, Q):- !.
	квадрат_восх(A, N, Q, K, R):-
        K1 = K + 1,
        R1 = (R + A) * (R + A),
        квадрат_восх(A, N, Q, K1, R1).

    квадрат_восх(X, A, N, Q):-
        квадрат_восх(A, N, Q, 0, X).

    восходящая(_, N, Z, N, Z):- !.
    восходящая(A, N, Z, K, R):-
        K1 = K + 1,
        R1 = R + A * A,
        восходящая(A, N, Z, K1, R1).

    восходящая(X, A, N, Z):-
        квадрат_восх(X, A, N, Q),
        Z1 = Q + A,
        восходящая(A, N, Z, 0, Z1).


/* НИСХОДЯЩАЯ РЕКУРСИЯ */

class predicates
    funcTwo:(integer, integer) nondeterm (i, o).
    funcA:(integer, integer) nondeterm (i,o).
    funcP:(integer, real) nondeterm (i,o).

clauses
    funcTwo(2, 2):-!.
    funcTwo(I, Two):-
        I1 = I - 1,
        funcTwo(I1, Two1),
        Two = Two1 * 2.

    funcA(0, 1):-!.
    funcA(1, 1):-!.
    funcA(I, A):-
        funcA(I - 1, A1),
        funcA(I - 2, A2),
        funcTwo(I, Two),
        A = A2 + A1 * Two.

    funcP(1, P):-
        funcA(1, A),
        P = A, !.
    funcP(N, P):-
        N1 = N - 1,
        funcA(N1, A1),
        funcP(N1, P1),
        P = A1 * P1.


/* ВОСХОДЯЩАЯ РЕКУРСИЯ */

class predicates
    funcTwo_:(integer, integer, integer, integer) nondeterm (i, o, i, i).
    funcTwo_:(integer, integer) nondeterm (i, o).
    funcA_:(integer, integer, integer, integer, integer) nondeterm (i,o, i, i, i).
    funcA_:(integer, integer) nondeterm (i,o).
    funcP_:(integer, real, integer, real) nondeterm (i,o, i, i).
    funcP_:(integer, real) nondeterm (i,o).

clauses
    funcTwo_(I, Two, I, Two):-!.
    funcTwo_(I, Two, K, R):-
        Two1 = R * 2,
        I1 = K + 1,
        funcTwo_(I, Two, I1, Two1).
    funcTwo_(I, Two):-
        funcTwo_(I, Two, 2, 2).

    funcA_(I, A, I, _, A):-!.
    funcA_(I, A, K, A2, A1):-
        K1 = K + 1,
        funcTwo_(K1, Two),
        A_ = A2 + A1 * Two,
        funcA_(I, A, K1, A1, A_).
    funcA_(0, 1):-!.
    funcA_(1, 1):-!.
    funcA_(I, A):-
        funcA_(I, A, 1, 1, 1).

    funcP_(N, P, N, P):-!.
     funcP_(N, P, K, R):-
        K < N,
        funcA_(K, A),
        P1 = R * A,
        K1 = K + 1,
        funcP_(N, P, K1, P1).
    funcP_(N, P):-
        funcP_(N, P, 1, 1).


clauses
    run():-	console::init(),
	/*	write("X = "), X = read(),
        write("A = "), A = read(),
        write("N = "), N = read(), nl,

        итерация(X, A, N, Z1),
		write("Метод итераций: Z = ", Z1), nl,

        нисходящая(X, A, N, Z2),
		write("Нисходящая рекурсия: Z = ", Z2), nl,

        восходящая(X, A, N, Z3),
		write("Восходящая рекурсия: Z = ", Z3), nl,*/

        write("I = "), I = read(), nl,
        funcP(I, P1),
		write("P1 = ", P1), nl,
        funcP_(I, P2),
		write("P2 = ", P2), nl,
        !,

        _ = readLine(), _ = readLine().

	run().

end implement main
goal
 mainExe::run(main::run).