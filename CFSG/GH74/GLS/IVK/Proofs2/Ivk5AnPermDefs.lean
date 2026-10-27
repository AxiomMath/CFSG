module

public import CFSG.GH74.GLS.Bg.TwoGroups.L23Models
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk5An

open Equiv Equiv.Perm
open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

@[expose] def sw (m i j : ℕ) : Perm (Fin (m + 1)) := swap (Fin.ofNat (m + 1) i) (Fin.ofNat (m + 1) j)

@[expose] def tb (m : ℕ) : Perm (Fin (m + 1)) := sw m 0 1 * sw m 2 3 * sw m 4 5 * sw m 6 7

@[expose] def ub (m : ℕ) : Perm (Fin (m + 1)) := sw m 0 5 * sw m 1 4 * sw m 2 6 * sw m 3 7

@[expose] def vb (m : ℕ) : Perm (Fin (m + 1)) := sw m 0 3 * sw m 1 2 * sw m 4 6 * sw m 5 7

@[expose] def xb1 (m : ℕ) : Perm (Fin (m + 1)) := sw m 0 2 * sw m 1 3 * sw m 4 6 * sw m 5 7

@[expose] def xb2 (m : ℕ) : Perm (Fin (m + 1)) := sw m 0 4 * sw m 1 5 * sw m 2 6 * sw m 3 7

@[expose] def c3 (m : ℕ) : Perm (Fin (m + 1)) := sw m 0 2 * sw m 2 4 * sw m 1 3 * sw m 3 5

@[expose] def sg (m : ℕ) : Perm (Fin (m + 1)) := sw m 2 4 * sw m 3 5

@[expose] def vp (m : ℕ) : Perm (Fin (m + 1)) := sw m 0 2 * sw m 1 3 * sw m 6 7 * sw m 8 9

@[expose] def o3 (m : ℕ) : Perm (Fin (m + 1)) := sw m 8 9 * sw m 9 10

@[expose] def zpow2 {G : Type*} [Group G] (g : G) (a : ZMod 2) : G := if a = 0 then 1 else g

@[expose] def rbar (m : ℕ) (x : F4c) : Perm (Fin (m + 1)) := zpow2 (ub m) x.a * zpow2 (vb m) x.b

@[expose] def sbar (m : ℕ) (x : F4c) : Perm (Fin (m + 1)) := zpow2 (xb1 m) x.a * zpow2 (xb2 m) x.b

@[expose] def wbar (m : ℕ) (x : F4c) : Perm (Fin (m + 1)) := zpow2 (tb m) x.a

@[expose] def Sfun (m : ℕ) (x : UT3 F4c) : Perm (Fin (m + 1)) := sbar m x.b * rbar m x.a * wbar m x.c

end CFSG.GH74.GLS.IVK.Proofs2.Ivk5An
