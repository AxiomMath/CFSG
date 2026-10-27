module

public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M23
public import CFSG.Sporadic.J1
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.J3
public import CFSG.Sporadic.Ly
public import CFSG.Sporadic.McL.Simple

public section

namespace CFSG.GH74

open CFSG.Blueprint

theorem card_eq_of_isSporadic {G : Type} [Group G] {s : TauCeti.SporadicName} {n : ℕ}
    (hn : Nat.card (NativeSporadic.Carrier s) = n) (h : NativeSporadic.IsSporadic G s) :
    Nat.card G = n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, hn]

theorem card_nativeM23
    : Nat.card NativeSporadic.M23 = 10200960 := by
  rw [CFSG.Sporadic.Mathieu.nativeM23_eq]
  exact (Nat.card_eq_fintype_card (α := CFSG.M23.M23Group.H0)).trans CFSG.M23.M23Group.card_M23

theorem card_of_isSporadic_M12
    {G : Type} [Group G] (h : NativeSporadic.IsSporadic G .M12) :
    Nat.card G = 2 ^ 6 * 3 ^ 3 * 5 * 11 :=
  card_eq_of_isSporadic (s := .M12) (CFSG.Sporadic.Mathieu.card_M12.trans (by norm_num)) h

theorem card_of_isSporadic_M22
    {G : Type} [Group G] (h : NativeSporadic.IsSporadic G .M22) :
    Nat.card G = 2 ^ 7 * 3 ^ 2 * 5 * 7 * 11 :=
  card_eq_of_isSporadic (s := .M22) (CFSG.Sporadic.Mathieu.card_M22.trans (by norm_num)) h

theorem card_of_isSporadic_M23
    {G : Type} [Group G] (h : NativeSporadic.IsSporadic G .M23) :
    Nat.card G = 2 ^ 7 * 3 ^ 2 * 5 * 7 * 11 * 23 :=
  card_eq_of_isSporadic (s := .M23) (card_nativeM23.trans (by norm_num)) h

theorem card_of_isSporadic_J1
    {G : Type} [Group G] (h : NativeSporadic.IsSporadic G .J1) :
    Nat.card G = 2 ^ 3 * 3 * 5 * 7 * 11 * 19 :=
  card_eq_of_isSporadic (s := .J1) (CFSG.Sporadic.J1.card_J1.trans (by norm_num)) h

theorem card_of_isSporadic_J2
    {G : Type} [Group G] (h : NativeSporadic.IsSporadic G .J2) :
    Nat.card G = 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7 :=
  card_eq_of_isSporadic (s := .J2) (CFSG.Sporadic.J2.card_J2.trans (by norm_num)) h

theorem card_of_isSporadic_J3
    {G : Type} [Group G] (h : NativeSporadic.IsSporadic G .J3) :
    Nat.card G = 2 ^ 7 * 3 ^ 5 * 5 * 17 * 19 :=
  card_eq_of_isSporadic (s := .J3) (CFSG.Sporadic.J3.card_J3.trans (by norm_num)) h

theorem card_of_isSporadic_McL
    {G : Type} [Group G] (h : NativeSporadic.IsSporadic G .McL) :
    Nat.card G = 2 ^ 7 * 3 ^ 6 * 5 ^ 3 * 7 * 11 :=
  card_eq_of_isSporadic (s := .McL) (CFSG.Sporadic.McL.card_McL.trans (by norm_num)) h

theorem card_of_isSporadic_Ly
    {G : Type} [Group G] (h : NativeSporadic.IsSporadic G .Ly) :
    Nat.card G = 2 ^ 8 * 3 ^ 7 * 5 ^ 6 * 7 * 11 * 31 * 37 * 67 :=
  card_eq_of_isSporadic (s := .Ly) (CFSG.Sporadic.Ly.card_Ly.trans (by norm_num)) h

end CFSG.GH74
