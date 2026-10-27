module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTExcl
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Signalizer.Odd87

variable {k : Kind} {Y : Type} [Group Y]

theorem card_of_alt {n : ℕ} (hn : 2 ≤ n) (e : Y ≃* alternatingGroup (Fin n)) :
    Nat.card Y = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem not_kindFactorAll_alt (hk : IsClassicalKind k) {n : ℕ} (hn8 : 8 ≤ n) (hn11 : n ≤ 11)
    (hY : Nonempty (Y ≃* alternatingGroup (Fin n))) : ¬ KindFactorAll k Y := by
  obtain ⟨e⟩ := hY
  have hc := card_of_alt (by omega) e
  interval_cases n
  · exact not_kindFactorAll_of_card_btw hk hc 34 (by decide) (by decide) (by decide)
  · exact not_kindFactorAll_of_card_btw hk hc 71 (by decide) (by decide) (by decide)
  · exact not_kindFactorAll_of_card_btw hk hc 153 (by decide) (by decide) (by decide)
  · exact not_kindFactorAll_of_card_btw hk hc 341 (by decide) (by decide) (by decide)

theorem not_kindFactorAll_m12 (hk : IsClassicalKind k)
    (hY : NativeSporadic.IsSporadic Y .M12) : ¬ KindFactorAll k Y := by
  obtain ⟨e⟩ := hY
  have hc : Nat.card Y = 95040 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M12
  exact not_kindFactorAll_of_card_btw hk hc 57 (by decide) (by decide) (by decide)

theorem not_kindFactorAll_m22 (hk : IsClassicalKind k)
    (hY : NativeSporadic.IsSporadic Y .M22) : ¬ KindFactorAll k Y := by
  obtain ⟨e⟩ := hY
  have hc : Nat.card Y = 443520 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M22
  exact not_kindFactorAll_of_card_btw hk hc 96 (by decide) (by decide) (by decide)

theorem not_kindFactorAll_m23 (hk : IsClassicalKind k)
    (hY : NativeSporadic.IsSporadic Y .M23) : ¬ KindFactorAll k Y := by
  obtain ⟨e⟩ := hY
  have hc : Nat.card Y = 10200960 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Schreier.m23_card
  exact not_kindFactorAll_of_card_btw hk hc 273 (by decide) (by decide) (by decide)

theorem not_kindFactorAll_j2 (hk : IsClassicalKind k)
    (hY : NativeSporadic.IsSporadic Y .J2) : ¬ KindFactorAll k Y := by
  obtain ⟨e⟩ := hY
  have hc : Nat.card Y = 604800 := (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J2.card_J2
  exact not_kindFactorAll_of_card_btw hk hc 106 (by decide) (by decide) (by decide)

theorem not_kindFactorAll_j3 (hk : IsClassicalKind k)
    (hY : NativeSporadic.IsSporadic Y .J3) : ¬ KindFactorAll k Y := by
  obtain ⟨e⟩ := hY
  have hc : Nat.card Y = 50232960 := (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J3.card_J3
  exact not_kindFactorAll_of_card_btw hk hc 464 (by decide) (by decide) (by decide)

theorem statedClassicalModel_of_lieModel {t : Assembly.LowTwoRank.StatedLieTag}
    (ht : t = .PSL ∨ t = .PSU)
    {n p f : ℕ} (h : LieModel Y t n p f) : Assembly.LowTwoRank.StatedClassicalModel Y t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by rcases ht with rfl | rfl <;> decide)

theorem not_kindFactorAll_l216 (hk : IsClassicalKind k) (hY : LieModel Y .PSL 2 2 4) :
    ¬ KindFactorAll k Y := by
  have hc : Nat.card Y = 4080 := by
    rw [(Timmesfeld.card_statedClassicalModel_two
      (statedClassicalModel_of_lieModel (Or.inl rfl) hY)).1 rfl]
    decide
  exact not_kindFactorAll_of_card_btw hk hc 20 (by decide) (by decide) (by decide)

theorem not_kindFactorAll_l34 (hk : IsClassicalKind k) (hY : LieModel Y .PSL 3 2 2) :
    ¬ KindFactorAll k Y := by
  have hc : Nat.card Y = 20160 := by
    rw [(Timmesfeld.card_statedClassicalModel_two
      (statedClassicalModel_of_lieModel (Or.inl rfl) hY)).1 rfl]
    decide
  exact not_kindFactorAll_of_card_btw hk hc 34 (by decide) (by decide) (by decide)

theorem not_kindFactorAll_u34 (hk : IsClassicalKind k) (hY : LieModel Y .PSU 3 2 2) :
    ¬ KindFactorAll k Y := by
  have hc : Nat.card Y = 62400 := by
    rw [(Timmesfeld.card_statedClassicalModel_two
      (statedClassicalModel_of_lieModel (Or.inr rfl) hY)).2.1 rfl]
    decide
  exact not_kindFactorAll_of_card_btw hk hc 49 (by decide) (by decide) (by decide)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
