module

public import CFSG.LocalAnalysis.SectionRank.QTK.List
public import CFSG.Open.StatedDefs
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.J1
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.J3
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.He
public import CFSG.Sporadic.McL.Simple
public import CFSG.Sporadic.Ru
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.Bridge.J4Surj
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import CFSG.Sporadic.M23.M23Group

public section

namespace CFSG.SectionRank.QTK

open CFSG.Open

theorem not_two_pow_fifteen_dvd_alt {S : Type} [Group S] [Finite S] {n : ℕ} (h5 : 5 ≤ n)
    (h9 : n ≤ 9) (e : S ≃* alternatingGroup (Fin n)) : ¬ 2 ^ 15 ∣ Nat.card S := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hc : Nat.card S = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  rw [hc]
  interval_cases n <;> norm_num [Nat.factorial]

theorem units_eq_one_of_card_two (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2)
    (u : Kˣ) : u = 1 := by
  have h1 : Nat.card Kˣ = 1 := by
    rw [Nat.card_units, hK]
  have hs : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp h1).1
  exact Subsingleton.elim u 1

theorem card_statedProj_sl_two (n : ℕ) [NeZero n] (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    Nat.card (StatedProj (StatedSL n K)) = ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  classical
  have hdet : ∀ A : GL (Fin n) K, (A : Matrix (Fin n) (Fin n) K).det = 1 := by
    intro A
    have h := Matrix.GeneralLinearGroup.val_det_apply A
    rw [← h, units_eq_one_of_card_two K hK (Matrix.GeneralLinearGroup.det A), Units.val_one]
  have hSL : StatedSL n K = ⊤ := by
    rw [eq_top_iff]
    intro A _
    exact Subgroup.subset_closure (show A ∈ {A : GL (Fin n) K |
      (A : Matrix (Fin n) (Fin n) K).det = 1} from hdet A)
  have hScal : StatedScalars (Fin n) K = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨c, rfl⟩
    rw [Subgroup.mem_bot, units_eq_one_of_card_two K hK c, map_one]
  have hfin : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  unfold StatedProj
  rw [hScal, Subgroup.bot_subgroupOf, Nat.card_congr (QuotientGroup.quotientBot (G := StatedSL n K)).toEquiv]
  rw [hSL, Nat.card_congr Subgroup.topEquiv.toEquiv, Matrix.card_GL_field, hq]

theorem card_psl_four_two {S : Type} [Group S] (h : StatedClassicalModel S .PSL 4 2 1) :
    Nat.card S = 20160 := by
  obtain ⟨-, K, hF, hfin, hcard, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, card_statedProj_sl_two 4 K (by simpa using hcard)]
  simp [Fin.prod_univ_four]

theorem card_psl_five_two {S : Type} [Group S] (h : StatedClassicalModel S .PSL 5 2 1) :
    Nat.card S = 9999360 := by
  obtain ⟨-, K, hF, hfin, hcard, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, card_statedProj_sl_two 5 K (by simpa using hcard)]
  simp [Fin.prod_univ_five]

theorem not_two_pow_fifteen_dvd_psl_four_five_two {S : Type} [Group S] {n : ℕ}
    (hn : n = 4 ∨ n = 5) (h : StatedClassicalModel S .PSL n 2 1) : ¬ 2 ^ 15 ∣ Nat.card S := by
  rcases hn with rfl | rfl
  · rw [card_psl_four_two h]; norm_num
  · rw [card_psl_five_two h]; norm_num

theorem not_two_pow_fifteen_dvd_sporadic
    (s : TauCeti.SporadicName)
    (hs : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨
      s = .J3 ∨ s = .HS ∨ s = .He ∨ s = .Ru ∨ s = .McL) :
    ¬ 2 ^ 15 ∣ Nat.card (CFSG.Blueprint.NativeSporadic.Carrier s) := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show ¬ 2 ^ 15 ∣ Nat.card CFSG.Blueprint.NativeSporadic.M11
    rw [CFSG.Sporadic.Mathieu.card_M11]; norm_num
  · show ¬ 2 ^ 15 ∣ Nat.card CFSG.Blueprint.NativeSporadic.M12
    rw [CFSG.Sporadic.Mathieu.card_M12]; norm_num
  · show ¬ 2 ^ 15 ∣ Nat.card CFSG.Blueprint.NativeSporadic.M22
    rw [CFSG.Sporadic.Mathieu.card_M22]; norm_num
  · show ¬ 2 ^ 15 ∣ Nat.card CFSG.Blueprint.NativeSporadic.M23
    rw [CFSG.Sporadic.Schreier.m23_card]; norm_num
  · show ¬ 2 ^ 15 ∣ Nat.card CFSG.Blueprint.NativeSporadic.M24
    rw [CFSG.Sporadic.Mathieu.card_M24]; norm_num
  · show ¬ 2 ^ 15 ∣ Nat.card CFSG.Blueprint.NativeSporadic.J1
    rw [CFSG.Sporadic.J1.card_J1]; norm_num
  · show ¬ 2 ^ 15 ∣ Nat.card CFSG.Blueprint.NativeSporadic.J2
    rw [CFSG.Sporadic.J2.card_J2]; norm_num
  · show ¬ 2 ^ 15 ∣ Nat.card CFSG.Blueprint.NativeSporadic.J3
    rw [CFSG.Sporadic.J3.card_J3]; norm_num
  · show ¬ 2 ^ 15 ∣ Nat.card CFSG.Blueprint.NativeSporadic.HS
    rw [CFSG.Sporadic.HS.card_HS]; norm_num
  · show ¬ 2 ^ 15 ∣ Nat.card CFSG.Blueprint.NativeSporadic.He
    rw [(CFSG.Sporadic.He.fam_he_order).1]; norm_num
  · show ¬ 2 ^ 15 ∣ Nat.card CFSG.Blueprint.NativeSporadic.Ru
    rw [CFSG.Sporadic.Ru.card_Ru]; norm_num
  · show ¬ 2 ^ 15 ∣ Nat.card CFSG.Blueprint.NativeSporadic.McL
    rw [CFSG.Sporadic.McL.card_McL]; norm_num

end CFSG.SectionRank.QTK
