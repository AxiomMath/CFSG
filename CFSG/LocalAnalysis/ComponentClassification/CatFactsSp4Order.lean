module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Kron
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.GH74.Generic.Context
import CFSG.Adapters.StatedSmallProjOrders

public section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup

variable {K : Type} [Field K]

private theorem two_ne_zero_of_odd [Finite K] (hodd : Odd (Nat.card K)) : (2 : K) ≠ 0 := by
  have : Fintype K := Fintype.ofFinite K
  apply Ring.two_ne_zero
  intro h
  have := (FiniteField.even_card_iff_char_two (F := K)).mp h
  rw [← Nat.card_eq_fintype_card] at this
  exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_iff.mpr this)

theorem neg_one_symplectic :
    (-1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * formJ 2 K * (-1) = formJ 2 K := by
  rw [transpose_neg, transpose_one, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg,
    Matrix.mul_one, neg_neg]

theorem card_spScalars (h2 : (2 : K) ≠ 0) : Nat.card (spScalars 2 K) = 2 := by
  have hneg : toSp (-1) neg_one_symplectic ∈ spScalars 2 K :=
    (mem_spScalars_iff _).mpr (Or.inr rfl)
  rw [Nat.card_eq_two_iff]
  refine ⟨1, ⟨_, hneg⟩, fun h => ?_, ?_⟩
  · have h1 := congrArg (fun x : spScalars 2 K =>
      (((x : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
        (Sum.inl 0) (Sum.inl 0)) h
    simp only [OneMemClass.coe_one, Units.val_one, one_apply_eq, coe_toSp, Matrix.neg_apply]
      at h1
    exact h2 (by linear_combination h1)
  · ext ⟨x, hx⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases (mem_spScalars_iff x).mp hx with h | h
    · left
      exact Subtype.ext (sp_ext h)
    · right
      exact Subtype.ext (sp_ext h)

theorem two_mul_card_P [Finite K] (h2 : (2 : K) ≠ 0) :
    Nat.card (StatedProj (StatedSp 2 K)) * 2 =
      Nat.card K ^ 4 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) := by
  have h := (spScalars 2 K).card_eq_card_quotient_mul_card_subgroup
  rw [card_spScalars h2, card_statedSp] at h
  rw [← h]
  simp [Finset.prod_Icc_succ_top]

theorem two_mul_card_of_lieModel_psp {K₀ : Type} [Group K₀] {p f : ℕ} (hp2 : p ≠ 2)
    (h : Blueprint.LieModel K₀ .PSp 2 p f) :
    Nat.card K₀ * 2 = (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) := by
  obtain ⟨hp, -, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data h
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hp.odd_of_ne_two hp2).pow
  rw [Nat.card_congr e.toEquiv, two_mul_card_P (two_ne_zero_of_odd hodd), hF]

theorem card_statedProj_statedSL_two_odd {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) :
    Nat.card (StatedProj (StatedSL 2 F)) = Nat.card F * (Nat.card F ^ 2 - 1) / 2 :=
  CFSG.Open.StatedAPI.card_statedProj_statedSL_two_of_odd hodd

theorem card_of_lieModel_psl_sq {Y₀ : Type} [Group Y₀] {p f : ℕ} (hp2 : p ≠ 2)
    (h : Blueprint.LieModel Y₀ .PSL 2 p (2 * f)) :
    Nat.card Y₀ = (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) / 2 := by
  obtain ⟨hp, -, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psl_data h
  have hF' : Nat.card F = (p ^ f) ^ 2 := by rw [hF, ← pow_mul, mul_comm]
  have hodd : Odd (Nat.card F) := by
    rw [hF']
    exact ((hp.odd_of_ne_two hp2).pow).pow
  rw [Nat.card_congr e.toEquiv, card_statedProj_statedSL_two_odd hodd, hF']

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem psl_sq_lt_psp {q : ℕ} (hq : 2 ≤ q) :
    q ^ 2 * ((q ^ 2) ^ 2 - 1) < q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h2 : 4 ≤ q ^ 2 := by nlinarith
  have e : (q ^ 2) ^ 2 = q ^ 4 := by ring
  rw [e]
  have h5 : 0 < q ^ 4 - 1 := by
    have : 16 ≤ q ^ 4 := by nlinarith
    omega
  have h6 : q ^ 2 < q ^ 4 * (q ^ 2 - 1) := by
    have : q ^ 4 = q ^ 2 * q ^ 2 := by ring
    rw [this]
    have h7 : 1 < q ^ 2 * (q ^ 2 - 1) := by
      have : 3 ≤ q ^ 2 - 1 := by omega
      nlinarith
    nlinarith
  calc q ^ 2 * (q ^ 4 - 1) < q ^ 4 * (q ^ 2 - 1) * (q ^ 4 - 1) :=
        Nat.mul_lt_mul_of_pos_right h6 h5
    _ = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by ring

end CFSG.ComponentClassification.CatFactsSp4
