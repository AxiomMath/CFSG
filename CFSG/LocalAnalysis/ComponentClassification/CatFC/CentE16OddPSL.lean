module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentE16Core
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.GH74.GLS.IVK.L2.Lemma13
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.GH74.GLS.IVK

theorem e16_false_psl_two (hO : LieOrderFormulasInput) {K : Type} [Group K] [Finite K]
    (D : CatE16Data K) {f : ℕ} (hadm : StatedLieAdmissible .PSL 2 5 f)
    (hmod : LieModel K .PSL 2 5 f) : False := by
  have hf : 1 ≤ f := hadm.2.1
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · have hf1' : f = 1 := by omega
    subst hf1'
    obtain ⟨-, hord, -⟩ := hO K .PSL 2 5 1 hadm hmod
    have h1 : lieOrderDivisor .PSL 2 (5 ^ 1) = 2 := by decide
    have h2 : lieOrderNumerator .PSL 2 (5 ^ 1) = 120 := by decide
    rw [h1, h2] at hord
    exact D.card_ne_sixty (by omega)
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := LieModel.statedClassicalModel hmod (by decide)
    have h25 : 25 ≤ Nat.card F := by
      rw [hF]
      calc 25 = 5 ^ 2 := by norm_num
        _ ≤ 5 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    have hodd : Odd (Nat.card F) := by
      rw [hF]
      exact Odd.pow (by decide)
    have hmod4 : (Nat.card F : ℤ) ≡ 1 [ZMOD 4] := by
      rw [hF]
      push_cast
      have : (5 : ℤ) ^ f ≡ 1 ^ f [ZMOD 4] := Int.ModEq.pow f (by decide)
      simpa using this
    have hd : ((Nat.card F - 1 : ℕ) : ℤ) = Nat.card F - 1 := by
      have : 1 ≤ Nat.card F := by omega
      push_cast [this]
      ring
    obtain ⟨-, hdih, -⟩ := ivk_1_3a F ⟨hodd, by omega⟩ K e 1 (Or.inl rfl) hmod4
      (Nat.card F - 1) hd D.κ D.hκ2
    obtain ⟨k, hk, hk2, ⟨φ⟩⟩ := hdih
    have hcard : Nat.card (Subgroup.centralizer ({D.κ} : Set K)) = 2 * k := by
      rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]
    have := D.hQ
    omega

end CFSG.ComponentClassification.CatFC
