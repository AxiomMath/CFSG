module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowFrame

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Blueprint CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin (coe_quadOdd coe_quadPlus coe_quadMinus)

private theorem a2l_fin_three_ne {m : ℕ} (hm : 3 ≤ m) :
    (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ ∧ (⟨0, by omega⟩ : Fin m) ≠ ⟨2, by omega⟩ ∧
      (⟨1, by omega⟩ : Fin m) ≠ ⟨2, by omega⟩ :=
  ⟨by simp [Fin.ext_iff], by simp [Fin.ext_iff], by simp [Fin.ext_iff]⟩

private theorem a2l_card_three_pow {K : Type} {f : ℕ} (hcard : Nat.card K = 3 ^ f) (hf : 2 ≤ f) :
    Odd (Nat.card K) ∧ 9 ≤ Nat.card K := by
  rw [hcard]
  exact ⟨Odd.pow (by decide), calc 9 = 3 ^ 2 := by norm_num
    _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf⟩

theorem a2l_rowPOmegaOdd_two {X : Type} [Group X] [Finite X] {n f : ℕ} (hn : 3 ≤ n)
    (hf : 2 ≤ f) (hm : LieModel X .POmegaOdd n 3 f) : a2lDatum X := by
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  obtain ⟨hodd, h9⟩ := a2l_card_three_pow hcard hf
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  obtain ⟨h01, h02, h12⟩ := a2l_fin_three_ne hn
  have hd := a2lDatum_projElementary_of_pairs (Q := CFSG.LieType.Universal.Spin.quadOdd n K)
    hodd h9 (oddPair_orth h01) (oddPair_orth h02).symm (oddPair_orth h12).symm
  exact a2lDatum_of_mulEquiv (e.trans (statedProjEquiv (coe_quadOdd n K)
    (commutator_orthogonalGroup_quadOdd h2 hn))).symm hd

theorem a2l_rowPOmegaPlus_two {X : Type} [Group X] [Finite X] {n f : ℕ} (hn : 4 ≤ n)
    (hf : 2 ≤ f) (hm : LieModel X .POmegaPlus n 3 f) : a2lDatum X := by
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  obtain ⟨hodd, h9⟩ := a2l_card_three_pow hcard hf
  obtain ⟨h01, h02, h12⟩ := a2l_fin_three_ne (m := n) (by omega)
  have hd := a2lDatum_projElementary_of_pairs (Q := CFSG.LieType.Universal.Spin.quadPlus n K)
    hodd h9 (plusPair_orth h01) (plusPair_orth h02).symm (plusPair_orth h12).symm
  exact a2lDatum_of_mulEquiv (e.trans (statedProjEquiv (coe_quadPlus n K)
    (commutator_orthogonalGroup_quadPlus (by omega)))).symm hd

theorem a2l_rowPOmegaMinus_two {X : Type} [Group X] [Finite X] {n f : ℕ} (hn : 4 ≤ n)
    (hf : 2 ≤ f) (hm : LieModel X .POmegaMinus n 3 f) : a2lDatum X := by
  obtain ⟨-, K, _, _, hcard, b, c, hirr, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  obtain ⟨hodd, h9⟩ := a2l_card_three_pow hcard hf
  obtain ⟨h01, h02, h12⟩ := a2l_fin_three_ne (m := n - 1) (by omega)
  have hd := a2lDatum_projElementary_of_pairs
    (Q := CFSG.LieType.Universal.Spin.quadMinus n K b c) hodd h9
    (minusPair_orth h01) (minusPair_orth h02).symm (minusPair_orth h12).symm
  exact a2lDatum_of_mulEquiv (e.trans (statedProjEquiv (coe_quadMinus n K b c)
    (commutator_orthogonalGroup_quadMinus hn hirr))).symm hd

end CFSG.OddStandard.SmallF3.HypA2Leaves
