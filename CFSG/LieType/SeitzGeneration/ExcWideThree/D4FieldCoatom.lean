module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4IndexThree
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4FieldOrderNine

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
  CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Coatom

theorem d4_fieldType_isCoatom_index
    {K : Type} [Field K] [Finite K] [CharP K 3] {f : ℕ}
    (hK : Nat.card K = 3 ^ f) {e : MulAut ↥(adjointGroup Tag.D4 K)} (he1 : e ≠ 1)
    (he3 : e ^ 3 = 1) {σ : K ≃+* K} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hNF : HasNF e 0 σ) :
    IsCoatom (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup e) ∧
      3 ∣ (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup e).index := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : 1 ≤ f := by
    by_contra h
    push Not at h
    have hf0 : f = 0 := by omega
    subst hf0
    rw [pow_zero] at hK
    have := Finite.one_lt_card (α := K)
    omega
  obtain ⟨d, T, hd0, hdf, hT, hT3, hσT⟩ :=
    exists_frobenius_of_cube Nat.prime_three hf K hK σ hσ3 hσ1
  have hT1 : T ≠ 1 := by
    rintro rfl
    rcases hσT with h | h
    · exact hσ1 h
    · exact hσ1 (by rw [h, one_pow])
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK, ← hdf]
    calc 4 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (d * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ 3 ^ (d * 3) := Nat.pow_le_pow_left (by norm_num) (d * 3)
  have hordT : orderOf T = 3 := orderOf_eq_prime hT3 hT1
  have hq0 : Nat.card (fixSubfield T) = 3 ^ d := card_fixSubfield_eq_pow hK hdf T hT3 hT1
  have h2 : Nat.card (fixSubfield T) ≠ 2 := by
    rw [hq0]
    have h3d : 3 ≤ 3 ^ d := by
      simpa using Nat.pow_le_pow_right (show 0 < 3 by norm_num) (show 1 ≤ d by omega)
    omega
  have hmax : ∀ M : Subgroup ↥(adjointGroup Tag.D4 K),
      subfieldGroup Tag.D4 T ≤ M → M = subfieldGroup Tag.D4 T ∨ M = ⊤ :=
    fun M hM => subfieldMaximal_D4_of_card_ne_two T Nat.prime_three (by norm_num) hordT h2 M hM
  obtain ⟨g, a, hα⟩ := hNF
  rw [d4Graph_zero, mul_one] at hα
  obtain ⟨ψ, -, hψ⟩ := exists_conj_fixedSubgroup_D4_field hK hK4 hd0 hdf T σ hT hT3 hσT
    (AlgebraicClosure K) g a e hα he3
  have hmaxψ : ∀ M : Subgroup ↥(adjointGroup Tag.D4 K),
      CFSG.RankThree.PartOne.CTP.fixedSubgroup e ≤ M →
      M = CFSG.RankThree.PartOne.CTP.fixedSubgroup e ∨ M = ⊤ :=
    maximal_fixedSubgroup_of_conj hmax hψ
  have hmaxF : ∀ M : Subgroup ↥(adjointGroup Tag.D4 K),
      CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup e ≤ M →
      M = CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup e ∨ M = ⊤ := by
    intro M hM
    rw [fixedCommutingProduct_fixedSubgroup_eq e] at hM ⊢
    exact hmaxψ M hM
  have hFne : CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup e ≠ ⊤ := by
    intro htop
    apply he1
    refine MulEquiv.ext fun x => ?_
    have hx : x ∈ CFSG.RankThree.PartOne.CTP.fixedSubgroup e := by
      rw [← fixedCommutingProduct_fixedSubgroup_eq e, htop]
      exact Subgroup.mem_top x
    show e x = x
    exact (CFSG.RankThree.PartOne.CTP.mem_fixedSubgroup).1 hx
  have hidx : (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup e).index =
      (subfieldGroup Tag.D4 T).index := by
    calc (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup e).index
        = (CFSG.RankThree.PartOne.CTP.fixedSubgroup e).index := by
          rw [fixedCommutingProduct_fixedSubgroup_eq e]
      _ = ((CFSG.RankThree.PartOne.CTP.fixedSubgroup e).map ψ.toMonoidHom).index :=
          (Subgroup.index_map_equiv _ ψ).symm
      _ = (CFSG.RankThree.PartOne.CTP.fixedSubgroup (ψ * e * ψ⁻¹)).index := by
          rw [← CFSG.RankThree.PartOne.CTP.fixedSubgroup_conj ψ e]
      _ = (subfieldGroup Tag.D4 T).index := by rw [hψ]
  have hK' : Nat.card K = 3 ^ (d * 3) := by rw [hK, ← hdf]
  refine ⟨?_, ?_⟩
  · rw [isCoatom_iff_ge_of_le]
    refine ⟨hFne, ?_⟩
    intro M hMtop hFM
    rcases hmaxF M hFM with h | h
    · exact le_of_eq h
    · exact absurd h hMtop
  · rw [hidx]
    exact three_dvd_index_subfieldGroup_D4 hK' hd0 T hT3 hq0

theorem d4_fieldAutMaximal_model
    {K : Type} [Field K] [Finite K] [CharP K 3] {f : ℕ}
    (hK : Nat.card K = 3 ^ f) {E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 9)
    (hEI : E ⊓ inner ↥(adjointGroup Tag.D4 K) = ⊥) :
    ∃ e ∈ E, e ≠ 1 ∧
      IsCoatom (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup e) ∧
        3 ∣ (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup e).index := by
  obtain ⟨e, heE, he1, σ, hσ3, hσ1, hNF⟩ := exists_hasNF_zero_of_nine hE hcard hEI
  obtain ⟨hco, hidx⟩ := d4_fieldType_isCoatom_index hK he1 (hE.2 e heE) hσ3 hσ1 hNF
  exact ⟨e, heE, he1, hco, hidx⟩

end Coatom

end CFSG.LieType.SeitzGeneration.ExcWideThree
