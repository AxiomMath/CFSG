module

public import CFSG.LieType.SeitzGeneration.ExcTorusThreeRank
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6One
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Two
public import CFSG.LieType.SeitzGeneration.ExcTorusThreeTw

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial
open scoped Matrix

section Rational


theorem exists_elemAbelian_twistedE6_three_one {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (he : orderOf (((ℓ ^ f : ℕ)) : ZMod 3) = 1) :
    ∃ E : Subgroup (twistedE6RootGroup K σ), IsElemAbelian 3 E ∧ 3 ^ 4 ≤ 3 * Nat.card E := by
  have hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6OneWord) • x =
      toMat TwistTag.E6.tag.rank twE6OneMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
    rw [wordProd_smul_eq_wordMat_mulVec, twE6One_wordMat, toMat_lmul, permLattice_E6_eq,
      Matrix.mulVec_mulVec]
  have h := exists_elemAbelian_ge_twistedE6_three_of_blocks hℓ hf K hK σ hσ _ hv
    [1, 1, 1, 1, 2, 2] twE6One_charpoly (by norm_num) twE6One_pow (by norm_num) he
    (by norm_num) (by decide)
  simpa using h

theorem exists_elemAbelian_twistedE6_three_two {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (he : orderOf (((ℓ ^ f : ℕ)) : ZMod 3) = 2) :
    ∃ E : Subgroup (twistedE6RootGroup K σ), IsElemAbelian 3 E ∧ 3 ^ 6 ≤ 3 * Nat.card E := by
  have hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6TwoWord) • x =
      toMat TwistTag.E6.tag.rank twE6TwoMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
    rw [wordProd_smul_eq_wordMat_mulVec, twE6Two_wordMat, toMat_lmul, permLattice_E6_eq,
      Matrix.mulVec_mulVec]
  have h := exists_elemAbelian_ge_twistedE6_three_of_blocks hℓ hf K hK σ hσ _ hv
    [2, 2, 2, 2, 2, 2] twE6Two_charpoly (by norm_num) twE6Two_pow (by norm_num) he
    (by norm_num) (by decide)
  simpa using h

theorem not_rankLE2_twistedE6_three {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hpq : ¬ 3 ∣ ℓ ^ f) : ¬ RankLE2 3 (twistedE6RootGroup K σ) := by
  rcases orderOf_natCast_three hpq with he | he
  · obtain ⟨E, hE, hle⟩ := exists_elemAbelian_twistedE6_three_one hℓ hf K hK σ hσ he
    exact not_rankLE2_three_of_ge (m := 4) (d := 3) le_rfl le_rfl hE hle
  · obtain ⟨E, hE, hle⟩ := exists_elemAbelian_twistedE6_three_two hℓ hf K hK σ hσ he
    exact not_rankLE2_three_of_ge (m := 6) (d := 3) (by norm_num) le_rfl hE hle

end Rational

end CFSG.LieType.SeitzGeneration
