module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YHDescent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YGRest
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4YH

open CFSG.Open CFSG.StandardType CFSG.StandardType.Triality

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

section PureField

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_pure_field {A : Subgroup (MulAut (Om8 K))} (hA : IsElemAbelian 3 A)
    {α : MulAut (Om8 K)} (hαA : α ∈ A)
    (hα : α ∉ Inn (Om8 K) ⊔ (AutOm.fieldAutP (K := K) 4).range)
    (hidx : 3 * Nat.card ↥(A ⊓ Inn (Om8 K)) < Nat.card A) :
    ∃ c ∈ A, c ∈ Inn (Om8 K) ⊔ (AutOm.fieldAutP (K := K) 4).range ∧ c ∉ Inn (Om8 K) := by
  by_contra hno
  push Not at hno
  have hα3 : α ^ 3 = 1 := hA.2 α hαA
  have h1 : Nat.card A ≤ 3 * Nat.card ↥(A ⊓ (Inn (Om8 K) ⊔ (AutOm.fieldAutP (K := K) 4).range)) :=
    NbrGraphD4.card_le_three_mul hαA fun a ha => NbrGraphD4.exists_mul_pow_mem_sup (hA.2 a ha) hα3 hα
  have h2 : Nat.card ↥(A ⊓ (Inn (Om8 K) ⊔ (AutOm.fieldAutP (K := K) 4).range)) ≤
      Nat.card ↥(A ⊓ Inn (Om8 K)) :=
    Subgroup.card_le_of_le fun a ha => ⟨ha.1, hno a ha.1 ha.2⟩
  omega

end PureField

section FixedSub

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)
open CFSG.RankThree.PartOne.AUTSL (conjAct conjAct_inclusion_of_mem derivedProjEquiv)
open CFSG.RankThree.Classical.SteinbergBY
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (linearConjugationHom)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_pair_of_mem_sup {c : MulAut (Om8 K)}
    (hc : c ∈ Inn (Om8 K) ⊔ (AutOm.fieldAutP (K := K) 4).range) :
    ∃ (g : similarityPairs (coordinateQuadPlus 4 K)) (σ : K ≃+* K) (ι : MulAut (Om8 K)),
      ι ∈ Inn (Om8 K) ∧ c = ι * AutOm.fieldAutP 4 σ ∧ conjAct _ g = c ∧ g.val.right = σ := by
  obtain ⟨ι, hι, _, ⟨σ, rfl⟩, hιc⟩ := Subgroup.mem_sup_of_normal_left.1 hc
  obtain ⟨γ, rfl⟩ := hι
  let g₁ : similarityPairs (coordinateQuadPlus 4 K) :=
    matrixIsometryInclusion _ ⟨γ.val, matrixDerived_le_isometries _ γ.2⟩
  have h1 : conjAct _ g₁ = MulAut.conj γ := conjAct_inclusion_of_mem _ γ.2
  refine ⟨g₁ * AutOm.gField σ, σ, MulAut.conj γ, ⟨γ, rfl⟩, hιc.symm, ?_, ?_⟩
  · rw [map_mul, h1, ← AutOm.fieldAutP_eq, hιc]
  · change (g₁.val * (AutOm.gField σ).val).right = σ
    simp [g₁, matrixIsometryInclusion, AutOm.gField, fieldPair]

theorem fixed_sub_om8 {n : ℕ} (hn1 : 1 ≤ n) (hK₀ : Nat.card K = 2 ^ n) {c : MulAut (Om8 K)}
    (hc3 : c ^ 3 = 1) (hcI : c ∈ Inn (Om8 K) ⊔ (AutOm.fieldAutP (K := K) 4).range)
    (hcn : c ∉ Inn (Om8 K)) :
    3 ∣ n ∧ ∃ k : Subfield K, Nat.card k = 2 ^ (n / 3) ∧ ∀ k₁ : Subfield K, k₁ ≤ k →
      ∃ j : matrixDerived (coordinateQuadPlus 4 ↥k₁) →* Om8 K,
        Function.Injective j ∧ ∀ x, c (j x) = j x := by
  classical
  have hQne : ∃ v, coordinateQuadPlus 4 K v ≠ 0 :=
    ⟨stdU K, by rw [coordinateQuadPlus_stdU]; exact one_ne_zero⟩
  let Λ := derivedProjEquiv (coordinateQuadPlus 4 K) hQne
  obtain ⟨g, σ', ι, hι, hcι, hgc, hgr⟩ := exists_pair_of_mem_sup hcI
  set a : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := MulAut.congr Λ c with ha
  have hag : matrixProjectiveConjugationHom (coordinateQuadPlus 4 K) g = a := by
    ext x
    obtain ⟨A, rfl⟩ := Λ.surjective x
    have h1 : matrixProjectiveConjugationHom (coordinateQuadPlus 4 K) g (Λ A) =
        Λ (matrixDerivedConjugation (coordinateQuadPlus 4 K) g A) :=
      matrixProjectiveConjugation_mk _ g A
    have h2 : (MulAut.congr Λ c) (Λ A) = Λ (c A) := by
      simp [MulAut.congr_apply]
    rw [h1, ha, h2, ← hgc]
    rfl
  have haE : a ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) :=
    (mem_matrixProjectiveImage_iff _ a).2 ⟨g, hag⟩
  have hc1 : c ≠ 1 := fun h => hcn (h ▸ Subgroup.one_mem _)
  have hap : orderOf a = 3 := by
    have h3 : a ^ 3 = 1 := by rw [ha, ← map_pow, hc3, map_one]
    have h1 : a ≠ 1 := fun h => hc1 ((MulAut.congr Λ).injective (by rw [map_one]; exact h))
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime h3 h1
  let e : matrixProjectiveDerived (coordinateQuadPlus 4 K) ≃*
      StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
    (statedProjectiveReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)).symm
  have hmodel : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus 4 K))
      .POmegaPlus 4 2 n :=
    ⟨⟨Nat.prime_two, hn1, le_refl 4⟩, K, inferInstance, inferInstance, hK₀, ⟨e⟩⟩
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates
    (matrixProjectiveDerived (coordinateQuadPlus 4 K)) .POmegaPlus (Or.inr (Or.inl rfl)) 4 2 n
    hmodel K hK₀ e
  obtain ⟨hker, ⟨ψ, hψg, hψker, -⟩, hrest⟩ := hgates
  have haD : a ∉ (linearConjugationHom (coordinateQuadPlus 4 K)).range := by
    intro hD
    have hmem : (⟨a, haE⟩ : matrixProjectiveImage (coordinateQuadPlus 4 K)) ∈ ψ.ker := by
      rw [hψker]
      exact hD
    have h1 : ψ ⟨a, haE⟩ = σ' := by
      have h2 := hψg g
      rw [hgr] at h2
      rw [← h2]
      congr 1
      exact Subtype.ext hag.symm
    rw [MonoidHom.mem_ker, h1] at hmem
    apply hcn
    rw [hcι, hmem, map_one, mul_one]
    exact hι
  obtain ⟨h3n, k, hk, hj⟩ := exists_fixed_embedding hn1 hK₀ a haE haD hap
  refine ⟨h3n, k, hk, fun k₁ hk₁ => ?_⟩
  obtain ⟨j, hjinj, hjfix⟩ := hj k₁ hk₁
  refine ⟨Λ.symm.toMonoidHom.comp j, Λ.symm.injective.comp hjinj, fun x => ?_⟩
  have h2 : a (j x) = Λ (c (Λ.symm (j x))) := by
    rw [ha, MulAut.congr_apply]
    rfl
  have h3 := hjfix x
  rw [h2] at h3
  change c (Λ.symm (j x)) = Λ.symm (j x)
  rw [← Λ.symm_apply_apply (c (Λ.symm (j x))), h3]

end FixedSub


end CFSG.LocalAnalysis.GLTheoremA.D4YH
