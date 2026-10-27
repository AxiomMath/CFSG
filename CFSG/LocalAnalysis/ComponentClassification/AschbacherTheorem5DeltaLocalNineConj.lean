module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalNineSylow

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaLocal.Nine

open SectionSix SectionSix.BarTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

omit [Finite G] in
theorem centralizing_conj (g : G) (i : Fin r) :
    centralizing (rightConjugate D g) (conjFactors D Abar g i) =
      rightConjugate (centralizing D (Abar i)) g := by
  ext y
  rw [mem_centralizing_iff, mem_rightConjugate_iff, mem_rightConjugate_iff, mem_centralizing_iff,
    centralizes_conj_iff]

omit [Finite G] in
theorem factorZStar_conj (g : G) (i : Fin r) :
    factorZStar (rightConjugate D g) (conjFactors D Abar g) i =
      rightConjugate (factorZStar D Abar i) g := by
  rw [factorZStar, factorZStar, preimage_conjFactors, centralizing_conj,
    AschbacherTheorem3.rightConjugate_inf]

theorem normalizes_conj_of_le (h3 : AschbacherTheorem3.Theorem3Statement)
    (hin : SectionSixInputs) (hC : Counterexample G D r Abar) {g : G}
    (hΔ : rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G))) (hr : 3 ≤ r) {i : Fin r}
    {P : Subgroup G} (hP2 : IsPGroup 2 P) (hPA : P ≤ aschbacherThm5Preimage D (Abar i))
    (hPH : P ≤ rightConjugate (Subgroup.normalizer (D : Set G)) g) (k : Fin r) :
    P ≤ Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar k)) g : Set G) := by
  have h := normalizes_of_le h3 hin (hC.conj g) (delta_conj h3 hin hC hΔ) hr (i := i) hP2
    (by rw [preimage_conjFactors, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
        exact hPA)
    (by rw [normalizer_rightConjugate]; exact hPH) k
  rwa [preimage_conjFactors] at h

theorem not_le_factorZStar_conj (h3 : AschbacherTheorem3.Theorem3Statement)
    (hin : SectionSixInputs) (hC : Counterexample G D r Abar) {g : G}
    (hΔ : rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G))) (i : Fin r) {T : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate (aschbacherThm5Preimage D (Abar i)) g ⊓
      Subgroup.normalizer (D : Set G))) :
    ¬ T ≤ rightConjugate (factorZStar D Abar i) g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx, hxZ, k, hk⟩ := lemma_6_5_two h3 hin (hC.conj g) (delta_conj h3 hin hC hΔ) i
  rw [preimage_conjFactors, Six.conj_normalizer_inv, factorZStar_conj] at *
  obtain ⟨c, hc, hcle⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hT
    (Five.isPGroup_zpowers_of_pow hk) (Subgroup.zpowers_le.mpr hx)
  intro hTZ
  apply hxZ
  have hcx := hTZ (hcle (AschbacherTheorem3.conj_mem_rightConjugate (Subgroup.mem_zpowers x) c))
  have hc' : c ∈ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g i) := by
    rw [preimage_conjFactors]
    exact hc.1
  rw [← factorZStar_conj] at hcx ⊢
  have := conj_mem_factorZStar (c := c) hc' hcx
  simpa [mul_assoc] using this

end DeltaLocal.Nine

end CFSG.ComponentClassification.AschbacherTheorem5
