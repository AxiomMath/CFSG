module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalEndData

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

omit [Finite G] in
theorem omegaOne_rightConjugate (P : Subgroup G) (x : G) :
    AschbacherTheorem3.omegaOne (rightConjugate P x) =
      rightConjugate (AschbacherTheorem3.omegaOne P) x := by
  apply le_antisymm
  · rw [AschbacherTheorem3.omegaOne, Subgroup.closure_le]
    rintro y ⟨hy, hy2⟩
    rw [SetLike.mem_coe, mem_rightConjugate_iff]
    rw [mem_rightConjugate_iff] at hy
    refine mem_omegaOne hy ?_
    rw [conj_pow, hy2]
    group
  · rw [rightConjugate, Subgroup.map_le_iff_le_comap, AschbacherTheorem3.omegaOne,
      Subgroup.closure_le]
    rintro y ⟨hy, hy2⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    refine mem_omegaOne ?_ ?_
    · rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using hy
    · change (x⁻¹ * y * x⁻¹⁻¹) ^ 2 = 1
      rw [conj_pow, hy2]
      group

omit [Finite G] in
theorem card_omegaOne_rightConjugate (P : Subgroup G) (x : G) :
    Nat.card (AschbacherTheorem3.omegaOne (rightConjugate P x)) =
      Nat.card (AschbacherTheorem3.omegaOne P) := by
  rw [omegaOne_rightConjugate, rightConjugate_card]

theorem swap_T {a : Fin r} (d d' : DeltaDatum D Abar a) (hg : d'.g = d.g⁻¹)
    (hW : IsSylowOf 2 (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))
      (aschbacherThm5Preimage D (Abar a) ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))) :
    ∃ c : G, d'.T = rightConjugate (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)) c := by
  have h1 := AschbacherTheorem3.isSylowOf_rightConjugate hW d.g⁻¹
  rw [rightConjugate_inf_normalizer'] at h1
  have h2 := d'.sylowT
  rw [hg] at h2
  obtain ⟨c, -, hc⟩ := AschbacherTheorem3.exists_rightConjugate_eq_of_isSylowOf h2 h1
  refine ⟨d.g⁻¹ * c, ?_⟩
  rw [← rightConjugate_mul, hc]

theorem swap_W {a : Fin r} (d d' : DeltaDatum D Abar a) (hg : d'.g = d.g⁻¹)
    (hW' : IsSylowOf 2 (d'.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d'.g : Set G))
      (aschbacherThm5Preimage D (Abar a) ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d'.g : Set G))) :
    ∃ c ∈ aschbacherThm5Preimage D (Abar a),
      d'.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d'.g : Set G) =
        rightConjugate d.T (d.g⁻¹ * c) := by
  have h1 := AschbacherTheorem3.isSylowOf_rightConjugate d.sylowT d.g⁻¹
  rw [rightConjugate_inf_normalizer] at h1
  rw [hg] at hW'
  obtain ⟨c, hc, hcW⟩ := AschbacherTheorem3.exists_rightConjugate_eq_of_isSylowOf hW' h1
  refine ⟨c, hc.1, ?_⟩
  rw [hg, ← hcW, rightConjugate_mul]

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
