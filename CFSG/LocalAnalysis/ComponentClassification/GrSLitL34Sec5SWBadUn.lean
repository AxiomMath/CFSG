module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryCentralizer
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer

theorem exists_sq_ne_one_of_unitary {G : Type} [Group G] [Finite G] {J S : Subgroup G}
    (hJ : ⁅J, J⁆ = J) (hL : IsL34Type (J ⧸ Open.fusionZStar J)) (hP : IsSylowTwoIn (S ⊓ J) J)
    {b : G} (hbS : b ∈ S) (hU : IsL34Unitary J b) (hZc : IsCyclic ↥(S ⊓ zStarIn J)) :
    ∃ y ∈ S ⊓ J, y * b = b * y ∧ y * y ≠ 1 ∧ y * y * (y * y) = 1 := by
  have hbN : b ∈ normalizer ((S ⊓ J : Subgroup G) : Set G) :=
    UnbalancedLayer.normalizer_inf_mem (le_normalizer hbS) hU.1
  obtain ⟨-, -, -, hQ8, hcyc, -, -, -⟩ :=
    L34Facts.l34UnitaryCentralizerFact G J (S ⊓ J) b hJ hL hU hP hbN
  have hzJ : zStarIn J ≤ J := map_subtype_le _
  have hZP : S ⊓ J ⊓ zStarIn J = S ⊓ zStarIn J := by rw [inf_assoc, inf_eq_right.mpr hzJ]
  by_cases hZ : S ⊓ zStarIn J = ⊥
  · obtain ⟨e⟩ := hQ8 (by rw [hZP]; exact hZ)
    have h2 : (QuaternionGroup.a 1 * QuaternionGroup.a 1 : QuaternionGroup 2) ≠ 1 := by decide
    have h4 : (QuaternionGroup.a 1 * QuaternionGroup.a 1 *
        (QuaternionGroup.a 1 * QuaternionGroup.a 1) : QuaternionGroup 2) = 1 := by decide
    set y0 : ↥(S ⊓ J ⊓ centralizer ({b} : Set G)) := e.symm (QuaternionGroup.a 1) with hy0
    have hy0m := mem_inf.mp y0.2
    refine ⟨y0, hy0m.1, mem_centralizer_singleton_iff.mp hy0m.2, fun h => h2 ?_, ?_⟩
    · apply e.symm.injective
      rw [map_mul, map_one]
      exact Subtype.ext h
    · have := congrArg (fun q => ((e.symm q : ↥(S ⊓ J ⊓ centralizer ({b} : Set G))) : G)) h4
      simp only [map_mul, map_one, Subgroup.coe_mul, OneMemClass.coe_one] at this
      exact this
  · set R : Subgroup G := S ⊓ J ⊓ centralizer ({b} : Set G) with hRdef
    obtain ⟨-, hRexp⟩ := hcyc (by rwa [hZP]) (by rwa [hZP])
    obtain ⟨w, hwR, hw1⟩ : ∃ w ∈ R, w * w ≠ 1 := by
      by_contra h
      push Not at h
      have hd : Monoid.exponent ↥R ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one fun r =>
        Subtype.ext (by rw [pow_two]; exact h r r.2)
      rw [hRexp] at hd
      norm_num at hd
    have hw4 : w * w * (w * w) = 1 := by
      have h1 := congrArg Subtype.val (Monoid.pow_exponent_eq_one (⟨w, hwR⟩ : ↥R))
      rw [hRexp] at h1
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
      rw [show w * w * (w * w) = w ^ 4 by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
      exact h1
    exact ⟨w, (mem_inf.mp hwR).1, mem_centralizer_singleton_iff.mp (mem_inf.mp hwR).2, hw1, hw4⟩

end CFSG.ComponentClassification.GrSLit.GrS5S
