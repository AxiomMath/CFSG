module

public import CFSG.FeitThompson.Representations.DegreeZeroIsometryDisjointConjPairs
import CFSG.FeitThompson.Representations.DegreeZeroVirtualCharactersNormTwo
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality
import CFSG.FeitThompson.Representations.DisjointCoherentRowColumnContradiction

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

noncomputable section

variable {L G : Type*} [Group L] [Group G]

theorem eq_or_star_eq_of_cfInner_sub_sub_star_eq_one [Fintype G] {ρ σ η : G → ℂ}
    (hρ : ρ ∈ Irr G) (hσ : σ ∈ Irr G) (hη : η ∈ Irr G)
    (h : cfInner (ρ - σ) (η - star η) = 1) : ρ = η ∨ σ = star η := by
  classical
  by_contra hc
  rw [not_or] at hc
  obtain ⟨h1, h2⟩ := hc
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right,
    cfInner_eq_ite_of_mem_Irr hρ hη, cfInner_eq_ite_of_mem_Irr hρ (star_mem_Irr hη),
    cfInner_eq_ite_of_mem_Irr hσ hη, cfInner_eq_ite_of_mem_Irr hσ (star_mem_Irr hη),
    if_neg h1, if_neg h2] at h
  split_ifs at h <;> norm_num at h

theorem star_eq_or_eq_of_cfInner_sub_sub_star_eq_neg_one [Fintype G] {ρ σ η : G → ℂ}
    (hρ : ρ ∈ Irr G) (hσ : σ ∈ Irr G) (hη : η ∈ Irr G)
    (h : cfInner (ρ - σ) (η - star η) = -1) : ρ = star η ∨ σ = η := by
  have key := eq_or_star_eq_of_cfInner_sub_sub_star_eq_one hρ hσ (star_mem_Irr hη)
    (by rw [star_star, show star η - η = -(η - star η) by ring, cfInner_neg_right, h]; ring)
  rwa [star_star] at key

theorem cfInner_sub_sub_star_left_eq_one [Fintype L] {χ ψ : L → ℂ} (hχ : χ ∈ Irr L)
    (hψ : ψ ∈ Irr L) (hnr : star χ ≠ χ) (h1 : ψ ≠ χ) (h2 : ψ ≠ star χ) :
    cfInner (χ - ψ) (χ - star χ) = 1 := by
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, cfInner_self_of_mem_Irr hχ,
    cfInner_eq_zero_of_mem_Irr hχ (star_mem_Irr hχ) (Ne.symm hnr),
    cfInner_eq_zero_of_mem_Irr hψ hχ h1,
    cfInner_eq_zero_of_mem_Irr hψ (star_mem_Irr hχ) h2]
  ring

theorem cfInner_sub_sub_star_right_eq_neg_one [Fintype L] {χ ψ : L → ℂ} (hχ : χ ∈ Irr L)
    (hψ : ψ ∈ Irr L) (hnr : star ψ ≠ ψ) (h1 : ψ ≠ χ) (h2 : ψ ≠ star χ) :
    cfInner (χ - ψ) (ψ - star ψ) = -1 := by
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, cfInner_self_of_mem_Irr hψ,
    cfInner_eq_zero_of_mem_Irr hχ hψ (Ne.symm h1),
    cfInner_eq_zero_of_mem_Irr hχ (star_mem_Irr hψ) (fun hc => h2 (by rw [hc, star_star])),
    cfInner_eq_zero_of_mem_Irr hψ (star_mem_Irr hψ) (Ne.symm hnr)]
  ring

theorem sub_mem_charSpanZero_of_apply_one_eq {S : Set (L → ℂ)} {χ ψ : L → ℂ} (hχ : χ ∈ S)
    (hψ : ψ ∈ S) (hdeg : χ 1 = ψ 1) : χ - ψ ∈ charSpanZero S :=
  mem_charSpanZero.2
    ⟨sub_mem (Submodule.subset_span hχ) (Submodule.subset_span hψ), by simp [hdeg]⟩

namespace IsAntirealIsometry

variable [Fintype L] [Fintype G] {X : Set (L → ℂ)} {τ : (L → ℂ) → G → ℂ}
  (hτ : IsAntirealIsometry X τ)

include hτ

theorem root_eq_of_map_sub_star_eq {χ : L → ℂ} {η : G → ℂ} (hχ : χ ∈ X) (hη : η ∈ Irr G)
    (hηeq : τ (χ - star χ) = η - star η) : η = antirealRoot (τ (χ - star χ)) :=
  eq_of_sub_star_eq_sub_star (hτ.root_mem_Irr hχ) hη (hτ.star_root_ne hχ)
    ((hτ.map_sub_star_eq hχ).symm.trans hηeq)

theorem star_ne_of_map_sub_star_eq {χ : L → ℂ} {η : G → ℂ} (hχ : χ ∈ X) (hη : η ∈ Irr G)
    (hηeq : τ (χ - star χ) = η - star η) : star η ≠ η := by
  rw [hτ.root_eq_of_map_sub_star_eq hχ hη hηeq]; exact hτ.star_root_ne hχ

theorem disjoint_pair_of_map_sub_star_eq {χ ψ : L → ℂ} {η ξ : G → ℂ} (hχ : χ ∈ X) (hψ : ψ ∈ X)
    (h1 : ψ ≠ χ) (h2 : ψ ≠ star χ) (hη : η ∈ Irr G) (hξ : ξ ∈ Irr G)
    (hηeq : τ (χ - star χ) = η - star η) (hξeq : τ (ψ - star ψ) = ξ - star ξ) :
    Disjoint ({η, star η} : Set (G → ℂ)) {ξ, star ξ} := by
  rw [hτ.root_eq_of_map_sub_star_eq hχ hη hηeq, hτ.root_eq_of_map_sub_star_eq hψ hξ hξeq]
  exact hτ.disjoint_root_pair hχ hψ h1 h2

theorem map_sub_eq_or_eq {χ ψ : L → ℂ} {η ξ : G → ℂ} (hχ : χ ∈ X) (hψ : ψ ∈ X)
    (hdeg : χ 1 = ψ 1) (h1 : ψ ≠ χ) (h2 : ψ ≠ star χ) (hη : η ∈ Irr G) (hξ : ξ ∈ Irr G)
    (hηeq : τ (χ - star χ) = η - star η) (hξeq : τ (ψ - star ψ) = ξ - star ξ) :
    τ (χ - ψ) = η - ξ ∨ τ (χ - ψ) = star ξ - star η := by
  have hmem := sub_mem_charSpanZero_of_apply_one_eq hχ hψ hdeg
  have hχI := hτ.subset_Irr hχ
  have hψI := hτ.subset_Irr hψ
  have hnorm : cfInner (τ (χ - ψ)) (τ (χ - ψ)) = 2 := by
    rw [hτ.inner_eq _ hmem _ hmem]
    exact cfInner_self_sub_of_mem_Irr hχI hψI (Ne.symm h1)
  obtain ⟨ρ, hρ, σ, hσ, hne, hdeg', hv⟩ :=
    exists_sub_Irr_of_cfInner_self_eq_two (hτ.map_mem _ hmem) hnorm (hτ.apply_one _ hmem)
  have hone : cfInner (ρ - σ) (η - star η) = 1 := by
    rw [← hv, ← hηeq, hτ.inner_eq _ hmem _ (hτ.sub_star_mem hχ)]
    exact cfInner_sub_sub_star_left_eq_one hχI hψI (hτ.star_ne χ hχ) h1 h2
  have hnegone : cfInner (ρ - σ) (ξ - star ξ) = -1 := by
    rw [← hv, ← hξeq, hτ.inner_eq _ hmem _ (hτ.sub_star_mem hψ)]
    exact cfInner_sub_sub_star_right_eq_neg_one hχI hψI (hτ.star_ne ψ hψ) h1 h2
  have hd := Set.disjoint_left.1
    (hτ.disjoint_pair_of_map_sub_star_eq hχ hψ h1 h2 hη hξ hηeq hξeq)
  rcases eq_or_star_eq_of_cfInner_sub_sub_star_eq_one hρ hσ hη hone with hA | hA
  · rcases star_eq_or_eq_of_cfInner_sub_sub_star_eq_neg_one hρ hσ hξ hnegone with hB | hB
    · exact absurd (hA ▸ hB ▸ rfl : η = star ξ) fun hc => hd (a := η) (by simp) (by simp [hc])
    · exact Or.inl (by rw [hv, hA, hB])
  · rcases star_eq_or_eq_of_cfInner_sub_sub_star_eq_neg_one hρ hσ hξ hnegone with hB | hB
    · exact Or.inr (by rw [hv, hA, hB])
    · exact absurd (hA ▸ hB ▸ rfl : star η = ξ)
        fun hc => hd (a := star η) (by simp) (by simp [hc])

theorem apply_one_eq_of_map_sub_star_eq {χ ψ : L → ℂ} {η ξ : G → ℂ} (hχ : χ ∈ X) (hψ : ψ ∈ X)
    (hdeg : χ 1 = ψ 1) (h1 : ψ ≠ χ) (h2 : ψ ≠ star χ) (hη : η ∈ Irr G) (hξ : ξ ∈ Irr G)
    (hηeq : τ (χ - star χ) = η - star η) (hξeq : τ (ψ - star ψ) = ξ - star ξ) : η 1 = ξ 1 := by
  have hzero := hτ.apply_one _ (sub_mem_charSpanZero_of_apply_one_eq hχ hψ hdeg)
  rcases hτ.map_sub_eq_or_eq hχ hψ hdeg h1 h2 hη hξ hηeq hξeq with h | h
  · rw [h] at hzero
    simpa [sub_eq_zero] using hzero
  · rw [h] at hzero
    simp only [Pi.sub_apply, Pi.star_apply, Complex.star_def, sub_eq_zero] at hzero
    rw [← conj_apply_one_of_mem_Irr hη, ← conj_apply_one_of_mem_Irr hξ]
    exact hzero.symm

theorem map_sub_mem_span {χ ψ : L → ℂ} {η ξ : G → ℂ} (hχ : χ ∈ X) (hψ : ψ ∈ X)
    (hdeg : χ 1 = ψ 1) (hη : η ∈ Irr G) (hξ : ξ ∈ Irr G)
    (hηeq : τ (χ - star χ) = η - star η) (hξeq : τ (ψ - star ψ) = ξ - star ξ) :
    τ (χ - ψ) ∈ Submodule.span ℤ ({η, star η, ξ, star ξ} : Set (G → ℂ)) := by
  have hmη : η ∈ ({η, star η, ξ, star ξ} : Set (G → ℂ)) := by simp
  have hmsη : star η ∈ ({η, star η, ξ, star ξ} : Set (G → ℂ)) := by simp
  have hmξ : ξ ∈ ({η, star η, ξ, star ξ} : Set (G → ℂ)) := by simp
  have hmsξ : star ξ ∈ ({η, star η, ξ, star ξ} : Set (G → ℂ)) := by simp
  by_cases h1 : ψ = χ
  · subst h1
    rw [sub_self, hτ.map_zero]
    exact zero_mem _
  by_cases h2 : ψ = star χ
  · subst h2
    rw [hηeq]
    exact sub_mem (Submodule.subset_span hmη) (Submodule.subset_span hmsη)
  rcases hτ.map_sub_eq_or_eq hχ hψ hdeg h1 h2 hη hξ hηeq hξeq with h | h
  · rw [h]; exact sub_mem (Submodule.subset_span hmη) (Submodule.subset_span hmξ)
  · rw [h]; exact sub_mem (Submodule.subset_span hmsξ) (Submodule.subset_span hmsη)

theorem map_sub_root_mem_span {χ ψ : L → ℂ} (hχ : χ ∈ X) (hψ : ψ ∈ X) (hdeg : χ 1 = ψ 1) :
    τ (χ - ψ) ∈ Submodule.span ℤ
      ({antirealRoot (τ (χ - star χ)), star (antirealRoot (τ (χ - star χ))),
        antirealRoot (τ (ψ - star ψ)), star (antirealRoot (τ (ψ - star ψ)))} : Set (G → ℂ)) :=
  hτ.map_sub_mem_span hχ hψ hdeg (hτ.root_mem_Irr hχ) (hτ.root_mem_Irr hψ)
    (hτ.map_sub_star_eq hχ) (hτ.map_sub_star_eq hψ)

theorem map_sub_eq_or_eq_root {χ ψ : L → ℂ} (hχ : χ ∈ X) (hψ : ψ ∈ X) (hdeg : χ 1 = ψ 1)
    (h1 : ψ ≠ χ) (h2 : ψ ≠ star χ) :
    τ (χ - ψ) = antirealRoot (τ (χ - star χ)) - antirealRoot (τ (ψ - star ψ)) ∨
      τ (χ - ψ) =
        star (antirealRoot (τ (ψ - star ψ))) - star (antirealRoot (τ (χ - star χ))) :=
  hτ.map_sub_eq_or_eq hχ hψ hdeg h1 h2 (hτ.root_mem_Irr hχ) (hτ.root_mem_Irr hψ)
    (hτ.map_sub_star_eq hχ) (hτ.map_sub_star_eq hψ)

theorem root_apply_one_eq {χ ψ : L → ℂ} (hχ : χ ∈ X) (hψ : ψ ∈ X) (hdeg : χ 1 = ψ 1)
    (h1 : ψ ≠ χ) (h2 : ψ ≠ star χ) :
    antirealRoot (τ (χ - star χ)) 1 = antirealRoot (τ (ψ - star ψ)) 1 :=
  hτ.apply_one_eq_of_map_sub_star_eq hχ hψ hdeg h1 h2 (hτ.root_mem_Irr hχ)
    (hτ.root_mem_Irr hψ) (hτ.map_sub_star_eq hχ) (hτ.map_sub_star_eq hψ)

end IsAntirealIsometry

end

end CFSG.FeitThompson
