module

public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap
import CFSG.FeitThompson.Representations.DisjointCoherentRowColumnContradiction
import CFSG.FeitThompson.Representations.DegreeZeroVirtualCharactersNormTwo
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

noncomputable section

variable {L G : Type*} [Group L] [Group G]

theorem star_mem_Irr [Finite G] {χ : G → ℂ} (hχ : χ ∈ Irr G) : star χ ∈ Irr G :=
  conj_mem_Irr hχ

omit [Group L] in
theorem star_sub_star_self (f : L → ℂ) : star (f - star f) = -(f - star f) := by
  rw [star_sub, star_star, neg_sub]

theorem sub_star_mem_charSpanZero {S : Set (L → ℂ)} (hS : S ⊆ Irr L)
    (hSstar : ∀ χ ∈ S, star χ ∈ S) {χ : L → ℂ} (hχ : χ ∈ S) :
    χ - star χ ∈ charSpanZero S := by
  refine mem_charSpanZero.2
    ⟨sub_mem (Submodule.subset_span hχ) (Submodule.subset_span (hSstar χ hχ)), ?_⟩
  simp only [Pi.sub_apply, Pi.star_apply, Complex.star_def]
  rw [conj_apply_one_of_mem_Irr (hS hχ), sub_self]

theorem cfInner_sub_star_sub_star_eq_zero [Fintype L] {χ ψ : L → ℂ} (hχ : χ ∈ Irr L)
    (hψ : ψ ∈ Irr L) (h1 : ψ ≠ χ) (h2 : ψ ≠ star χ) :
    cfInner (χ - star χ) (ψ - star ψ) = 0 := by
  have hsχ := star_mem_Irr hχ
  have hsψ := star_mem_Irr hψ
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right,
    cfInner_eq_zero_of_mem_Irr hχ hψ (Ne.symm h1),
    cfInner_eq_zero_of_mem_Irr hχ hsψ (by rintro rfl; exact h2 (by rw [star_star])),
    cfInner_eq_zero_of_mem_Irr hsχ hψ (Ne.symm h2),
    cfInner_eq_zero_of_mem_Irr hsχ hsψ fun hc => h1 (star_injective hc).symm]
  ring

theorem eq_of_sub_star_eq_sub_star [Finite G] {η ρ : G → ℂ} (hη : η ∈ Irr G) (hρ : ρ ∈ Irr G)
    (hnr : star η ≠ η) (h : η - star η = ρ - star ρ) : ρ = η := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have key : cfInner (η - star η) η = cfInner (ρ - star ρ) η := by rw [h]
  rw [cfInner_sub_left, cfInner_sub_left, cfInner_self_of_mem_Irr hη,
    cfInner_eq_ite_of_mem_Irr (star_mem_Irr hη) hη, cfInner_eq_ite_of_mem_Irr hρ hη,
    cfInner_eq_ite_of_mem_Irr (star_mem_Irr hρ) hη, if_neg hnr] at key
  by_cases h1 : ρ = η
  · exact h1
  rw [if_neg h1] at key
  by_cases h2 : star ρ = η
  · rw [if_pos h2] at key; norm_num at key
  · rw [if_neg h2] at key; norm_num at key

theorem exists_sub_star_Irr_of_cfInner_self_eq_two [Fintype G] {z : G → ℂ}
    (hz : z ∈ Submodule.span ℤ (Irr G)) (hnorm : cfInner z z = 2) (hz1 : z 1 = 0)
    (hstar : star z = -z) : ∃ η ∈ Irr G, star η ≠ η ∧ z = η - star η := by
  classical
  obtain ⟨ρ, hρ, σ, hσ, hne, hdeg, rfl⟩ := exists_sub_Irr_of_cfInner_self_eq_two hz hnorm hz1
  rw [star_sub] at hstar
  have hkey : ρ + star ρ = σ + star σ := by linear_combination (norm := module) hstar
  have hpair : cfInner (ρ + star ρ) ρ = cfInner (σ + star σ) ρ := by rw [hkey]
  rw [cfInner_add_left, cfInner_add_left, cfInner_self_of_mem_Irr hρ,
    cfInner_eq_ite_of_mem_Irr (star_mem_Irr hρ) hρ, cfInner_eq_ite_of_mem_Irr hσ hρ,
    cfInner_eq_ite_of_mem_Irr (star_mem_Irr hσ) hρ, if_neg (Ne.symm hne)] at hpair
  have hρnr : star ρ ≠ ρ := by
    intro h
    rw [if_pos h] at hpair
    by_cases h2 : star σ = ρ
    · rw [if_pos h2] at hpair; norm_num at hpair
    · rw [if_neg h2] at hpair; norm_num at hpair
  rw [if_neg hρnr] at hpair
  have hσρ : star σ = ρ := by
    by_contra h2
    rw [if_neg h2] at hpair
    norm_num at hpair
  exact ⟨ρ, hρ, hρnr, by rw [← hσρ, star_star]⟩

theorem disjoint_pair_of_cfInner_sub_star_eq_zero [Fintype G] {η σ : G → ℂ} (hσ : σ ∈ Irr G)
    (hσnr : star σ ≠ σ) (h : cfInner (η - star η) (σ - star σ) = 0) :
    Disjoint ({η, star η} : Set (G → ℂ)) {σ, star σ} := by
  have hnormσ : cfInner (σ - star σ) (σ - star σ) = 2 :=
    cfInner_self_sub_of_mem_Irr hσ (star_mem_Irr hσ) (Ne.symm hσnr)
  have h1 : η ≠ σ := by
    rintro rfl
    rw [hnormσ] at h
    norm_num at h
  have h2 : η ≠ star σ := by
    rintro rfl
    rw [star_star, show (star σ : G → ℂ) - σ = -(σ - star σ) by ring, cfInner_neg_left,
      hnormσ] at h
    norm_num at h
  refine Set.disjoint_iff_forall_ne.2 ?_
  rintro a ha b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact h1
  · exact h2
  · exact fun hc => h2 (by rw [← hc, star_star])
  · exact fun hc => h1 (star_injective hc)

open scoped Classical in
def antirealRoot (z : G → ℂ) : G → ℂ :=
  if h : ∃ η ∈ Irr G, star η ≠ η ∧ z = η - star η then h.choose else 0

section Root

variable {z : G → ℂ}

theorem antirealRoot_spec (h : ∃ η ∈ Irr G, star η ≠ η ∧ z = η - star η) :
    antirealRoot z ∈ Irr G ∧ star (antirealRoot z) ≠ antirealRoot z ∧
      z = antirealRoot z - star (antirealRoot z) := by
  classical
  rw [antirealRoot, dif_pos h]
  exact h.choose_spec

theorem antirealRoot_mem_Irr (h : ∃ η ∈ Irr G, star η ≠ η ∧ z = η - star η) :
    antirealRoot z ∈ Irr G := (antirealRoot_spec h).1

theorem star_antirealRoot_ne (h : ∃ η ∈ Irr G, star η ≠ η ∧ z = η - star η) :
    star (antirealRoot z) ≠ antirealRoot z := (antirealRoot_spec h).2.1

theorem sub_star_antirealRoot (h : ∃ η ∈ Irr G, star η ≠ η ∧ z = η - star η) :
    antirealRoot z - star (antirealRoot z) = z := (antirealRoot_spec h).2.2.symm

theorem antirealRoot_sub_star [Finite G] {η : G → ℂ} (hη : η ∈ Irr G) (hnr : star η ≠ η) :
    antirealRoot (η - star η) = η := by
  have h : ∃ ρ ∈ Irr G, star ρ ≠ ρ ∧ η - star η = ρ - star ρ := ⟨η, hη, hnr, rfl⟩
  exact eq_of_sub_star_eq_sub_star hη (antirealRoot_mem_Irr h) hnr (antirealRoot_spec h).2.2

theorem antirealRoot_eq_of_eq_sub_star [Finite G] {η : G → ℂ} (hη : η ∈ Irr G)
    (hnr : star η ≠ η) (hz : z = η - star η) : antirealRoot z = η := by
  rw [hz, antirealRoot_sub_star hη hnr]

theorem antirealRoot_neg [Finite G] (h : ∃ η ∈ Irr G, star η ≠ η ∧ z = η - star η) :
    antirealRoot (-z) = star (antirealRoot z) := by
  obtain ⟨h1, h2, h3⟩ := antirealRoot_spec h
  refine antirealRoot_eq_of_eq_sub_star (star_mem_Irr h1)
    (fun hc => h2 (by rw [star_star] at hc; exact hc.symm)) ?_
  rw [star_star]
  conv_lhs => rw [h3]
  ring

end Root

structure IsAntirealIsometry [Fintype L] [Fintype G] (X : Set (L → ℂ))
    (τ : (L → ℂ) → G → ℂ) : Prop where
  subset_Irr : X ⊆ Irr L
  star_mem : ∀ χ ∈ X, star χ ∈ X
  star_ne : ∀ χ ∈ X, star χ ≠ χ
  map_add : ∀ f ∈ charSpanZero X, ∀ h ∈ charSpanZero X, τ (f + h) = τ f + τ h
  map_mem : ∀ f ∈ charSpanZero X, τ f ∈ Submodule.span ℤ (Irr G)
  inner_eq : ∀ f ∈ charSpanZero X, ∀ h ∈ charSpanZero X, cfInner (τ f) (τ h) = cfInner f h
  apply_one : ∀ f ∈ charSpanZero X, τ f 1 = 0
  map_star : ∀ f ∈ charSpanZero X, τ (star f) = star (τ f)

namespace IsAntirealIsometry

variable [Fintype L] [Fintype G] {X : Set (L → ℂ)} {τ : (L → ℂ) → G → ℂ}
  (hτ : IsAntirealIsometry X τ)

include hτ

theorem map_zero : τ 0 = 0 := by
  have h0 : (0 : L → ℂ) ∈ charSpanZero X := zero_mem _
  have hadd := hτ.map_add 0 h0 0 h0
  rw [add_zero] at hadd
  exact left_eq_add.1 hadd

theorem map_neg {f : L → ℂ} (hf : f ∈ charSpanZero X) : τ (-f) = -τ f := by
  have hadd := hτ.map_add f hf (-f) (neg_mem hf)
  rw [add_neg_cancel, hτ.map_zero] at hadd
  exact eq_neg_of_add_eq_zero_right hadd.symm

theorem sub_star_mem {χ : L → ℂ} (hχ : χ ∈ X) : χ - star χ ∈ charSpanZero X :=
  sub_star_mem_charSpanZero hτ.subset_Irr hτ.star_mem hχ

theorem star_map_sub_star {χ : L → ℂ} (hχ : χ ∈ X) :
    star (τ (χ - star χ)) = -τ (χ - star χ) := by
  rw [← hτ.map_star _ (hτ.sub_star_mem hχ), star_sub_star_self,
    hτ.map_neg (hτ.sub_star_mem hχ)]

theorem exists_root {χ : L → ℂ} (hχ : χ ∈ X) :
    ∃ η ∈ Irr G, star η ≠ η ∧ τ (χ - star χ) = η - star η :=
  exists_sub_star_Irr_of_cfInner_self_eq_two (hτ.map_mem _ (hτ.sub_star_mem hχ))
    (by
      rw [hτ.inner_eq _ (hτ.sub_star_mem hχ) _ (hτ.sub_star_mem hχ)]
      exact cfInner_self_sub_of_mem_Irr (hτ.subset_Irr hχ)
        (star_mem_Irr (hτ.subset_Irr hχ)) (Ne.symm (hτ.star_ne χ hχ)))
    (hτ.apply_one _ (hτ.sub_star_mem hχ)) (hτ.star_map_sub_star hχ)

theorem existsUnique_root {χ : L → ℂ} (hχ : χ ∈ X) :
    ∃! η : G → ℂ, η ∈ Irr G ∧ star η ≠ η ∧ τ (χ - star χ) = η - star η := by
  obtain ⟨η, hη, hηnr, hηeq⟩ := hτ.exists_root hχ
  refine ⟨η, ⟨hη, hηnr, hηeq⟩, fun ρ hρ => ?_⟩
  exact eq_of_sub_star_eq_sub_star hη hρ.1 hηnr (hηeq ▸ hρ.2.2 ▸ rfl)

theorem root_mem_Irr {χ : L → ℂ} (hχ : χ ∈ X) : antirealRoot (τ (χ - star χ)) ∈ Irr G :=
  antirealRoot_mem_Irr (hτ.exists_root hχ)

theorem star_root_ne {χ : L → ℂ} (hχ : χ ∈ X) :
    star (antirealRoot (τ (χ - star χ))) ≠ antirealRoot (τ (χ - star χ)) :=
  star_antirealRoot_ne (hτ.exists_root hχ)

theorem map_sub_star_eq {χ : L → ℂ} (hχ : χ ∈ X) :
    τ (χ - star χ) = antirealRoot (τ (χ - star χ)) - star (antirealRoot (τ (χ - star χ))) :=
  (antirealRoot_spec (hτ.exists_root hχ)).2.2

theorem root_star {χ : L → ℂ} (hχ : χ ∈ X) :
    antirealRoot (τ (star χ - star (star χ))) = star (antirealRoot (τ (χ - star χ))) := by
  have hneg : star χ - star (star χ) = -(χ - star χ) := by rw [star_star]; ring
  rw [hneg, hτ.map_neg (hτ.sub_star_mem hχ), antirealRoot_neg (hτ.exists_root hχ)]

theorem disjoint_root_pair {χ ψ : L → ℂ} (hχ : χ ∈ X) (hψ : ψ ∈ X) (h1 : ψ ≠ χ)
    (h2 : ψ ≠ star χ) :
    Disjoint
      ({antirealRoot (τ (χ - star χ)), star (antirealRoot (τ (χ - star χ)))} : Set (G → ℂ))
      {antirealRoot (τ (ψ - star ψ)), star (antirealRoot (τ (ψ - star ψ)))} := by
  refine disjoint_pair_of_cfInner_sub_star_eq_zero (hτ.root_mem_Irr hψ) (hτ.star_root_ne hψ) ?_
  rw [← hτ.map_sub_star_eq hχ, ← hτ.map_sub_star_eq hψ,
    hτ.inner_eq _ (hτ.sub_star_mem hχ) _ (hτ.sub_star_mem hψ)]
  exact cfInner_sub_star_sub_star_eq_zero (hτ.subset_Irr hχ) (hτ.subset_Irr hψ) h1 h2

end IsAntirealIsometry

end

end CFSG.FeitThompson
