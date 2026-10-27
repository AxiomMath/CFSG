module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Classify

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Transport

variable {S S' : Type} [Group S] [Group S']

theorem fixedSubgroup_congr_eq (e : S ≃* S') (σ : MulAut S) :
    fixedSubgroup (MulAut.congr e σ) = (fixedSubgroup σ).map e.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv]
  change e (σ (e.symm x)) = x ↔ σ (e.symm x) = e.symm x
  constructor
  · intro h
    have := congrArg e.symm h
    simpa using this
  · intro h
    rw [h]
    simp

def fixedEquiv (e : S ≃* S') (σ : MulAut S) :
    ↥(fixedSubgroup σ) ≃* ↥(fixedSubgroup (MulAut.congr e σ)) :=
  (MulEquiv.subgroupMap e _).trans (MulEquiv.subgroupCongr (fixedSubgroup_congr_eq e σ).symm)

theorem congr_conj_eq (e : S ≃* S') (g : S) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem congr_mem_range_iff (e : S ≃* S') (σ : MulAut S) :
    MulAut.congr e σ ∈ (MulAut.conj : S' →* MulAut S').range ↔
      σ ∈ (MulAut.conj : S →* MulAut S).range := by
  constructor
  · rintro ⟨g', hg'⟩
    refine ⟨e.symm g', ?_⟩
    have h1 : MulAut.congr e σ = MulAut.conj g' := hg'.symm
    have h2 : σ = MulAut.congr e.symm (MulAut.conj g') := by
      rw [← h1]; ext x; simp [MulAut.congr_apply]
    rw [h2, congr_conj_eq]
  · rintro ⟨g, hg⟩
    refine ⟨e g, ?_⟩
    rw [← hg, congr_conj_eq]

theorem orderOf_congr (e : S ≃* S') (σ : MulAut S) : orderOf (MulAut.congr e σ) = orderOf σ :=
  orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective σ

theorem a6Hyp_congr (e : S ≃* S') (σ : MulAut S) (D : Subgroup ↥(fixedSubgroup σ))
    (h : A6Hyp σ D) :
    A6Hyp (MulAut.congr e σ) (D.map (fixedEquiv e σ).toMonoidHom) := by
  obtain ⟨hDn, ⟨eD⟩, hperf⟩ := h
  set Φ := fixedEquiv e σ with hΦ
  refine ⟨Subgroup.Normal.map hDn Φ.toMonoidHom Φ.surjective,
    ⟨(D.equivMapOfInjective Φ.toMonoidHom Φ.injective).symm.trans eD⟩, ?_⟩
  intro P' hP'
  have hP : ⁅P'.map Φ.symm.toMonoidHom, P'.map Φ.symm.toMonoidHom⁆ = P'.map Φ.symm.toMonoidHom := by
    rw [← Subgroup.map_commutator, hP']
  have h1 := hperf _ hP
  calc P' = (P'.map Φ.symm.toMonoidHom).map Φ.toMonoidHom := by
        rw [Subgroup.map_map]
        convert (Subgroup.map_id P').symm using 2
        ext x; simp
    _ ≤ D.map Φ.toMonoidHom := Subgroup.map_mono h1

theorem a6ShapeConcl_of_congr (e : S ≃* S') (σ : MulAut S) (D : Subgroup ↥(fixedSubgroup σ))
    {t : StatedLieTag} {n p f : ℕ}
    (h : A6ShapeConcl t n p f (MulAut.congr e σ) (D.map (fixedEquiv e σ).toMonoidHom)) :
    A6ShapeConcl t n p f σ D := by
  obtain ⟨hp, hs, hc⟩ := h
  refine ⟨hp, hs, fun h1 h2 h3 => ?_⟩
  obtain ⟨a, b, hab⟩ := hc h1 h2 h3
  refine ⟨(fixedEquiv e σ).symm a, (fixedEquiv e σ).symm b, fun hmem => hab ?_⟩
  have := Subgroup.mem_map_of_mem (fixedEquiv e σ).toMonoidHom hmem
  simpa using this

theorem a6SmallConcl_of_congr (e : S ≃* S') (σ : MulAut S) (D : Subgroup ↥(fixedSubgroup σ))
    {t : StatedLieTag} {n f : ℕ}
    (h : A6SmallConcl t n f (MulAut.congr e σ) (D.map (fixedEquiv e σ).toMonoidHom)) :
    A6SmallConcl t n f σ D := by
  obtain ⟨hin, hout⟩ := h
  have hcard : Nat.card (fixedSubgroup (MulAut.congr e σ)) = Nat.card (fixedSubgroup σ) :=
    (Nat.card_congr (fixedEquiv e σ).toEquiv).symm
  refine ⟨fun hσ => ?_, fun hσ h720 => ?_⟩
  · rw [← hcard]; exact hin ((congr_mem_range_iff e σ).2 hσ)
  · have hσ' : MulAut.congr e σ ∉ (MulAut.conj : S' →* MulAut S').range :=
      fun h' => hσ ((congr_mem_range_iff e σ).1 h')
    obtain ⟨hc720, hx⟩ := hout hσ' (by rw [hcard]; exact h720)
    refine ⟨by rw [← hcard]; exact hc720, ?_⟩
    rcases hx with ⟨x, hx2, hxD⟩ | hU
    · left
      refine ⟨(fixedEquiv e σ).symm x, ?_, fun hmem => hxD ?_⟩
      · rw [← hx2]
        exact orderOf_injective (fixedEquiv e σ).symm.toMonoidHom (fixedEquiv e σ).symm.injective x
      · have := Subgroup.mem_map_of_mem (fixedEquiv e σ).toMonoidHom hmem
        simpa using this
    · exact Or.inr hU

end Transport

theorem oddA6Shape_of_concrete {t : StatedLieTag}
    (H : ∀ (S : Type) [Group S] [Finite S] (n p f : ℕ), p.Prime → p ≠ 2 →
      StatedLieAdmissible t n p f → LieModel S t n p f →
      ∃ (X : Type) (_ : Group X) (_ : Finite X) (_ : S ≃* X),
        ∀ (σ : MulAut X) (D : Subgroup ↥(fixedSubgroup σ)), orderOf σ = 2 → A6Hyp σ D →
          A6ShapeConcl t n p f σ D) :
    OddA6Shape t := by
  intro S _ _ n p f hp hp2 hadm hm σ hσ D hD
  obtain ⟨X, _, _, e, hX⟩ := H S n p f hp hp2 hadm hm
  exact a6ShapeConcl_of_congr e σ D
    (hX (MulAut.congr e σ) _ ((orderOf_congr e σ).trans hσ) (a6Hyp_congr e σ D hD))

theorem oddA6Small_of_concrete {t : StatedLieTag}
    (H : ∀ (S : Type) [Group S] [Finite S] (n p f : ℕ), p.Prime → p ≠ 2 →
      StatedLieAdmissible t n p f → LieModel S t n p f → p = 3 → A6Shape t n f →
      ∃ (X : Type) (_ : Group X) (_ : Finite X) (_ : S ≃* X),
        ∀ (σ : MulAut X) (D : Subgroup ↥(fixedSubgroup σ)), orderOf σ = 2 → A6Hyp σ D →
          A6SmallConcl t n f σ D) :
    OddA6Small t := by
  intro S _ _ n p f hp hp2 hadm hm hp3 hs σ hσ D hD
  obtain ⟨X, _, _, e, hX⟩ := H S n p f hp hp2 hadm hm hp3 hs
  exact a6SmallConcl_of_congr e σ D
    (hX (MulAut.congr e σ) _ ((orderOf_congr e σ).trans hσ) (a6Hyp_congr e σ D hD))

end CFSG.ComponentClassification.CatFC
