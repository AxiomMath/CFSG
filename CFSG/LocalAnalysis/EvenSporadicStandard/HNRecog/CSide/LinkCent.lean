module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.BaseSwap

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Subgroup Module CFSG.RankThree.Literature.FSmith CFSG.EvenSporadicStandard.HNRecog.Fpf
  CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

variable {C : Type} [Group C] {Q : Subgroup C} [hQn : Q.Normal]
  [Module (ZMod 2) (Additive (Abelianization Q))]

private lemma cSide_conjLinEquiv_eq_one_iff_mem (hC : WeakHyp C Q) (x : C) :
    conjLinEquiv hQn x = 1 ↔ x ∈ Q := by
  haveI : Finite Q := hC.plus.finite
  have hE := hC.plus.isExtraspecialPGroup
  refine ⟨?_, fun hx => conjLinEquiv_eq_one_of_mem hx⟩
  intro hx
  refine mem_of_extraspecialConjOrth_eq_one (hQ := hE) (hQn := hQn) hC.centralizer_le ?_
  refine Subtype.ext ?_
  show (extraspecialConjOrth hE hQn x : Additive (Abelianization Q) ≃ₗ[ZMod 2]
    Additive (Abelianization Q)) = 1
  rw [show (extraspecialConjOrth hE hQn x : Additive (Abelianization Q) ≃ₗ[ZMod 2]
    Additive (Abelianization Q)) = conjLinEquiv hQn x from rfl, hx]

private lemma cSide_conjLinEquiv_comm_iff (hC : WeakHyp C Q) (x σ : C) :
    conjLinEquiv hQn x * conjLinEquiv hQn σ = conjLinEquiv hQn σ * conjLinEquiv hQn x ↔
      (x : C ⧸ Q) * (σ : C ⧸ Q) = (σ : C ⧸ Q) * (x : C ⧸ Q) := by
  have hL : (conjLinEquiv hQn x * conjLinEquiv hQn σ
      = conjLinEquiv hQn σ * conjLinEquiv hQn x) ↔ conjLinEquiv hQn ⁅x, σ⁆ = 1 := by
    rw [← commutatorElement_eq_one_iff_mul_comm,
      ← map_commutatorElement (f := conjLinEquiv hQn) (g₁ := x) (g₂ := σ)]
  have hR : ((x : C ⧸ Q) * (σ : C ⧸ Q) = (σ : C ⧸ Q) * (x : C ⧸ Q)) ↔
      conjLinEquiv hQn ⁅x, σ⁆ = 1 := by
    rw [← commutatorElement_eq_one_iff_mul_comm]
    change ⁅QuotientGroup.mk' Q x, QuotientGroup.mk' Q σ⁆ = 1 ↔
      conjLinEquiv hQn ⁅x, σ⁆ = 1
    rw [← map_commutatorElement (f := QuotientGroup.mk' Q) (g₁ := x) (g₂ := σ)]
    exact (QuotientGroup.eq_one_iff (⁅x, σ⁆)).trans
      (cSide_conjLinEquiv_eq_one_iff_mem hC ⁅x, σ⁆).symm
  exact hL.trans hR.symm

theorem cSide_swapCent_iff [Finite C] (hC : WeakHyp C Q) (S : CSideSetup C Q) {t₀ : C}
    (ht₀ : t₀ ∉ commutator C) {σ : C} (hσ : σ ∈ commutator C) :
    (∃ l : A5 × A5, S.σ l * conjLinEquiv hQn t₀ * S.σ (S.θ ⟨σ, hσ⟩) =
        S.σ (S.θ ⟨σ, hσ⟩) * (S.σ l * conjLinEquiv hQn t₀)) ↔
      ∃ w : A5WrTwo, w ∉ commutator A5WrTwo ∧
        w * A5WrTwo.baseEmb (S.θ ⟨σ, hσ⟩) = A5WrTwo.baseEmb (S.θ ⟨σ, hσ⟩) * w := by
  classical
  haveI : Finite Q := hC.plus.finite
  have hQL : Q ≤ commutator C := hC.le_commutator
  have hcomm_e : ∀ u : C, S.e (u : C ⧸ Q) ∈ commutator A5WrTwo ↔ u ∈ commutator C := by
    intro u
    have hmap : (commutator (C ⧸ Q)).map S.e.toMonoidHom = commutator A5WrTwo := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ S.e.surjective]
    rw [← hmap]
    change S.e.toMonoidHom (u : C ⧸ Q) ∈ (commutator (C ⧸ Q)).map S.e.toMonoidHom ↔
      u ∈ commutator C
    rw [Subgroup.mem_map_iff_mem S.e.injective]
    exact ⟨fun h => mem_commutator_of_mk_mem hQL h, fun h => mk_mem_commutator_of_mem h⟩
  have hρσ : conjLinEquiv hQn σ = S.σ (S.θ ⟨σ, hσ⟩) := (S.sigma_eq ⟨σ, hσ⟩).symm
  constructor
  · rintro ⟨l, hl⟩
    obtain ⟨l', hl'⟩ := S.surj l
    let x : C := (l' : C) * t₀
    have hxρ : conjLinEquiv hQn x = S.σ l * conjLinEquiv hQn t₀ := by
      change conjLinEquiv hQn ((l' : C) * t₀) = S.σ l * conjLinEquiv hQn t₀
      rw [map_mul, ← S.sigma_eq l', hl']
    have hrel : conjLinEquiv hQn x * conjLinEquiv hQn σ
        = conjLinEquiv hQn σ * conjLinEquiv hQn x := by
      rw [hxρ, hρσ]
      exact hl
    have hcommq := (cSide_conjLinEquiv_comm_iff hC x σ).1 hrel
    have hxnot : x ∉ commutator C := by
      intro hx
      apply ht₀
      have h : t₀ = (l' : C)⁻¹ * x := by
        rw [show x = (l' : C) * t₀ from rfl]; group
      rw [h]
      exact mul_mem ((commutator C).inv_mem l'.2) hx
    refine ⟨S.e (x : C ⧸ Q), ?_, ?_⟩
    · intro hw
      exact hxnot ((hcomm_e x).1 hw)
    · calc S.e (x : C ⧸ Q) * A5WrTwo.baseEmb (S.θ ⟨σ, hσ⟩)
          = S.e (x : C ⧸ Q) * S.e (σ : C ⧸ Q) := by
            rw [← S.emb ⟨σ, hσ⟩]
        _ = S.e ((x : C ⧸ Q) * (σ : C ⧸ Q)) := by rw [map_mul]
        _ = S.e ((σ : C ⧸ Q) * (x : C ⧸ Q)) := by rw [hcommq]
        _ = S.e (σ : C ⧸ Q) * S.e (x : C ⧸ Q) := by rw [map_mul]
        _ = A5WrTwo.baseEmb (S.θ ⟨σ, hσ⟩) * S.e (x : C ⧸ Q) := by
            rw [← S.emb ⟨σ, hσ⟩]
  · rintro ⟨w, hw, hwcomm⟩
    obtain ⟨y, hy⟩ := S.e.surjective w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hxnot : x ∉ commutator C := by
      intro hx
      exact hw (hy ▸ (hcomm_e x).2 hx)
    have hl' : x * t₀⁻¹ ∈ commutator C := by
      rw [Subgroup.mul_mem_iff_of_index_two (H := commutator C) hC.index_commutator]
      exact ⟨fun hx' => absurd hx' hxnot,
        fun hti => absurd ((commutator C).inv_mem_iff.1 hti) ht₀⟩
    let l' : ↥(commutator C) := ⟨x * t₀⁻¹, hl'⟩
    have hcommq : (x : C ⧸ Q) * (σ : C ⧸ Q) = (σ : C ⧸ Q) * (x : C ⧸ Q) := by
      apply S.e.injective
      rw [map_mul, map_mul, hy, ← S.emb ⟨σ, hσ⟩]
      exact hwcomm
    have hρcomm := (cSide_conjLinEquiv_comm_iff hC x σ).2 hcommq
    have hxρ : conjLinEquiv hQn x = S.σ (S.θ l') * conjLinEquiv hQn t₀ := by
      have hxdecomp : x = (x * t₀⁻¹) * t₀ := by group
      rw [hxdecomp, map_mul, ← S.sigma_eq l']
    refine ⟨S.θ l', ?_⟩
    rw [← hxρ, ← hρσ]
    exact hρcomm

end CFSG.EvenSporadicStandard.HNRecog.CSide
