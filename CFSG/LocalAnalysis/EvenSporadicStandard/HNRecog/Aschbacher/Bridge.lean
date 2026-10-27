module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.BaseEmb
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Extraspecial.InvariantSubgroups

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.RankThree.Literature.FSmith

variable {C : Type} [Group C] {Q : Subgroup C} [hQn : Q.Normal]
  [Module (ZMod 2) (Additive (Abelianization Q))]

theorem AschbacherHyp.exists_hom_baseEmb [Finite C] (hC : AschbacherHyp C Q) :
    ∃ (e : C ⧸ Q ≃* A5WrTwo)
      (θ : ↥(commutator C) →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5))
      (σ : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →*
        (Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q))),
      Function.Surjective θ ∧ (∀ l : ↥(commutator C), θ l = 1 ↔ (l : C) ∈ Q) ∧
      (∀ l : ↥(commutator C), A5WrTwo.baseEmb (θ l) = e (QuotientGroup.mk (l : C))) ∧
      (∀ l : ↥(commutator C), σ (θ l) = conjLinEquiv hQn (l : C)) ∧ Function.Injective σ ∧
      (∀ U : Submodule (ZMod 2) (Additive (Abelianization Q)),
        (∀ g : alternatingGroup (Fin 5) × alternatingGroup (Fin 5), ∀ u ∈ U, σ g u ∈ U) →
          U = ⊥ ∨ U = ⊤) := by
  classical
  haveI : Finite Q := hC.plus.finite
  have hE : IsExtraspecialPGroup 2 Q := hC.plus.isExtraspecialPGroup
  let e : C ⧸ Q ≃* A5WrTwo := hC.quotient.some
  let Φ : C →* A5WrTwo := (e : C ⧸ Q →* A5WrTwo).comp (QuotientGroup.mk' Q)
  have hΦsurj : Function.Surjective Φ :=
    e.surjective.comp (QuotientGroup.mk'_surjective Q)
  have hmap : (commutator C).map Φ = A5WrTwo.baseEmb.range := by
    rw [A5WrTwo.range_baseEmb, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective Φ hΦsurj]
    rfl
  have hΦ_eq_one : ∀ g : C, Φ g = 1 ↔ g ∈ Q := by
    intro g
    change e (QuotientGroup.mk' Q g) = 1 ↔ g ∈ Q
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff g
  let θ₀ : ↥(commutator C) →* A5WrTwo.baseEmb.range :=
    (Φ.comp (commutator C).subtype).codRestrict A5WrTwo.baseEmb.range (fun l => by
      have hmem : Φ (l : C) ∈ (commutator C).map Φ := Subgroup.mem_map_of_mem Φ l.2
      rwa [hmap] at hmem)
  let θ : ↥(commutator C) →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5) :=
    ((MonoidHom.ofInjective A5WrTwo.baseEmb_injective).symm :
      A5WrTwo.baseEmb.range →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5)).comp θ₀
  have hθ_base : ∀ l : ↥(commutator C), A5WrTwo.baseEmb (θ l) = Φ (l : C) := by
    intro l
    change A5WrTwo.baseEmb
      ((MonoidHom.ofInjective A5WrTwo.baseEmb_injective).symm (θ₀ l)) = Φ (l : C)
    rw [MonoidHom.apply_ofInjective_symm]
    rfl
  have hθsurj : Function.Surjective θ := by
    intro g
    have hmem : A5WrTwo.baseEmb g ∈ (commutator C).map Φ := by
      rw [hmap]
      exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
    obtain ⟨l, hl, hlg⟩ := Subgroup.mem_map.mp hmem
    refine ⟨⟨l, hl⟩, ?_⟩
    apply A5WrTwo.baseEmb_injective
    rw [hθ_base]
    exact hlg
  have hθker : ∀ l : ↥(commutator C), θ l = 1 ↔ (l : C) ∈ Q := by
    intro l
    rw [← A5WrTwo.baseEmb_injective.eq_iff, hθ_base, map_one]
    exact hΦ_eq_one (l : C)
  let ρL : ↥(commutator C) →* (Additive (Abelianization Q) ≃ₗ[ZMod 2]
      Additive (Abelianization Q)) := (conjLinEquiv hQn).comp (commutator C).subtype
  have hker : θ.ker ≤ ρL.ker := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl ⊢
    exact conjLinEquiv_eq_one_of_mem ((hθker l).1 hl)
  let σ : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →*
      (Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q)) :=
    MonoidHom.liftOfRightInverse θ (Function.surjInv hθsurj)
      (Function.rightInverse_surjInv hθsurj) ⟨ρL, hker⟩
  have hσ_apply : ∀ l : ↥(commutator C), σ (θ l) = ρL l := by
    intro l
    exact MonoidHom.liftOfRightInverse_comp_apply (f := θ)
      (f_inv := Function.surjInv hθsurj) (hf := Function.rightInverse_surjInv hθsurj)
      (g := ⟨ρL, hker⟩) (x := l)
  have hσinj : Function.Injective σ := by
    intro x y hxy
    obtain ⟨lx, rfl⟩ := hθsurj x
    obtain ⟨ly, rfl⟩ := hθsurj y
    rw [hσ_apply lx, hσ_apply ly] at hxy
    have hcli : conjLinEquiv hQn ((lx : C) * (ly : C)⁻¹) = 1 := by
      have h1 : ρL (lx * ly⁻¹) = 1 := by
        rw [map_mul, map_inv, hxy, mul_inv_cancel]
      exact h1
    have hker1 : (lx : C) * (ly : C)⁻¹ ∈ Q := by
      rw [← ker_extraspecialConjOrth hE hC.centralizer_le, MonoidHom.mem_ker]
      apply Subtype.ext
      show conjLinEquiv hQn ((lx : C) * (ly : C)⁻¹) = 1
      exact hcli
    have htheta : θ (lx * ly⁻¹) = 1 := (hθker (lx * ly⁻¹)).2 (by simpa using hker1)
    have h2 : θ lx * (θ ly)⁻¹ = 1 := by
      rw [← map_inv, ← map_mul, htheta]
    exact mul_inv_eq_one.mp h2
  refine ⟨e, θ, σ, hθsurj, hθker, ?_, ?_, hσinj, ?_⟩
  · intro l
    exact hθ_base l
  · intro l
    exact hσ_apply l
  · intro U hU
    refine (forall_invariant_subgroup_iff_of_subgroup (Q := Q) hE (commutator C)).1
      hC.irreducible U ?_
    intro g hg u hu
    have hgu : σ (θ ⟨g, hg⟩) u ∈ U := hU (θ ⟨g, hg⟩) u hu
    rw [hσ_apply] at hgu
    exact hgu

theorem AschbacherHyp.exists_hom [Finite C] (hC : AschbacherHyp C Q) :
    ∃ (θ : ↥(commutator C) →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5))
      (σ : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →*
        (Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q))),
      Function.Surjective θ ∧ (∀ l : ↥(commutator C), θ l = 1 ↔ (l : C) ∈ Q) ∧
      (∀ l : ↥(commutator C), σ (θ l) = conjLinEquiv hQn (l : C)) ∧ Function.Injective σ ∧
      (∀ U : Submodule (ZMod 2) (Additive (Abelianization Q)),
        (∀ g : alternatingGroup (Fin 5) × alternatingGroup (Fin 5), ∀ u ∈ U, σ g u ∈ U) →
          U = ⊥ ∨ U = ⊤) := by
  obtain ⟨-, θ, σ, h1, h2, -, h3, h4, h5⟩ := hC.exists_hom_baseEmb
  exact ⟨θ, σ, h1, h2, h3, h4, h5⟩

end CFSG.EvenSporadicStandard.HNRecog
