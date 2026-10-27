module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionStated
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionOrbits

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointAction

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open scoped Classical

universe u v w w'

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)
variable {G : Type w} [Group G] {D : Type w'} [Group D]

@[expose] noncomputable def actionStabilizer (ρ : G →* Equiv.Perm (Points Q))
    (L : Points Q) : Subgroup G :=
  letI := MulAction.compHom (Points Q) ρ
  MulAction.stabilizer G L

@[expose] noncomputable def actionStabilizerOrbit (ρ : G →* Equiv.Perm (Points Q))
    (L M : Points Q) : Set (Points Q) :=
  letI := MulAction.compHom (Points Q) ρ
  MulAction.orbit (actionStabilizer Q ρ L) M

@[expose] noncomputable def actionStabilizerFamily (ρ : G →* Equiv.Perm (Points Q)) :
    Set (Subgroup G) := Set.range (actionStabilizer Q ρ)

theorem mem_actionStabilizerOrbit (ρ : G →* Equiv.Perm (Points Q))
    (L M N : Points Q) : N ∈ actionStabilizerOrbit Q ρ L M ↔
      ∃ g : G, ρ g L = L ∧ ρ g M = N := by
  let := MulAction.compHom (Points Q) ρ
  change N ∈ MulAction.orbit (actionStabilizer Q ρ L) M ↔ _
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.val, g.property, hg⟩
  · rintro ⟨g, hL, hM⟩
    exact ⟨⟨g, hL⟩, hM⟩

@[expose] def ActionProperties (ρ : G →* Equiv.Perm (Points Q)) : Prop :=
  letI := MulAction.compHom (Points Q) ρ
  Nonempty (Points Q) ∧ Nontrivial (Points Q) ∧ Nontrivial G ∧
    FaithfulSMul G (Points Q) ∧ MulAction.IsPreprimitive G (Points Q) ∧
    Function.Injective (actionStabilizer Q ρ) ∧
    (∀ L M : Points Q, actionStabilizerOrbit Q ρ L M =
      if M = L then {L} else if PointPerp L M then perpendicularPoints Q L
      else nonperpendicularPoints Q L) ∧
    ∀ L : Points Q,
      (∃ M N : Points Q, M ≠ N ∧ M ∈ perpendicularPoints Q L ∧
        N ∈ perpendicularPoints Q L) ∧
      (∃ M N : Points Q, M ≠ N ∧ M ∈ nonperpendicularPoints Q L ∧
        N ∈ nonperpendicularPoints Q L)

theorem actionStabilizer_comap (ρ : G →* Equiv.Perm (Points Q))
    (τ : D →* Equiv.Perm (Points Q)) (e : G ≃* D)
    (h : ∀ g : G, ρ g = τ (e g)) (L : Points Q) :
    (actionStabilizer Q τ L).comap e.toMonoidHom = actionStabilizer Q ρ L := by
  ext g
  change τ (e g) L = L ↔ ρ g L = L
  rw [h]

theorem actionStabilizerOrbit_equiv (ρ : G →* Equiv.Perm (Points Q))
    (τ : D →* Equiv.Perm (Points Q)) (e : G ≃* D)
    (h : ∀ g : G, ρ g = τ (e g)) (L M : Points Q) :
    actionStabilizerOrbit Q ρ L M = actionStabilizerOrbit Q τ L M := by
  ext N
  rw [mem_actionStabilizerOrbit, mem_actionStabilizerOrbit]
  constructor
  · rintro ⟨g, hL, hM⟩
    rw [h] at hL hM
    exact ⟨e g, hL, hM⟩
  · rintro ⟨g, hL, hM⟩
    refine ⟨e.symm g, ?_, ?_⟩
    · rw [h, e.apply_symm_apply]
      exact hL
    · rw [h, e.apply_symm_apply]
      exact hM

theorem actionProperties_equiv (ρ : G →* Equiv.Perm (Points Q))
    (τ : D →* Equiv.Perm (Points Q)) (e : G ≃* D)
    (h : ∀ g : G, ρ g = τ (e g)) (hτ : ActionProperties Q τ) :
    ActionProperties Q ρ := by
  let := MulAction.compHom (Points Q) τ
  let := MulAction.compHom (Points Q) ρ
  obtain ⟨hΩ, hΩn, hD, hfaith, hprim, hinj, horbits, htwo⟩ := hτ
  let := hD
  let := hfaith
  let := hprim
  have hG : Nontrivial G := e.toEquiv.nontrivial
  have hfaithG : FaithfulSMul G (Points Q) := by
    apply faithfulSMul_iff.mpr
    intro g hg
    apply e.injective
    have he : e g = 1 := (faithfulSMul_iff.mp hfaith) (e g) (by
      intro L
      change τ (e g) L = L
      rw [← h]
      exact hg L)
    simpa using he
  have hprimG : MulAction.IsPreprimitive G (Points Q) := by
    exact MulAction.IsPreprimitive.of_surjective
      (f := (⟨id, by
        intro g L
        change τ g L = ρ (e.symm g) L
        rw [h, e.apply_symm_apply]⟩ : Points Q →ₑ[e.symm] Points Q))
      Function.surjective_id
  refine ⟨hΩ, hΩn, hG, hfaithG, hprimG, ?_, ?_, htwo⟩
  · intro L M hstab
    apply hinj
    ext g
    have hs : e.symm g ∈ actionStabilizer Q ρ L ↔
        e.symm g ∈ actionStabilizer Q ρ M := by rw [hstab]
    change ρ (e.symm g) L = L ↔ ρ (e.symm g) M = M at hs
    rw [h, e.apply_symm_apply] at hs
    exact hs
  · intro L M
    rw [actionStabilizerOrbit_equiv Q ρ τ e h]
    exact horbits L M

theorem projective_action_properties [FiniteDimensional K V]
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    ActionProperties Q (projectivePointAction Q) := by
  have h := elementary_projective_action Q hQ hT
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    projectiveStabilizer_injective Q hQ hT, projective_stabilizer_orbit Q hQ hT,
    off_diagonal_points Q hQ hT⟩

section Matrices

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F]
variable {Q : QuadraticForm F (ι → F)} {Q₀ : (ι → F) → F}

theorem stated_action_properties (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule F (ι → F), Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    ActionProperties Q (statedPointAction hQ) :=
  actionProperties_equiv Q _ _ (statedActionEquiv hQ hE)
    (statedPointAction_equiv hQ hE) (projective_action_properties Q hnd hT)

end Matrices

end CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
