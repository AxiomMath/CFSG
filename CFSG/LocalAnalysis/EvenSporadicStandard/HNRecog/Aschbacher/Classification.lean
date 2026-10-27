module

public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.Core

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Module QuadraticMap CFSG.GroupTheory.WeirSylow

theorem irreducible_iff_exists_stabilizer_alternatingGroup_five
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (q : QuadraticForm (ZMod 2) V)
    (hnd : q.polarBilin.Nondegenerate) (h8 : finrank (ZMod 2) V = 8) (hplus : IsPlusType q)
    {G : Type} [Group G] (ρ : G →* TauCeti.QuadraticMap.orthogonalGroup q)
    (hρ : Function.Injective ρ)
    (hG : Nonempty (G ≃* alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) :
    (∀ U : Submodule (ZMod 2) V,
        (∀ g : G, ∀ u ∈ U, ((ρ g : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[ZMod 2] V) u ∈ U) →
          U = ⊥ ∨ U = ⊤) ↔
      ∃ v : V, v ≠ 0 ∧ ∃ S : Subgroup G,
        (∀ g, g ∈ S ↔ ((ρ g : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[ZMod 2] V) v = v) ∧
          Nonempty (S ≃* alternatingGroup (Fin 5)) := by
  classical
  obtain ⟨e⟩ := hG
  let σ : Fpf.A5 × Fpf.A5 →* (V ≃ₗ[ZMod 2] V) :=
    ((TauCeti.QuadraticMap.orthogonalGroup q).subtype.comp ρ).comp e.symm.toMonoidHom
  have hσ : Function.Injective σ := by
    intro g1 g2 h
    have h1 : ρ (e.symm g1) = ρ (e.symm g2) := Subtype.val_injective h
    exact e.symm.injective (hρ h1)
  have hσ_apply : ∀ g' : Fpf.A5 × Fpf.A5,
      σ g' = ((ρ (e.symm g') : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[ZMod 2] V) :=
    fun _ => rfl
  have hσ_eq : ∀ g : G,
      σ (e g) = ((ρ g : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[ZMod 2] V) := by
    intro g
    rw [hσ_apply, MulEquiv.symm_apply_apply]
  have hinv :
      (∀ U : Submodule (ZMod 2) V,
          (∀ g : G, ∀ u ∈ U,
            ((ρ g : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[ZMod 2] V) u ∈ U) →
            U = ⊥ ∨ U = ⊤) ↔
        (∀ U : Submodule (ZMod 2) V,
          (∀ g' : Fpf.A5 × Fpf.A5, ∀ u ∈ U, σ g' u ∈ U) → U = ⊥ ∨ U = ⊤) := by
    constructor
    · intro h U hU
      apply h U
      intro g u hu
      have hgu : σ (e g) u ∈ U := hU (e g) u hu
      rwa [hσ_eq g] at hgu
    · intro h U hU
      apply h U
      intro g' u hu
      have hgu : ((ρ (e.symm g') : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[ZMod 2] V) u ∈ U :=
        hU (e.symm g') u hu
      rwa [← hσ_apply g'] at hgu
  have hex :
      (∃ v : V, v ≠ 0 ∧ ∃ S : Subgroup G,
          (∀ g, g ∈ S ↔ ((ρ g : TauCeti.QuadraticMap.orthogonalGroup q) : V ≃ₗ[ZMod 2] V) v = v) ∧
            Nonempty (S ≃* alternatingGroup (Fin 5))) ↔
        (∃ v : V, v ≠ 0 ∧ ∃ S : Subgroup (Fpf.A5 × Fpf.A5),
            (∀ g', g' ∈ S ↔ σ g' v = v) ∧ Nonempty (S ≃* Fpf.A5)) := by
    constructor
    · rintro ⟨v, hv, S, hS, ⟨iso⟩⟩
      refine ⟨v, hv, S.map e.toMonoidHom, ?_, ?_⟩
      · intro g'
        rw [Subgroup.mem_map_equiv, hS (e.symm g'), hσ_apply g']
      · exact ⟨(MulEquiv.subgroupMap e S).symm.trans iso⟩
    · rintro ⟨v, hv, S', hS', ⟨iso⟩⟩
      refine ⟨v, hv, S'.map e.symm.toMonoidHom, ?_, ?_⟩
      · intro g
        rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, hS' (e g), hσ_eq g]
      · exact ⟨(MulEquiv.subgroupMap e.symm S').symm.trans iso⟩
  exact hinv.trans ((Fpf.irreducible_iff_exists_stabilizer σ hσ h8).trans hex.symm)

end CFSG.EvenSporadicStandard.HNRecog
