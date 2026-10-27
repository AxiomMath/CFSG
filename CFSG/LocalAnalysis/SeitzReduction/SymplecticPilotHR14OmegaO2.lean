module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaPlane

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open scoped commutatorElement

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def omegaEichlerGroup (Q : QuadraticForm K V) (W : Submodule K V) :
    Subgroup (V ≃ₗ[K] V) :=
  Subgroup.closure {g | ∃ u ∈ W, ∃ w ∈ W, eichler Q u w = g}

theorem eichler_mem_omegaEichlerGroup {W : Submodule K V} {u w : V} (hu : u ∈ W) (hw : w ∈ W) :
    eichler Q u w ∈ omegaEichlerGroup Q W :=
  Subgroup.subset_closure ⟨u, hu, w, hw, rfl⟩

theorem eq_one_of_omegaInvNil_eq_zero {s : V ≃ₗ[K] V} (h : ∀ x, omegaInvNil s x = 0) : s = 1 :=
  LinearEquiv.ext fun x => omegaInvNil_eq_zero_iff_apply.1 (h x)

theorem mem_closure_odd_centralizer_omega {s : V ≃ₗ[K] V}
    (hsΩ : s ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (h : s ∈ omegaO2Cent Q s) :
    (⟨s, hsΩ⟩ : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆) ∈
      Subgroup.closure {x | x ∈ Subgroup.centralizer {⟨s, hsΩ⟩} ∧ Odd (orderOf x)} := by
  set Ω := ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆
  set H : Subgroup Ω := Subgroup.closure {x | x ∈ Subgroup.centralizer {⟨s, hsΩ⟩} ∧
    Odd (orderOf x)}
  have hle : omegaO2Cent Q s ≤ H.map Ω.subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxΩ, hxs, hxo⟩
    refine ⟨⟨x, hxΩ⟩, Subgroup.subset_closure ⟨?_, ?_⟩, rfl⟩
    · rw [Subgroup.mem_centralizer_singleton_iff] at hxs ⊢
      exact Subtype.ext hxs
    · rwa [← Subgroup.orderOf_coe]
  obtain ⟨y, hy, hys⟩ := hle h
  have : y = ⟨s, hsΩ⟩ := Subtype.ext hys
  rwa [← this]

end CFSG.SeitzReduction.SymplecticPilot
