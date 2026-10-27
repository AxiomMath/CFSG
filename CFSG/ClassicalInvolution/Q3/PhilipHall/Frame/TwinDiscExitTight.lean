module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Q8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.TL4

namespace TwinDisc

namespace ExitE4

theorem not_dEdgeless_top {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} {K : Subgroup X}
    (h2K : IsPGroup 2 ↥K) (hΦ : Φ = CoreAssembly.conjClass K) {K₀ J : Subgroup X}
    (hK₀ : K₀ ∈ Φ) (hJ : J ∈ omegaNbr Φ K₀) :
    ¬ DEdgeless (CoreAssembly.conjClass (K.subgroupOf (⊤ : Subgroup X))) := by
  subst hΦ
  intro hE
  have h2R : IsPGroup 2 ↥(K.subgroupOf (⊤ : Subgroup X)) := h2K.comap_subtype
  obtain ⟨hJΦ, hJne, hJle⟩ := (Vtx.mem_omegaNbr_conjClass_iff h2K).mp hJ
  obtain ⟨g₀, rfl⟩ := hK₀
  obtain ⟨gJ, rfl⟩ := hJΦ
  have hA : (conjSub g₀ K).subgroupOf (⊤ : Subgroup X) ∈
      CoreAssembly.conjClass (K.subgroupOf (⊤ : Subgroup X)) :=
    ⟨⟨g₀, Subgroup.mem_top g₀⟩, conjSub_subgroupOf _ _ _⟩
  have hB : (conjSub gJ K).subgroupOf (⊤ : Subgroup X) ∈
      CoreAssembly.conjClass (K.subgroupOf (⊤ : Subgroup X)) :=
    ⟨⟨gJ, Subgroup.mem_top gJ⟩, conjSub_subgroupOf _ _ _⟩
  refine hE _ hA _ hB (Or.inl ?_)
  refine (Vtx.mem_omegaNbr_conjClass_iff h2R).mpr ⟨hB, ?_, ?_⟩
  · intro e
    apply hJne
    have := congrArg (Subgroup.map (⊤ : Subgroup X).subtype) e
    rwa [Subgroup.map_subgroupOf_eq_of_le le_top, Subgroup.map_subgroupOf_eq_of_le le_top] at this
  · intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro a
    have hy' : (y : X) ∈ conjSub gJ K := hy
    have := Subgroup.mem_normalizer_iff.mp (hJle hy') (a : X)
    exact this

end ExitE4

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
