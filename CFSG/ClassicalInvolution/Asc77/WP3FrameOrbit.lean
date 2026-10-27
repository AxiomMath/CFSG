module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameData
public import CFSG.ClassicalInvolution.Asc77.WP3LayerHyp

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

namespace ChainFrame

variable {G : Type} [Group G]

theorem exists_orbitRep {z t z' : G} (hz : z * z = 1) (ht : t * t = 1) (hz' : z' * z' = 1)
    (hzt : z * t = t * z) (hzz' : z * z' = z' * z) (htz' : t * z' = z' * t)
    (hsymm : ChainFrameSymm z t z') {c : G}
    (hc : c ∈ Subgroup.closure ({z, t, z'} : Set G)) (hc1 : c ≠ 1) :
    ∃ r ∈ ({z, t, z * t} : Set G), ∃ n ∈ Subgroup.normalizer
      ((Subgroup.closure ({z, t, z'} : Set G) : Subgroup G) : Set G), c = n * r * n⁻¹ := by
  have h1 : ∀ r : G, r = (1 : G) * r * (1 : G)⁻¹ := fun r => by group
  obtain ⟨n₁, hn₁, hz₁, ht₁⟩ := hsymm.swap z' (Set.mem_insert _ _)
  obtain ⟨n₂, hn₂, hz₂, ht₂⟩ := hsymm.swap (t * z') (Set.mem_insert_of_mem _ rfl)
  rcases ChainFrame.mem_closure_eight hz ht hz' hzt hzz' htz' hc with
    h | h | h | h | h | h | h | h
  · exact absurd h hc1
  · exact ⟨z, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
  · exact ⟨t, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
  · exact ⟨t, by simp, n₁, hn₁, by rw [h, ← ht₁]⟩
  · exact ⟨z * t, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
  · refine ⟨z * t, by simp, n₁, hn₁, ?_⟩
    calc c = z * z' := h
      _ = (n₁ * z * n₁⁻¹) * (n₁ * t * n₁⁻¹) := by rw [hz₁, ht₁]
      _ = n₁ * (z * t) * n₁⁻¹ := by group
  · exact ⟨t, by simp, n₂, hn₂, by rw [h, ← ht₂]⟩
  · refine ⟨z * t, by simp, n₂, hn₂, ?_⟩
    calc c = z * (t * z') := h
      _ = (n₂ * z * n₂⁻¹) * (n₂ * t * n₂⁻¹) := by rw [hz₂, ht₂]
      _ = n₂ * (z * t) * n₂⁻¹ := by group

end ChainFrame

section Data

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J K' : Subgroup G} {z t z' : G}

theorem ChainFrameData.hyp51_of_vertices (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (h : ChainFrameData Ω K J K' z t z') (hsymm : ChainFrameSymm z t z')
    (hz : Hyp51At (Subgroup.closure ({z, t, z'} : Set G)) z)
    (ht : Hyp51At (Subgroup.closure ({z, t, z'} : Set G)) t)
    (hzt : Hyp51At (Subgroup.closure ({z, t, z'} : Set G)) (z * t)) :
    Hyp51 (Subgroup.closure ({z, t, z'} : Set G)) := by
  refine ExactLayer.hyp51_of_orbitReps (R := ({z, t, z * t} : Set G))
    (h.isElemAbelian hp hΩ) (h.natCard_eight hp hq hΩ) ?_ ?_
  · intro r hr
    rcases hr with rfl | rfl | rfl
    · exact hz
    · exact ht
    · exact hzt
  · intro c hc hc1
    exact ChainFrame.exists_orbitRep h.hz.sq h.ht.sq h.hz'.sq (h.comm_zt hp hΩ)
      (h.comm_zz' hp hΩ) h.htz' hsymm hc hc1

end Data

variable {p f : ℕ} [Fact p.Prime]

theorem chainFrameHyp51_of_vertices (hz : ChainFrameHyp51z (p := p) (f := f))
    (ht : ChainFrameHyp51t (p := p) (f := f)) (hzt : ChainFrameHyp51zt (p := p) (f := f)) :
    ChainFrameHyp51 (p := p) (f := f) := by
  intro G _ _ _ Ω K J K' z t z' hs
  exact hs.frame.hyp51_of_vertices hs.odd hs.five hs.hyp hs.symm (hz G Ω K J K' z t z' hs)
    (ht G Ω K J K' z t z' hs) (hzt G Ω K J K' z t z' hs)

end CFSG.ClassicalInvolution.Asc77
