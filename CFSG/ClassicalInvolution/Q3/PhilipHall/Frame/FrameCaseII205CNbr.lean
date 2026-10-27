module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205Defs
public import CFSG.ClassicalInvolution.Q3.Q3T6DExact

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D


theorem frameANbr_mem_cover (h : FrameAInvConj) {G : Type} [Group G] [Finite G] [FrameCore G]
    {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}
    (d : Std20Frame K K' J S R R' W V z t) {ρ : G} (hρt : ρ * t * ρ⁻¹ = z)
    {B M : Subgroup G} (hB : B = K ∨ B = K') (hadj : aGraphAdj (CoreAssembly.conjClass K) B M) :
    ∃ w ∈ sec20X (CoreAssembly.conjClass K) z K K' ⊔
        conjSub ρ⁻¹ (sec20X (CoreAssembly.conjClass K) z K K') ⊔ Subgroup.zpowers ρ,
      M = conjSub w K ∨ M = conjSub w K' := by
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hXdef
  set Y := X ⊔ conjSub ρ⁻¹ X ⊔ Subgroup.zpowers ρ with hYdef
  have hXY : X ≤ Y := le_trans le_sup_left le_sup_left
  have hρY : Subgroup.zpowers ρ ≤ Y := le_sup_right
  have hρ'Y : ρ⁻¹ ∈ Y := hρY (Subgroup.inv_mem _ (Subgroup.mem_zpowers ρ))
  have hK'z : IsUniqueInvolution K' z := d.late_hzK'
  have key : ∀ (M : Subgroup G) (s : G), M ∈ CoreAssembly.conjClass K →
      IsUniqueInvolution M s →
      ((∃ zK, AViol (CoreAssembly.conjClass K) K M zK s) ∨
        (∃ zK, AViol (CoreAssembly.conjClass K) K' M zK s)) →
      ∃ w ∈ Y, M = conjSub w K ∨ M = conjSub w K' := by
    intro M s hMΩ hMs hA
    obtain ⟨x, hx, hxs⟩ := h G K K' J S R R' W V z t d M s hA
    have e : ρ * x⁻¹ * s * (ρ * x⁻¹)⁻¹ = z := by
      rw [← hxs]
      calc ρ * x⁻¹ * (x * t * x⁻¹) * (ρ * x⁻¹)⁻¹ = ρ * t * ρ⁻¹ := by group
        _ = z := hρt
    have hQi : IsUniqueInvolution (conjSub (ρ * x⁻¹) M) z := by
      have h1 := hMs.conj (ρ * x⁻¹)
      rwa [e] at h1
    have hQ : conjSub (ρ * x⁻¹) M ∈ twinSet (CoreAssembly.conjClass K) K :=
      ⟨d.hyp.conjInvariant (ρ * x⁻¹) M hMΩ, z, d.viol.hzK, hQi⟩
    rw [d.twins] at hQ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hQ
    have hM' : M = conjSub (x * ρ⁻¹) (conjSub (ρ * x⁻¹) M) := by
      rw [← conjSub_mul]
      have e' : x * ρ⁻¹ * (ρ * x⁻¹) = 1 := by group
      rw [e', conjSub_one]
    refine ⟨x * ρ⁻¹, Subgroup.mul_mem Y (hXY hx) hρ'Y, ?_⟩
    rcases hQ with h1 | h1
    · exact Or.inl (hM'.trans (congrArg (conjSub (x * ρ⁻¹)) h1))
    · exact Or.inr (hM'.trans (congrArg (conjSub (x * ρ⁻¹)) h1))
  have hAK : ∀ M : Subgroup G, aGraphAdj (CoreAssembly.conjClass K) K M →
      ∃ w ∈ Y, M = conjSub w K ∨ M = conjSub w K' := by
    intro M hadj
    obtain ⟨hMΩ, h' | h' | ⟨ht, hne⟩⟩ := hadj
    · obtain ⟨zK, s, hv⟩ := h'
      exact key M s hMΩ hv.hzJ (Or.inl ⟨zK, hv⟩)
    · obtain ⟨zM, zK, hv⟩ := h'
      exact key M zM hMΩ hv.hzK (Or.inl ⟨zK, aviol_symmGen d.hyp hMΩ hv⟩)
    · have ht2 := ht
      rw [d.twins] at ht2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht2
      rcases ht2 with h1 | h1
      · exact absurd h1 hne
      · exact ⟨1, Subgroup.one_mem Y, by simp only [conjSub_one]; exact Or.inr h1⟩
  have hAK' : ∀ M : Subgroup G, aGraphAdj (CoreAssembly.conjClass K) K' M →
      ∃ w ∈ Y, M = conjSub w K ∨ M = conjSub w K' := by
    intro M hadj
    obtain ⟨hMΩ, h' | h' | ⟨ht, -⟩⟩ := hadj
    · obtain ⟨zK, s, hv⟩ := h'
      exact key M s hMΩ hv.hzJ (Or.inr ⟨zK, hv⟩)
    · obtain ⟨zM, zK, hv⟩ := h'
      exact key M zM hMΩ hv.hzK (Or.inr ⟨zK, aviol_symmGen d.hyp hMΩ hv⟩)
    · obtain ⟨-, z', hz'K', hz'M⟩ := ht
      have hzz : z = z' := hK'z.eq hz'K'
      rw [← hzz] at hz'M
      have hMtw : M ∈ twinSet (CoreAssembly.conjClass K) K := ⟨hMΩ, z, d.viol.hzK, hz'M⟩
      rw [d.twins] at hMtw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hMtw
      exact ⟨1, Subgroup.one_mem Y, by simp only [conjSub_one]; exact hMtw⟩
  rcases hB with hB | hB
  · rw [hB] at hadj
    exact hAK M hadj
  · rw [hB] at hadj
    exact hAK' M hadj

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
