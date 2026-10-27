module

public import CFSG.GH74.GLS.Bg.TwoGroups.A44Phi
public import CFSG.GH74.GLS.Bg.TwoGroups.A44Dict
public import CFSG.GH74.GLS.Bg.TwoGroups.Free2

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

open Subgroup

open A44

theorem mem_commB_iff {B : Type} [CommGroup B] (e : B ≃* Z4Z4) (φ : MulAut B) (b : B) :
    b ∈ commB B φ ↔ ∃ w : ZMod 4 × ZMod 4, vec e b = (phiB e φ).1.act w - w := by
  constructor
  · intro hb
    unfold commB at hb
    induction hb using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨b', rfl⟩ := hx
      exact ⟨vec e b', vec_quot e φ b'⟩
    | one => exact ⟨0, by rw [vec_one, M4.act_zero, sub_zero]⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨w, hw⟩ := ihx
      obtain ⟨w', hw'⟩ := ihy
      refine ⟨w + w', ?_⟩
      rw [vec_mul, hw, hw', M4.act_add]
      abel
    | inv x _ ih =>
      obtain ⟨w, hw⟩ := ih
      refine ⟨-w, ?_⟩
      rw [vec_inv, hw, M4.act_neg]
      abel
  · rintro ⟨w, hw⟩
    obtain ⟨b', rfl⟩ := vec_surjective e w
    have h1 : b'⁻¹ * φ b' ∈ commB B φ := Subgroup.subset_closure ⟨b', rfl⟩
    have h2 : b = b'⁻¹ * φ b' := by
      apply vec_injective e
      rw [hw, vec_quot]
    rw [h2]; exact h1

theorem isPhi_iff {B : Type} [CommGroup B] (e : B ≃* Z4Z4) {z : B} (hz : z ∈ ZB B)
    (φ : MulAut B) : IsPhi B z φ ↔ M4.IsPhiM (phiB e φ).1 (vec e z) := by
  have hz2 : z * z = 1 := by
    have := (mem_ZB B).mp hz
    rwa [pow_two] at this
  have hzp : ∀ b : B, b ∈ zpowers z ↔ vec e b = 0 ∨ vec e b = vec e z := by
    intro b
    constructor
    · intro hb
      rcases zpowers_of_sq_eq_one z hz2 b hb with h | h
      · left; rw [h]; exact vec_one e
      · right; rw [h]
    · rintro (h | h)
      · rw [(vec_eq_zero_iff e b).mp h]; exact one_mem _
      · rw [vec_injective e h]; exact mem_zpowers z
  unfold IsPhi
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun u => ?_, fun v => ?_⟩
    · obtain ⟨b, rfl⟩ := vec_surjective e u
      rw [← hzp, ← h1, mem_commB_iff]
    · obtain ⟨b, rfl⟩ := vec_surjective e v
      have := h2 b
      rw [mem_CB_iff, hzp, vec_pow_two] at this
      exact this
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun b => ?_⟩
    · ext b
      rw [mem_commB_iff, hzp]
      exact h1 (vec e b)
    · rw [mem_CB_iff, hzp, vec_pow_two]
      exact h2 (vec e b)

theorem iv2_2_1_e : IV2_2_1_e := by
  intro B _ ⟨e⟩ z hz hz1
  have hvz0 : vec e z ≠ 0 := fun h => hz1 ((vec_eq_zero_iff e z).mp h)
  have hvz2 : vec e z + vec e z = 0 := (mem_ZB_iff e z).mp hz
  obtain ⟨hinv, hspec⟩ := M4.phiOf_spec (vec e z) hvz0 hvz2
  refine ⟨(phiB e).symm (G96.mk (M4.phiOf (vec e z)) hinv), ?_, ?_⟩
  · show IsPhi B z _
    rw [isPhi_iff e hz, MulEquiv.apply_symm_apply]
    exact hspec
  · intro φ' hφ'
    have hφ'' : IsPhi B z φ' := hφ'
    rw [isPhi_iff e hz] at hφ''
    have := M4.phiOf_unique (vec e z) hvz0 hvz2 _ (phiB e φ').2 hφ''
    apply (phiB e).injective
    apply Subtype.ext
    rw [MulEquiv.apply_symm_apply]
    exact this

end CFSG.GH74.GLS.Bg.TwoGroups
