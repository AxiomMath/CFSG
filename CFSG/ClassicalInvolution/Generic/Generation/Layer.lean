module

public import CFSG.ClassicalInvolution.Generic.Generation.Toral

public section

namespace CFSG.ClassicalInvolution.Generic

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_mul_of_central {H : Subgroup G} {a b z w : G} (hw : w ∈ H)
    (ha : a ∈ H) (hb : b ∈ H) (hzc : ∀ h ∈ H, z * h = h * z) (hwc : ∀ h ∈ H, w * h = h * w) :
    ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz2 : Commute z b := hzc b hb
  have hz3 : Commute z w := hzc w hw
  have hw1 : Commute w a := hwc a ha
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
      = a * (z * b * w * z⁻¹) * a⁻¹ * (w⁻¹ * b⁻¹) := by group
    _ = a * (b * w) * a⁻¹ * (w⁻¹ * b⁻¹) := by
        rw [show z * b * w * z⁻¹ = b * w by
          rw [hz2.eq, mul_assoc, mul_assoc, ← mul_assoc z w, hz3.eq, mul_assoc w z,
            mul_inv_cancel, mul_one]]
    _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by
        rw [show w * a⁻¹ * w⁻¹ = a⁻¹ by
          rw [hw1.inv_right.eq, mul_assoc, mul_inv_cancel, mul_one]]

theorem exists_mul_of_mem_sup_central {H A Z : Subgroup G} (hAH : A ≤ H)
    (hZc : ∀ z ∈ Z, ∀ h ∈ H, z * h = h * z) {g : G} (hg : g ∈ A ⊔ Z) :
    ∃ a ∈ A, ∃ z ∈ Z, g = a * z := by
  rw [Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, Z.one_mem, (mul_one x).symm⟩
    · exact ⟨1, A.one_mem, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, A.one_mem, 1, Z.one_mem, (mul_one 1).symm⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨a, ha, z, hz, rfl⟩ := ihx
    obtain ⟨b, hb, w, hw, rfl⟩ := ihy
    refine ⟨a * b, A.mul_mem ha hb, z * w, Z.mul_mem hz hw, ?_⟩
    have h : z * b = b * z := hZc z hz b (hAH hb)
    calc a * z * (b * w) = a * (z * b) * w := by group
      _ = a * (b * z) * w := by rw [h]
      _ = a * b * (z * w) := by group
  | inv x hx ihx =>
    obtain ⟨a, ha, z, hz, rfl⟩ := ihx
    refine ⟨a⁻¹, A.inv_mem ha, z⁻¹, Z.inv_mem hz, ?_⟩
    have h : Commute z a := hZc z hz a (hAH ha)
    rw [mul_inv_rev]
    exact h.inv_inv.eq

theorem le_of_perfect_of_le_sup_central {H A Z : Subgroup G} (hAH : A ≤ H) (hZH : Z ≤ H)
    (hZc : ∀ z ∈ Z, ∀ h ∈ H, z * h = h * z) (hperf : H ≤ ⁅H, H⁆) (hHAZ : H ≤ A ⊔ Z) :
    H ≤ A := by
  refine hperf.trans (Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_)
  obtain ⟨a, ha, z, hz, rfl⟩ := exists_mul_of_mem_sup_central hAH hZc (hHAZ hg₁)
  obtain ⟨b, hb, w, hw, rfl⟩ := exists_mul_of_mem_sup_central hAH hZc (hHAZ hg₂)
  rw [commutator_mul_of_central (hZH hw) (hAH ha) (hAH hb) (hZc z hz) (hZc w hw)]
  rw [commutatorElement_def]
  exact A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)

theorem centLayer_perfect {Ω : Set (Subgroup G)} (hperf : ∀ L ∈ Ω, ⁅L, L⁆ = L) (a : G) :
    centLayer Ω a ≤ ⁅centLayer Ω a, centLayer Ω a⁆ :=
  centLayer_le fun L hL => by
    have h := Subgroup.commutator_mono (le_centLayer hL) (le_centLayer hL)
    rwa [hperf L hL.1] at h

@[expose] def FrameGenerationModCenter (Ω : Set (Subgroup G)) (E : Subgroup G)
    (S : Set (Subgroup G)) : Prop :=
  ∀ x ∈ E, x ≠ 1 → ∃ Z : Subgroup G, Z ≤ centLayer Ω x ∧
    (∀ z ∈ Z, ∀ y ∈ centLayer Ω x, z * y = y * z) ∧
    centLayer Ω x ≤ (⨆ K ∈ {K | K ∈ S ∧ K ≤ Subgroup.centralizer ({x} : Set G)}, K) ⊔ Z

theorem FrameGenerationModCenter.frameGeneration {Ω : Set (Subgroup G)} {E : Subgroup G}
    {S : Set (Subgroup G)} (hperf : ∀ L ∈ Ω, ⁅L, L⁆ = L) (hS : S ⊆ Ω)
    (h : FrameGenerationModCenter Ω E S) : FrameGeneration Ω E S := by
  intro x hx hx1
  obtain ⟨Z, hZH, hZc, hHAZ⟩ := h x hx hx1
  refine le_of_perfect_of_le_sup_central ?_ hZH hZc (centLayer_perfect hperf x) hHAZ
  exact iSup₂_le fun K hK => le_centLayer ⟨hS hK.1, hK.2⟩

end CFSG.ClassicalInvolution.Generic
