module

public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

theorem center_le_mul_of_gen {X : Type} [Group X] {K L Z : Subgroup X} [L.Normal]
    (hZ : Z ≤ Subgroup.center X)
    (hgen : (⨆ g : X, CFSG.ClassicalInvolution.Generic.conjSub g K) = ⊤)
    (hKLZ : ∀ x : X, ∃ k ∈ K, ∃ l ∈ L, ∃ c ∈ Z, x = k * l * c) :
    ∀ c ∈ Z, ∃ k ∈ K, ∃ l ∈ L, c = k * l := by
  have hA : ∀ g : X, ∀ k ∈ K, ∃ k' ∈ K, ∃ l ∈ L, g * k * g⁻¹ = k' * l := by
    intro g k hk
    obtain ⟨k₁, hk₁, l₁, hl₁, c₁, hc₁, rfl⟩ := hKLZ g
    have hcen : c₁ * k = k * c₁ := (Subgroup.mem_center_iff.mp (hZ hc₁) k).symm
    have hcc : c₁ * k * c₁⁻¹ = k := by
      rw [hcen, mul_inv_cancel_right]
    have hm : k⁻¹ * l₁ * k * l₁⁻¹ ∈ L := by
      refine L.mul_mem ?_ (L.inv_mem hl₁)
      have h := Subgroup.Normal.conj_mem ‹L.Normal› l₁ hl₁ k⁻¹
      rwa [inv_inv] at h
    refine ⟨k₁ * k * k₁⁻¹, K.mul_mem (K.mul_mem hk₁ hk) (K.inv_mem hk₁),
      k₁ * (k⁻¹ * l₁ * k * l₁⁻¹) * k₁⁻¹, Subgroup.Normal.conj_mem ‹L.Normal› _ hm k₁, ?_⟩
    calc k₁ * l₁ * c₁ * k * (k₁ * l₁ * c₁)⁻¹
        = k₁ * l₁ * (c₁ * k * c₁⁻¹) * l₁⁻¹ * k₁⁻¹ := by group
      _ = k₁ * l₁ * k * l₁⁻¹ * k₁⁻¹ := by rw [hcc]
      _ = k₁ * k * k₁⁻¹ * (k₁ * (k⁻¹ * l₁ * k * l₁⁻¹) * k₁⁻¹) := by group
  have hB : ∀ g : X, CFSG.ClassicalInvolution.Generic.conjSub g K ≤
      (K.map (QuotientGroup.mk' L)).comap (QuotientGroup.mk' L) := by
    intro g x hx
    have hk : g⁻¹ * x * g ∈ K := CFSG.ClassicalInvolution.Generic.mem_conjSub_iff.mp hx
    obtain ⟨k₁, hk₁, l₁, hl₁, he⟩ := hA g _ hk
    have hx' : x = k₁ * l₁ := by
      rw [← he]
      group
    refine Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr ⟨k₁, hk₁, ?_⟩)
    rw [hx', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    exact QuotientGroup.eq.mpr (by rw [inv_mul_cancel_left]; exact hl₁)
  have hH : (⊤ : Subgroup X) ≤ (K.map (QuotientGroup.mk' L)).comap (QuotientGroup.mk' L) := by
    rw [← hgen]
    exact iSup_le fun g => hB g
  intro c hc
  obtain ⟨k, hk, hkc⟩ :=
    Subgroup.mem_map.mp (Subgroup.mem_comap.mp (hH (Subgroup.mem_top c)))
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hkc
  exact ⟨k, hk, k⁻¹ * c, QuotientGroup.eq.mp hkc, (mul_inv_cancel_left k c).symm⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
