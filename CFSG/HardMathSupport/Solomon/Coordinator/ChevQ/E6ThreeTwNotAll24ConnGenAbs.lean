module

public import CFSG.HardMathSupport.Lang.TwE6Step3.FixedSplit

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSGen

open CFSG.HardMathSupport.Lang.TwE6Step3

variable {G X : Type*} [Group G] [Group X]

theorem exists_peel_frame (F : G →* G) (F' : X →* X) (ψ : X →* G)
    (hψF : ∀ y, F (ψ y) = ψ (F' y)) {H Q' : Subgroup G} (D : Subgroup X)
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hFH : ∀ t ∈ H, F t ∈ H)
    (hFQ' : ∀ q ∈ Q', F q ∈ Q')
    (hHQ₁ : H ≤ Subgroup.normalizer (ψ.range : Set G))
    (hHQ' : H ≤ Subgroup.normalizer (Q' : Set G))
    (hQQ' : ∀ a ∈ ψ.range, ∀ b ∈ Q', a * b = b * a)
    (hLang : ∀ d ∈ D, ∃ δ ∈ D, F' δ * δ⁻¹ = d)
    (hψD : ∀ δ ∈ D, ψ δ ∈ H)
    (hkerD : ∀ κ, ψ κ = 1 → κ ∈ D) (hkerc : ∀ κ, ψ κ = 1 → ∀ y, κ * y = y * κ)
    (hc2 : ∀ y, (∀ δ ∈ D, ψ y * ψ δ = ψ δ * ψ y) → y ∈ D)
    {x : G} (hx : x ∈ H ⊔ (ψ.range ⊔ Q')) (hFx : F x = x) :
    ∃ y, F' y = y ∧ ∃ x' ∈ H ⊔ Q', F x' = x' ∧ x = ψ y * x' := by
  classical
  have hQ₁n : ψ.range ≤ Subgroup.normalizer (Q' : Set G) := le_normalizer_of_commute hQQ'
  have hHQ : H ≤ Subgroup.normalizer ((ψ.range ⊔ Q' : Subgroup G) : Set G) :=
    le_normalizer_sup_of_commute hHQ₁ hHQ' hQQ'
  have hHQ'n : H ≤ Subgroup.normalizer (Q' : Set G) := hHQ'
  have hnf : ∀ z ∈ H ⊔ Q', ∃ t ∈ H, ∃ q ∈ Q', z = t * q := by
    intro z hz
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHQ'n] at hz
    obtain ⟨t, ht, q, hq, rfl⟩ := hz
    exact ⟨t, ht, q, hq, rfl⟩
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHQ] at hx
  obtain ⟨t₀, ht₀, q, hq, rfl⟩ := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hQ₁n] at hq
  obtain ⟨q₁, ⟨y₀, rfl⟩, q', hq', rfl⟩ := hq
  beta_reduce at hFx ⊢
  obtain ⟨q₁', hq₁'⟩ : ∃ q : G, q = t₀ * ψ y₀ * t₀⁻¹ := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ z : G, z = t₀ * q' := ⟨_, rfl⟩
  have hq₁'mem : q₁' ∈ ψ.range := by
    rw [hq₁']
    exact (Subgroup.mem_normalizer_iff.1 (hHQ₁ ht₀) (ψ y₀)).1 ⟨y₀, rfl⟩
  have hyHQ : y ∈ H ⊔ Q' := by
    rw [hy]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ht₀) (Subgroup.mem_sup_right hq')
  have hxeq : t₀ * (ψ y₀ * q') = q₁' * y := by rw [hq₁', hy]; group
  rw [hxeq] at hFx ⊢
  obtain ⟨Y₁, hY₁⟩ := hq₁'mem
  have hFyQ : F y ∈ H ⊔ Q' := by
    rw [hy, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hFH t₀ ht₀))
      (Subgroup.mem_sup_right (hFQ' q' hq'))
  have hFq : F q₁' * F y = q₁' * y := by rw [← map_mul]; exact hFx
  have hFq1 : F q₁' = q₁' * ψ (Y₁⁻¹ * F' Y₁) := by
    rw [map_mul, map_inv, hY₁, ← hψF, hY₁]
    group
  have hu : ψ (Y₁⁻¹ * F' Y₁) = y * (F y)⁻¹ := by
    have h1 : q₁' * ψ (Y₁⁻¹ * F' Y₁) * F y = q₁' * y := by rw [← hFq1]; exact hFq
    calc ψ (Y₁⁻¹ * F' Y₁) = q₁'⁻¹ * (q₁' * ψ (Y₁⁻¹ * F' Y₁) * F y) * (F y)⁻¹ := by group
      _ = y * (F y)⁻¹ := by rw [h1]; group
  have huD : Y₁⁻¹ * F' Y₁ ∈ D := by
    apply hc2
    intro δ hδ
    obtain ⟨t'', ht'', q'', hq'', hue⟩ := hnf _ (Subgroup.mul_mem _ hyHQ (inv_mem hFyQ))
    rw [hu, hue]
    have h1 : q'' * ψ δ = ψ δ * q'' := (hQQ' _ ⟨δ, rfl⟩ _ hq'').symm
    calc t'' * q'' * ψ δ = t'' * (q'' * ψ δ) := by group
      _ = t'' * (ψ δ * q'') := by rw [h1]
      _ = (t'' * ψ δ) * q'' := by group
      _ = (ψ δ * t'') * q'' := by rw [hH _ ht'' _ (hψD δ hδ)]
      _ = ψ δ * (t'' * q'') := by group
  obtain ⟨δ, hδD, hδ⟩ := hLang _ (inv_mem huD)
  have hFr₁ : F (q₁' * ψ δ) = q₁' * ψ δ := by
    have h2 : F' δ = (Y₁⁻¹ * F' Y₁)⁻¹ * δ := by
      calc F' δ = (F' δ * δ⁻¹) * δ := by group
        _ = (Y₁⁻¹ * F' Y₁)⁻¹ * δ := by rw [hδ]
    rw [map_mul, hFq1, hψF, mul_assoc, ← map_mul, h2]
    congr 2
    group
  have hx'mem : (ψ δ)⁻¹ * y ∈ H ⊔ Q' :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left (inv_mem (hψD δ hδD))) hyHQ
  have hFx' : F ((ψ δ)⁻¹ * y) = (ψ δ)⁻¹ * y := by
    have h1 : F (q₁' * ψ δ) * F ((ψ δ)⁻¹ * y) = (q₁' * ψ δ) * ((ψ δ)⁻¹ * y) := by
      rw [← map_mul]
      calc F (q₁' * ψ δ * ((ψ δ)⁻¹ * y)) = F (q₁' * y) := by congr 1; group
        _ = q₁' * y := hFx
        _ = (q₁' * ψ δ) * ((ψ δ)⁻¹ * y) := by group
    rw [hFr₁] at h1
    exact mul_left_cancel h1
  obtain ⟨Y₁', hY₁'⟩ : ∃ Y : X, Y = Y₁ * δ := ⟨_, rfl⟩
  have hrY : q₁' * ψ δ = ψ Y₁' := by rw [hY₁', map_mul, hY₁]
  have hκ : ψ (F' Y₁' * Y₁'⁻¹) = 1 := by
    rw [map_mul, map_inv, ← hψF, ← hrY, hFr₁]; group
  have hκD := hkerD _ hκ
  obtain ⟨δ', hδ'D, hδ'⟩ := hLang _ hκD
  obtain ⟨Y₂, hY₂⟩ : ∃ Y : X, Y = Y₁' * δ'⁻¹ := ⟨_, rfl⟩
  have hFY₂ : F' Y₂ = Y₂ := by
    have hc := hkerc _ hκ Y₂
    have h3 : F' δ' = (F' Y₁' * Y₁'⁻¹) * δ' := by rw [← hδ']; group
    calc F' Y₂ = F' Y₁' * (F' δ')⁻¹ := by rw [hY₂, map_mul, map_inv]
      _ = (F' Y₁' * Y₁'⁻¹) * (Y₁' * δ'⁻¹) * (F' Y₁' * Y₁'⁻¹)⁻¹ := by rw [h3]; group
      _ = Y₁' * δ'⁻¹ := by rw [hY₂] at hc; rw [hc]; group
      _ = Y₂ := hY₂.symm
  have hfinal : ψ Y₂ * (ψ δ' * ((ψ δ)⁻¹ * y)) = q₁' * y := by
    have h1 : ψ Y₂ * ψ δ' = ψ Y₁' := by rw [← map_mul, hY₂, inv_mul_cancel_right]
    calc ψ Y₂ * (ψ δ' * ((ψ δ)⁻¹ * y)) = (ψ Y₂ * ψ δ') * ((ψ δ)⁻¹ * y) := by group
      _ = ψ Y₁' * ((ψ δ)⁻¹ * y) := by rw [h1]
      _ = q₁' * ψ δ * ((ψ δ)⁻¹ * y) := by rw [hrY]
      _ = q₁' * y := by group
  refine ⟨Y₂, hFY₂, ψ δ' * ((ψ δ)⁻¹ * y),
    Subgroup.mul_mem _ (Subgroup.mem_sup_left (hψD δ' hδ'D)) hx'mem, ?_, hfinal.symm⟩
  have h1 : F (ψ Y₂) * F (ψ δ' * ((ψ δ)⁻¹ * y)) = ψ Y₂ * (ψ δ' * ((ψ δ)⁻¹ * y)) := by
    rw [← map_mul, hfinal]
    exact hFx
  rw [hψF, hFY₂] at h1
  exact mul_left_cancel h1

end KSGen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
