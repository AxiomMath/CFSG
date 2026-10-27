module

public import CFSG.GH74.GLS.C3.Layer1.Th2P61A7

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup CFSG

theorem centralizer_rootFour_sup_swap {F : Subgroup (Perm (Fin 7))} (hF : IsRootFour F)
    {t : Perm (Fin 7)} (ht : t.IsSwap) (hdis : ∀ i, (∃ f ∈ F, f i ≠ i) → t i = i)
    {g : Perm (Fin 7)} (hg : ∀ y ∈ F ⊔ Subgroup.zpowers t, g * y = y * g) :
    g ∈ F ⊔ Subgroup.zpowers t := by
  classical
  obtain ⟨-, hcard, hF2, S, hS, hsupp⟩ := hF
  have hFt : F ≤ F ⊔ zpowers t := le_sup_left
  have htmem : t ∈ F ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have hFab : ∀ f ∈ F, ∀ f' ∈ F, f * f' = f' * f := by
    intro f hf f' hf'
    have h1 : (f * f') * (f * f') = 1 := hF2 _ (F.mul_mem hf hf')
    have h2 : f⁻¹ = f := inv_eq_of_mul_eq_one_right (hF2 f hf)
    have h3 : f'⁻¹ = f' := inv_eq_of_mul_eq_one_right (hF2 f' hf')
    have : f * f' = (f * f')⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    rw [this, mul_inv_rev, h2, h3]
  obtain ⟨f₁, hf₁F, hf₁1⟩ : ∃ f ∈ F, f ≠ 1 := by
    by_contra hno
    push Not at hno
    have : F = ⊥ := (Subgroup.eq_bot_iff_forall F).2 hno
    rw [this, Subgroup.card_bot] at hcard
    omega
  have hS₁ : f₁.support = S := hsupp f₁ hf₁F hf₁1
  obtain ⟨x, y, hxy, rfl⟩ := ht
  have hxS : x ∉ S := by
    intro hxS
    rw [← hS₁] at hxS
    have := hdis x ⟨f₁, hf₁F, Equiv.Perm.mem_support.1 hxS⟩
    rw [swap_apply_left] at this
    exact hxy this.symm
  have hyS : y ∉ S := by
    intro hyS
    rw [← hS₁] at hyS
    have := hdis y ⟨f₁, hf₁F, Equiv.Perm.mem_support.1 hyS⟩
    rw [swap_apply_right] at this
    exact hxy this
  have hgS : ∀ i ∈ S, g i ∈ S := by
    intro i hi
    rw [← hS₁] at hi ⊢
    have hc := hg f₁ (hFt hf₁F)
    have : f₁ (g i) = g (f₁ i) := by
      have := congrArg (fun p : Perm (Fin 7) => p i) hc
      simpa using this.symm
    rw [Equiv.Perm.mem_support, this]
    intro h
    exact (Equiv.Perm.mem_support.1 hi) (g.injective h)
  have hmove : ∀ f ∈ F, f ≠ 1 → ∀ i ∈ S, f i ≠ i := by
    intro f hf hf1 i hi
    rw [← hsupp f hf hf1] at hi
    exact Equiv.Perm.mem_support.1 hi
  have hFS : ∀ f ∈ F, ∀ i ∈ S, f i ∈ S := by
    intro f hf i hi
    by_cases hf1 : f = 1
    · rw [hf1]; simpa using hi
    · rw [← hsupp f hf hf1] at hi ⊢
      exact Equiv.Perm.apply_mem_support.2 hi
  have hreg : ∀ i ∈ S, ∀ j ∈ S, ∃ f ∈ F, f i = j := by
    intro i hi j hj
    let φ : F → S := fun f => ⟨f.1 i, hFS f.1 f.2 i hi⟩
    have hinj : Function.Injective φ := by
      intro f f' h
      have h1 : f.1 i = f'.1 i := congrArg Subtype.val h
      have h2 : (f'.1⁻¹ * f.1) i = i := by
        rw [Equiv.Perm.mul_apply, h1]; simp
      by_contra hne
      have hne' : f'.1⁻¹ * f.1 ≠ 1 := by
        intro h3
        apply hne
        apply Subtype.ext
        have : f.1 = f'.1 := by
          calc f.1 = f'.1 * (f'.1⁻¹ * f.1) := by group
            _ = f'.1 := by rw [h3, mul_one]
        exact this
      exact hmove _ (F.mul_mem (F.inv_mem f'.2) f.2) hne' i hi h2
    have hcardS : Nat.card ↥S = 4 := by rw [Nat.card_eq_fintype_card, Fintype.card_coe, hS]
    have hbij : Function.Bijective φ :=
      hinj.bijective_of_nat_card_le (by rw [hcard, hcardS])
    obtain ⟨f, hf⟩ := hbij.2 ⟨j, hj⟩
    exact ⟨f.1, f.2, congrArg Subtype.val hf⟩
  have hS0 : S.Nonempty := by
    rw [← Finset.card_pos, hS]; norm_num
  obtain ⟨s₀, hs₀⟩ := hS0
  obtain ⟨f₂, hf₂F, hf₂⟩ := hreg s₀ hs₀ (g s₀) (hgS s₀ hs₀)
  set g' : Perm (Fin 7) := f₂⁻¹ * g with hg'
  have hcommF : ∀ f ∈ F, g' * f = f * g' := by
    intro f hf
    have h1 := hg f (hFt hf)
    have h2 := hFab f₂⁻¹ (F.inv_mem hf₂F) f hf
    calc g' * f = f₂⁻¹ * (g * f) := by rw [hg', mul_assoc]
      _ = f₂⁻¹ * (f * g) := by rw [h1]
      _ = (f₂⁻¹ * f) * g := by rw [mul_assoc]
      _ = (f * f₂⁻¹) * g := by rw [h2]
      _ = f * g' := by rw [hg', mul_assoc]
  have hg's : g' s₀ = s₀ := by
    rw [hg', Equiv.Perm.mul_apply, ← hf₂]; simp
  have hfix : ∀ i ∈ S, g' i = i := by
    intro i hi
    obtain ⟨f, hf, rfl⟩ := hreg s₀ hs₀ i hi
    have h1 : g' (f s₀) = f (g' s₀) := by
      have := congrArg (fun p : Perm (Fin 7) => p s₀) (hcommF f hf)
      simpa using this
    rw [h1, hg's]
  have hct : g' * swap x y = swap x y * g' := by
    have h1 := hg (swap x y) htmem
    have h2 := hFab f₂⁻¹ (F.inv_mem hf₂F)
    have hcomm_t : f₂⁻¹ * swap x y = swap x y * f₂⁻¹ := by
      ext i
      simp only [Equiv.Perm.mul_apply]
      by_cases hiS : i ∈ S
      · have h4 : swap x y i = i := by
          apply swap_apply_of_ne_of_ne
          · rintro rfl; exact hxS hiS
          · rintro rfl; exact hyS hiS
        rw [h4]
        have h5 : f₂⁻¹ i ∈ S := hFS _ (F.inv_mem hf₂F) i hiS
        have h6 : swap x y (f₂⁻¹ i) = f₂⁻¹ i := by
          apply swap_apply_of_ne_of_ne
          · intro h; rw [h] at h5; exact hxS h5
          · intro h; rw [h] at h5; exact hyS h5
        rw [h6]
      · have h4 : f₂⁻¹ i = i := by
          by_contra hne
          by_cases hf1 : f₂⁻¹ = 1
          · rw [hf1] at hne; simp at hne
          · apply hiS
            rw [← hsupp _ (F.inv_mem hf₂F) hf1]
            exact Equiv.Perm.mem_support.2 hne
        rw [h4]
        by_cases hf1 : f₂⁻¹ = 1
        · rw [hf1]; simp
        · have : swap x y i ∉ S := by
            by_cases hix : i = x
            · rw [hix, swap_apply_left]; exact hyS
            · by_cases hiy : i = y
              · rw [hiy, swap_apply_right]; exact hxS
              · rw [swap_apply_of_ne_of_ne hix hiy]; exact hiS
          have h7 : f₂⁻¹ (swap x y i) = swap x y i := by
            by_contra hne
            apply this
            rw [← hsupp _ (F.inv_mem hf₂F) hf1]
            exact Equiv.Perm.mem_support.2 hne
          rw [h7]
    calc g' * swap x y = f₂⁻¹ * (g * swap x y) := by rw [hg', mul_assoc]
      _ = f₂⁻¹ * (swap x y * g) := by rw [h1]
      _ = (f₂⁻¹ * swap x y) * g := by rw [mul_assoc]
      _ = (swap x y * f₂⁻¹) * g := by rw [hcomm_t]
      _ = swap x y * g' := by rw [hg', mul_assoc]
  rcases eq_one_or_swap_of_comm hS hxy hxS hyS hfix hct with h1 | h1
  · have : g = f₂ := by
      calc g = f₂ * (f₂⁻¹ * g) := by group
        _ = f₂ := by rw [← hg', h1, mul_one]
    rw [this]; exact hFt hf₂F
  · have : g = f₂ * swap x y := by
      calc g = f₂ * (f₂⁻¹ * g) := by group
        _ = f₂ * swap x y := by rw [← hg', h1]
    rw [this]
    exact Subgroup.mul_mem _ (hFt hf₂F) htmem

end CFSG.GH74.GLS.Th2.Obs
