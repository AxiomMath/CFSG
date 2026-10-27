module

public import CFSG.LargeExtraspecial.A2ModPointMapsNorm
public import CFSG.ClassicalGroups.SpecialLinear.TvCentralizer

public section

namespace CFSG.LargeExtraspecial.A2Mod

open Matrix CFSG.ClassicalGroups.SpecialLinear.TvMod
open scoped commutatorElement

private theorem commutatorElement_mul_left_of_commute {G : Type*} [Group G] {t a b : G}
    (ha : Commute t a) (hb : Commute t b) : ⁅t * a, b⁆ = ⁅a, b⁆ := by
  have h1 : Commute t ⁅a, b⁆ := by
    rw [commutatorElement_def]
    exact ((ha.mul_right hb).mul_right ha.inv_right).mul_right hb.inv_right
  have h2 : t⁻¹ * b⁻¹ = b⁻¹ * t⁻¹ := hb.inv_inv.eq
  calc ⁅t * a, b⁆ = t * (a * b * a⁻¹) * (t⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
    _ = t * ⁅a, b⁆ * t⁻¹ := by rw [h2, commutatorElement_def]; group
    _ = ⁅a, b⁆ := by rw [h1.eq]; group

private theorem commutatorElement_mul_right_of_commute {G : Type*} [Group G] {t a b : G}
    (ha : Commute t a) (hb : Commute t b) : ⁅a, t * b⁆ = ⁅a, b⁆ := by
  have h1 : Commute t ⁅a, b⁆ := by
    rw [commutatorElement_def]
    exact ((ha.mul_right hb).mul_right ha.inv_right).mul_right hb.inv_right
  calc ⁅a, t * b⁆ = a * t * (b * a⁻¹ * b⁻¹) * t⁻¹ := by rw [commutatorElement_def]; group
    _ = t * ⁅a, b⁆ * t⁻¹ := by rw [← ha.eq, commutatorElement_def]; group
    _ = ⁅a, b⁆ := by rw [h1.eq]; group

private theorem commutatorElement_mul_mul_of_commute {G : Type*} [Group G] {t a b c₁ c₂ : G}
    (ha : Commute t a) (hb : Commute t b) (h₁ : c₁ = 1 ∨ c₁ = t) (h₂ : c₂ = 1 ∨ c₂ = t) :
    ⁅c₁ * a, c₂ * b⁆ = ⁅a, b⁆ := by
  have hm : ∀ c : G, (c = 1 ∨ c = t) → Commute c a ∧ Commute c b := by
    intro c hc
    rcases hc with rfl | rfl
    · exact ⟨Commute.one_left a, Commute.one_left b⟩
    · exact ⟨ha, hb⟩
  have hc : Commute c₁ c₂ := by
    rcases h₁ with rfl | rfl
    · exact Commute.one_left _
    · rcases h₂ with rfl | rfl
      · exact Commute.one_right _
      · exact Commute.refl _
  rw [commutatorElement_mul_left_of_commute (hm c₁ h₁).1 (hc.mul_right (hm c₁ h₁).2),
    commutatorElement_mul_right_of_commute (hm c₂ h₂).1 (hm c₂ h₂).2]

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
  {P Pd : (Fin n → ZMod 2) →ₗ[ZMod 2] V} {H : Type*} [Group H] {ρ : H →* (V ≃ₗ[ZMod 2] V)}
  {Ψ : SpecialLinearGroup (Fin n) (ZMod 2) →* H}

private theorem mem_sup_centralizer_of_fix (hP : IsPointMaps (ρ.comp Ψ) Q P Pd) {ℓ : H}
    (hℓ : ∀ g, ∃ g', ℓ * Ψ g * ℓ⁻¹ = Ψ g') {v₀ φ₀ : Fin n → ZMod 2} (hv₀ : v₀ ≠ 0)
    (hφ₀ : φ₀ ≠ 0) (hfix : ρ ℓ (P v₀) = P v₀ ∨ ρ ℓ (Pd φ₀) = Pd φ₀) :
    ℓ ∈ Ψ.range ⊔ Subgroup.centralizer (Ψ.range : Set H) := by
  obtain ⟨g₁, hg₁⟩ : ∃ g₁, ∀ g, Commute ((Ψ g₁)⁻¹ * ℓ) (Ψ g) := hfix.elim
    (hP.exists_mul_commute_of_apply_eq hℓ hv₀) (hP.exists_mul_commute_of_apply_dual_eq hℓ hφ₀)
  have hc : (Ψ g₁)⁻¹ * ℓ ∈ Subgroup.centralizer (Ψ.range : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hh
    exact (hg₁ g).eq.symm
  have h : Ψ g₁ * ((Ψ g₁)⁻¹ * ℓ) ∈ Ψ.range ⊔ Subgroup.centralizer (Ψ.range : Set H) :=
    Subgroup.mul_mem_sup (MonoidHom.mem_range.mpr ⟨g₁, rfl⟩) hc
  rwa [mul_inv_cancel_left] at h

theorem IsPointMaps.le_sup_centralizer_of_tvCore (hP : IsPointMaps (ρ.comp Ψ) Q P Pd)
    (hn : 5 ≤ n) (hΨ : Function.Injective Ψ) {v₀ φ₀ : Fin n → ZMod 2} (hv₀ : v₀ ≠ 0)
    (hφ₀ : φ₀ ≠ 0) (h₀ : φ₀ ⬝ᵥ v₀ = 0) {L : Subgroup H} (hL : ∀ ℓ ∈ L, ℓ * ℓ = 1)
    (hτ : Ψ (tv v₀ φ₀) ∈ L) (hLX : ∀ ℓ ∈ L, ∀ g, ∃ g', ℓ * Ψ g * ℓ⁻¹ = Ψ g')
    (hY : ∀ y ∈ tvCoreGen v₀ φ₀, ∀ ℓ ∈ L, Ψ y * ℓ * (Ψ y)⁻¹ ∈ L) :
    L ≤ Ψ.range ⊔ Subgroup.centralizer (Ψ.range : Set H) ∧
      Nat.card ↥(L ⊓ Ψ.range) ≤ 2 ^ (n - 1) := by
  have hLc : ∀ ℓ ∈ L, ∀ ℓ' ∈ L, Commute ℓ ℓ' := by
    intro ℓ hℓ ℓ' hℓ'
    have h1 : ℓ⁻¹ = ℓ := inv_eq_of_mul_eq_one_right (hL ℓ hℓ)
    have h2 : ℓ'⁻¹ = ℓ' := inv_eq_of_mul_eq_one_right (hL ℓ' hℓ')
    have h3 : (ℓ * ℓ')⁻¹ = ℓ * ℓ' := inv_eq_of_mul_eq_one_right (hL _ (L.mul_mem hℓ hℓ'))
    calc ℓ * ℓ' = (ℓ * ℓ')⁻¹ := h3.symm
      _ = ℓ' * ℓ := by rw [_root_.mul_inv_rev, h1, h2]
  have hA : ∀ a ∈ L.comap Ψ, a * a = 1 := fun a ha =>
    hΨ (by rw [map_mul, map_one]; exact hL _ (Subgroup.mem_comap.mp ha))
  have hAY : ∀ y ∈ tvCoreGen v₀ φ₀, ∀ a ∈ L.comap Ψ, y * a * y⁻¹ ∈ L.comap Ψ := by
    intro y hy a ha
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hY y hy _ (Subgroup.mem_comap.mp ha)
  have hcases := le_pointGroup_or_le_hyperplaneGroup hn hv₀ hφ₀ h₀ hA
    (Subgroup.mem_comap.mpr hτ) hAY
  refine ⟨fun ℓ hℓ => mem_sup_centralizer_of_fix hP (hLX ℓ hℓ) hv₀ hφ₀ ?_, ?_⟩
  · have hcτ : Commute (ρ ℓ) (ρ (Ψ (tv v₀ φ₀))) := (hLc ℓ hℓ _ hτ).map ρ
    by_cases hbig : ∃ a ∈ L.comap Ψ, a ≠ 1 ∧ a ≠ tv v₀ φ₀
    · obtain ⟨a, ha, ha1, haτ⟩ := hbig
      have hca : Commute (ρ ℓ) (ρ (Ψ a)) := (hLc ℓ hℓ _ (Subgroup.mem_comap.mp ha)).map ρ
      rcases hcases with hle | hle
      · obtain ⟨ψ, hψ, rfl⟩ := mem_pointGroup.mp (hle ha)
        have hψ0 : ψ ≠ 0 := by
          rintro rfl
          exact ha1 (tv_zero_right v₀)
        have hψφ : φ₀ ≠ ψ := by
          rintro rfl
          exact haτ rfl
        exact .inl (hP.apply_eq_self_of_commute_tv hv₀ hφ₀ hψ0 hψφ h₀ hψ hcτ hca)
      · obtain ⟨w, hw, rfl⟩ := mem_hyperplaneGroup.mp (hle ha)
        have hw0 : w ≠ 0 := by
          rintro rfl
          exact ha1 (tv_zero_left φ₀)
        have hvw : v₀ ≠ w := by
          rintro rfl
          exact haτ rfl
        exact .inr (hP.apply_dual_eq_self_of_commute_tv hφ₀ hv₀ hw0 hvw h₀ hw hcτ hca)
    · push Not at hbig
      have hconj : ∀ y ∈ tvCoreGen v₀ φ₀, ∃ c, (c = 1 ∨ c = Ψ (tv v₀ φ₀)) ∧
          ℓ * Ψ y * ℓ⁻¹ = c * Ψ y := by
        intro y hy
        obtain ⟨g', hg'⟩ := hLX ℓ hℓ y
        have hmem : g' * y⁻¹ ∈ L.comap Ψ := by
          rw [Subgroup.mem_comap, map_mul, map_inv, ← hg']
          have := L.mul_mem hℓ (hY y hy _ (L.inv_mem hℓ))
          simpa [mul_assoc] using this
        refine ⟨Ψ (g' * y⁻¹), ?_, by rw [hg', map_mul, map_inv, inv_mul_cancel_right]⟩
        by_cases h1 : g' * y⁻¹ = 1
        · exact .inl (by rw [h1, map_one])
        · exact .inr (by rw [hbig _ hmem h1])
      have hpt : ∀ ψ : Fin n → ZMod 2, ψ ⬝ᵥ v₀ = 0 → Commute ℓ (Ψ (tv v₀ ψ)) := by
        intro ψ hψ
        obtain ⟨u, χ, hu₁, hu₂, hχ₁, -, heq⟩ :=
          exists_tv_eq_commutatorElement hn (v := v₀) (φ := φ₀) (w := v₀) hψ
        have hy₁ : tv v₀ χ ∈ tvCoreGen v₀ φ₀ := ⟨v₀, χ, h₀, hχ₁, hχ₁, rfl⟩
        have hz₁ : tv u ψ ∈ tvCoreGen v₀ φ₀ := ⟨u, ψ, hu₁, hψ, hu₂, rfl⟩
        have hc₁ : Commute (Ψ (tv v₀ φ₀)) (Ψ (tv v₀ χ)) :=
          ((commute_tv_of_mem_tvCore (subset_tvCore v₀ φ₀ hy₁)).map Ψ).symm
        have hc₂ : Commute (Ψ (tv v₀ φ₀)) (Ψ (tv u ψ)) :=
          ((commute_tv_of_mem_tvCore (subset_tvCore v₀ φ₀ hz₁)).map Ψ).symm
        obtain ⟨c₁, hc₁1, he₁⟩ := hconj _ hy₁
        obtain ⟨c₂, hc₂1, he₂⟩ := hconj _ hz₁
        have hmap := map_commutatorElement (MulAut.conj ℓ) (Ψ (tv v₀ χ)) (Ψ (tv u ψ))
        simp only [MulAut.conj_apply] at hmap
        refine mul_inv_eq_iff_eq_mul.mp ?_
        rw [heq, map_commutatorElement, hmap, he₁, he₂,
          commutatorElement_mul_mul_of_commute hc₁ hc₂ hc₁1 hc₂1]
      obtain ⟨ψ₁, ψ₂, hψ₁, hψ₂, hψ₁₂, hψ₁v, hψ₂v⟩ :=
        exists_two_ne_zero_annihilator (k := 1) (by omega) ![v₀]
      have h₁ : ψ₁ ⬝ᵥ v₀ = 0 := by simpa using hψ₁v 0
      have h₂ : ψ₂ ⬝ᵥ v₀ = 0 := by simpa using hψ₂v 0
      obtain ⟨ψ, hψ0, hψφ, hψv⟩ : ∃ ψ : Fin n → ZMod 2, ψ ≠ 0 ∧ φ₀ ≠ ψ ∧ ψ ⬝ᵥ v₀ = 0 := by
        by_cases h : φ₀ = ψ₁
        · exact ⟨ψ₂, hψ₂, fun h' => hψ₁₂ (h.symm.trans h'), h₂⟩
        · exact ⟨ψ₁, hψ₁, h, h₁⟩
      exact .inl (hP.apply_eq_self_of_commute_tv hv₀ hφ₀ hψ0 hψφ h₀ hψv hcτ
        ((hpt ψ hψv).map ρ))
  · have hmap : L ⊓ Ψ.range = (L.comap Ψ).map Ψ := by
      rw [Subgroup.map_comap_eq, inf_comm]
    rw [hmap, Subgroup.card_map_of_injective hΨ]
    rcases hcases with hle | hle
    · exact (Subgroup.card_le_of_le hle).trans (card_pointGroup hv₀).le
    · exact (Subgroup.card_le_of_le hle).trans (card_hyperplaneGroup hφ₀).le

end CFSG.LargeExtraspecial.A2Mod
