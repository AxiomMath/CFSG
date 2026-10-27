module

public import CFSG.Fischer.Classification.Orthogonal2.SpModel

public section

namespace CFSG.Fischer.Classification.Orth2

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Module CFSG.LargeExtraspecial CFSG.Open Matrix

private theorem zmod2_cases' (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

variable {m : ℕ} {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}

theorem eq_one_or_eq_conj_of_fix_commute {G : Type} [Group G] {D : Set G}
    (hgen : Subgroup.closure D = ⊤) (halt : ∀ x, b x x = 0)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) (Φ : G ≃* TauCeti.BilinForm.isometryGroup b)
    (hΦ : ∀ g, g ∈ D ↔ ∃ v, v ≠ 0 ∧ Φ g = spT (f := b) halt v)
    {d₀ : G} (hd₀ : d₀ ∈ D) (ψ : MulAut G) (hψ : ∀ g ∈ D, ψ g ∈ D)
    (hfix : ∀ g ∈ D, g * d₀ = d₀ * g → ψ g = g) :
    ψ = 1 ∨ ψ = MulAut.conj d₀ := by
  have hb : b.IsAlt := halt
  have hbn : b.Nondegenerate := nondegenerate_of_isAlt halt hnd
  have hsymm : ∀ x y, b x y = b y x := OrthoF2.isAlt_symm hb
  have hz : ∀ x : Fin (2 * m) → ZMod 2, x + x = 0 := fun x => by
    rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  obtain ⟨u, hu0, hu⟩ := (hΦ d₀).mp hd₀
  have hcomm : ∀ {g g' : G} {v v' : Fin (2 * m) → ZMod 2}, v ≠ 0 → v' ≠ 0 →
      Φ g = spT hb v → Φ g' = spT hb v' → (g * g' = g' * g ↔ b v v' = 0) := by
    intro g g' v v' hv hv' hg hg'
    rw [← spT_mul_comm_iff hb hbn hv, ← hg, ← hg', ← map_mul, ← map_mul]
    exact Φ.injective.eq_iff.symm
  have hmemD : ∀ z, z ≠ 0 → Φ.symm (spT hb z) ∈ D := fun z hz0 =>
    (hΦ _).mpr ⟨z, hz0, Φ.apply_symm_apply _⟩
  have hclaim : ∀ g ∈ D, ∀ v, v ≠ 0 → Φ g = spT hb v →
      ∀ w, w ≠ 0 → Φ (ψ g) = spT hb w → w = v ∨ w = v + u := by
    intro g hg v hv hgv w hw hgw
    have hperp : ∀ z, b z u = 0 → b z (v + w) = 0 := by
      intro z hzu
      by_cases hz0 : z = 0
      · rw [hz0, LinearMap.map_zero₂]
      set h' := Φ.symm (spT hb z) with hh'
      have hh'D : h' ∈ D := hmemD z hz0
      have hh'z : Φ h' = spT hb z := Φ.apply_symm_apply _
      have hh'd : h' * d₀ = d₀ * h' := (hcomm hz0 hu0 hh'z hu).mpr hzu
      have hψh : ψ h' = h' := hfix h' hh'D hh'd
      have e1 : (g * h' = h' * g ↔ b v z = 0) := hcomm hv hz0 hgv hh'z
      have e2 : (ψ g * ψ h' = ψ h' * ψ g ↔ b w z = 0) := by
        rw [hψh]
        exact hcomm hw hz0 hgw hh'z
      have e3 : (ψ g * ψ h' = ψ h' * ψ g ↔ g * h' = h' * g) := by
        rw [← map_mul, ← map_mul]
        exact ψ.injective.eq_iff
      have key : (b v z = 0 ↔ b w z = 0) := e1.symm.trans (e3.symm.trans e2)
      rw [map_add, hsymm z v, hsymm z w]
      rcases zmod2_cases' (b v z) with h0 | h1
      · rw [h0, key.mp h0, add_zero]
      · have : b w z ≠ 0 := fun h => by rw [key.mpr h] at h1; exact zero_ne_one h1
        rcases zmod2_cases' (b w z) with h0' | h1'
        · exact absurd h0' this
        · rw [h1, h1']; rfl
    rcases eq_zero_or_eq_of_forall_perp hb hbn hperp with h0 | h1
    · left
      have h2 : v + w + w = 0 + w := by rw [h0]
      rw [add_assoc, hz, add_zero, zero_add] at h2
      exact h2.symm
    · right
      have h2 : v + w + v = u + v := by rw [h1]
      rw [add_comm v w, add_assoc, hz, add_zero, add_comm u v] at h2
      exact h2
  have hvu0 : ∀ v, b v u = 1 → v + u ≠ 0 := by
    intro v hvu h0
    have : b (v + u) u = 1 := by rw [map_add, LinearMap.add_apply, hvu, hb.self_eq_zero,
      add_zero]
    rw [h0, LinearMap.map_zero₂] at this
    exact zero_ne_one this
  have hext : ∀ φ₁ φ₂ : MulAut G, (∀ g ∈ D, φ₁ g = φ₂ g) → φ₁ = φ₂ := by
    intro φ₁ φ₂ h
    refine MulEquiv.ext fun g => ?_
    have hg : g ∈ Subgroup.closure D := hgen ▸ Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact h x hx
    | one => rw [map_one, map_one]
    | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]
    | inv x _ hx => rw [map_inv, map_inv, hx]
  by_cases hall : ∀ g ∈ D, ψ g = g
  · left
    exact hext ψ 1 fun g hg => by rw [hall g hg]; rfl
  · right
    push Not at hall
    obtain ⟨g₀, hg₀D, hg₀⟩ := hall
    obtain ⟨v₀, hv₀, hgv₀⟩ := (hΦ g₀).mp hg₀D
    obtain ⟨w₀, hw₀, hgw₀⟩ := (hΦ _).mp (hψ g₀ hg₀D)
    have hg₀u : b v₀ u = 1 := by
      rcases zmod2_cases' (b v₀ u) with h0 | h1
      · exact absurd (hfix g₀ hg₀D ((hcomm hv₀ hu0 hgv₀ hu).mpr h0)) hg₀
      · exact h1
    have hw₀eq : w₀ = v₀ + u := by
      rcases hclaim g₀ hg₀D v₀ hv₀ hgv₀ w₀ hw₀ hgw₀ with h | h
      · exfalso
        apply hg₀
        apply Φ.injective
        rw [hgw₀, hgv₀, h]
      · exact h
    refine hext ψ (MulAut.conj d₀) fun g hg => ?_
    obtain ⟨v, hv, hgv⟩ := (hΦ g).mp hg
    rcases zmod2_cases' (b v u) with h0 | h1
    ·
      have hgd : g * d₀ = d₀ * g := (hcomm hv hu0 hgv hu).mpr h0
      rw [hfix g hg hgd, MulAut.conj_apply, ← hgd, mul_inv_cancel_right]
    · obtain ⟨w, hw, hgw⟩ := (hΦ _).mp (hψ g hg)
      have hconj : Φ (MulAut.conj d₀ g) = spT hb (v + u) := by
        rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hu, hgv]
        have hinv : (spT hb u)⁻¹ = spT hb u := inv_eq_of_mul_eq_one_left (spT_mul_self hb u)
        have huv : b u v = 1 := by rw [hsymm]; exact h1
        rw [hinv, spT_mul_spT_mul_spT hb huv, add_comm]
      rcases hclaim g hg v hv hgv w hw hgw with hwv | hwv
      ·
        exfalso
        have e1 := hcomm hv hv₀ hgv hgv₀
        have e2 : (ψ g * ψ g₀ = ψ g₀ * ψ g ↔ b v (v₀ + u) = 0) := by
          rw [show ψ g = g from Φ.injective (by rw [hgw, hgv, hwv])]
          rw [hw₀eq] at hgw₀
          exact hcomm hv (hvu0 v₀ hg₀u) hgv hgw₀
        have e3 : (ψ g * ψ g₀ = ψ g₀ * ψ g ↔ g * g₀ = g₀ * g) := by
          rw [← map_mul, ← map_mul]
          exact ψ.injective.eq_iff
        have key : (b v v₀ = 0 ↔ b v (v₀ + u) = 0) := e1.symm.trans (e3.symm.trans e2)
        rw [map_add, h1] at key
        rcases zmod2_cases' (b v v₀) with h0' | h1'
        · rw [h0', zero_add] at key
          exact one_ne_zero (key.mp rfl)
        · rw [h1'] at key
          exact one_ne_zero (key.mpr (by decide))
      · apply Φ.injective
        rw [hconj, hgw, hwv]

end CFSG.Fischer.Classification.Orth2
