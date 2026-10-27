module

public import CFSG.GH74.GLS.IVK.L2.BorelSylow
public import CFSG.CharacterTheory.PSL2Table.Partition

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L48

open Subgroup

structure IsTorus {G : Type} [Group G] (H : Subgroup G) : Prop where
  comm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x
  ti : ∀ x ∈ H, x ≠ 1 → ∀ g : G, g * x * g⁻¹ ∈ H → g ∈ normalizer (H : Set G)
  exists_inv : ∃ w : G, w ∉ H ∧ w * w = 1 ∧ (∀ x ∈ H, w * x * w⁻¹ = x⁻¹) ∧
    ∀ g : G, g ∈ normalizer (H : Set G) ↔ g ∈ H ∨ w⁻¹ * g ∈ H

namespace IsTorus

variable {G : Type} [Group G] {H : Subgroup G}

theorem card_normalizer [Finite G] (hH : IsTorus H) :
    Nat.card (normalizer (H : Set G)) = 2 * Nat.card H := by
  obtain ⟨w, hw, -, -, hN⟩ := hH.exists_inv
  exact CFSG.PSL2Table.card_eq_two_mul_of_mem_iff hw hN

theorem conj_eq_inv (hH : IsTorus H) {g : G} (hg : g ∈ normalizer (H : Set G)) (hgH : g ∉ H)
    {x : G} (hx : x ∈ H) : g * x * g⁻¹ = x⁻¹ := by
  obtain ⟨w, -, -, hinv, hN⟩ := hH.exists_inv
  rcases (hN g).mp hg with h | h
  · exact absurd h hgH
  · obtain ⟨h', hh', rfl⟩ : ∃ h' ∈ H, g = w * h' := ⟨w⁻¹ * g, h, by group⟩
    have h1 : h' * x * h'⁻¹ = x := by rw [hH.comm h' hh' x hx, mul_inv_cancel_right]
    calc w * h' * x * (w * h')⁻¹ = w * (h' * x * h'⁻¹) * w⁻¹ := by group
      _ = x⁻¹ := by rw [h1]; exact hinv x hx

theorem centralizer_le (hH : IsTorus H) {y : G} (hy : y ∈ H) (hy2 : y * y ≠ 1) :
    centralizer {y} ≤ H := by
  intro g hg
  rw [mem_centralizer_singleton_iff] at hg
  have hy1 : y ≠ 1 := fun h => hy2 (by rw [h, one_mul])
  have hconj : g * y * g⁻¹ = y := by rw [hg, mul_inv_cancel_right]
  have hgN : g ∈ normalizer (H : Set G) := hH.ti y hy hy1 g (by rw [hconj]; exact hy)
  by_contra hgH
  have h := hH.conj_eq_inv hgN hgH hy
  rw [hconj] at h
  exact hy2 (mul_eq_one_iff_eq_inv.mpr h)

theorem centralizer_eq_normalizer (hH : IsTorus H) {a : G} (ha : a ∈ H) (ha1 : a ≠ 1)
    (ha2 : a * a = 1) : centralizer {a} = normalizer (H : Set G) := by
  ext g
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro hg
    have hconj : g * a * g⁻¹ = a := by rw [hg, mul_inv_cancel_right]
    exact hH.ti a ha ha1 g (by rw [hconj]; exact ha)
  · intro hg
    by_cases hgH : g ∈ H
    · exact hH.comm g hgH a ha
    · have h := hH.conj_eq_inv hg hgH ha
      have hainv : a⁻¹ = a := (mul_eq_one_iff_eq_inv.mp ha2).symm
      calc g * a = g * a * g⁻¹ * g := by group
        _ = a * g := by rw [h, hainv]

theorem card_centralizer [Finite G] (hH : IsTorus H) {a : G} (ha : a ∈ H) (ha1 : a ≠ 1)
    (ha2 : a * a = 1) : Nat.card (centralizer {a} : Subgroup G) = 2 * Nat.card H := by
  rw [hH.centralizer_eq_normalizer ha ha1 ha2, hH.card_normalizer]

theorem map_equiv {G' : Type} [Group G'] (ψ : G ≃* G') (hH : IsTorus H) :
    IsTorus (H.map ψ.toMonoidHom) := by
  obtain ⟨w, hw, hw2, hinv, hN⟩ := hH.exists_inv
  refine ⟨?_, ?_, ⟨ψ w, ?_, ?_, ?_, ?_⟩⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, hH.comm x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩ hx1 g hg
    obtain ⟨g, rfl⟩ := ψ.surjective g
    rw [CFSG.GH74.GLS.IVK.L2Borel.normalizer_map_equiv, Subgroup.mem_map_equiv,
      MulEquiv.symm_apply_apply]
    rw [MulEquiv.coe_toMonoidHom, ← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_equiv,
      MulEquiv.symm_apply_apply] at hg
    refine hH.ti x hx (fun h => hx1 ?_) g hg
    rw [h, map_one]
  · rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    exact hw
  · rw [← map_mul, hw2, map_one]
  · rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_inv, ← map_mul, ← map_mul, hinv x hx, map_inv]
  · intro g
    obtain ⟨g, rfl⟩ := ψ.surjective g
    rw [CFSG.GH74.GLS.IVK.L2Borel.normalizer_map_equiv, Subgroup.mem_map_equiv,
      MulEquiv.symm_apply_apply, Subgroup.mem_map_equiv, ← map_inv, ← map_mul,
      Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    exact hN g

theorem conj (hH : IsTorus H) (c : G) : IsTorus (H.map (MulAut.conj c).toMonoidHom) :=
  hH.map_equiv (MulAut.conj c)

end IsTorus

theorem eq_of_dvd_of_mem {t x z : ℕ} (ht : 2 ≤ t) (hx : x = t ∨ x = t + 1) (hz : z = t ∨ z = t + 1)
    (hdvd : x ∣ z) : x = z := by
  rcases hx with rfl | rfl <;> rcases hz with rfl | rfl
  · rfl
  · have h1 : x ∣ 1 := (Nat.dvd_add_right (dvd_refl x)).mp hdvd
    have := Nat.le_of_dvd one_pos h1
    omega
  · have := Nat.le_of_dvd (by omega) hdvd
    omega
  · rfl

theorem key_of_torus {G : Type} [Group G] [Finite G] {t : ℕ} (ht : 2 ≤ t) {a : G}
    (ha2 : a * a = 1) (ha1 : a ≠ 1) {Ha : Subgroup G} (hHa : IsTorus Ha) (haH : a ∈ Ha)
    (hcardA : Nat.card Ha = t ∨ Nat.card Ha = t + 1) {Y : Subgroup G} {y₀ : G} (hy₀Y : y₀ ∈ Y)
    (hy₀2 : y₀ * y₀ ≠ 1) (hy₀Z : ∀ y ∈ Y, y * y₀ = y₀ * y) {H₀ : Subgroup G} (hH₀ : IsTorus H₀)
    (hy₀H : y₀ ∈ H₀) (hcard₀ : Nat.card H₀ = t ∨ Nat.card H₀ = t + 1)
    (hN : ∀ c : G, c * a = a * c → c ∈ normalizer (Y : Set G)) : ∀ y ∈ Y, y * a = a * y := by
  have hy₀1 : y₀ ≠ 1 := fun h => hy₀2 (by rw [h, one_mul])
  have hYH₀ : Y ≤ H₀ := fun y hy =>
    hH₀.centralizer_le hy₀H hy₀2 (mem_centralizer_singleton_iff.mpr (hy₀Z y hy))
  have hDle : centralizer {a} ≤ normalizer (H₀ : Set G) := by
    intro c hc
    rw [mem_centralizer_singleton_iff] at hc
    have hcY : c * y₀ * c⁻¹ ∈ Y := (mem_normalizer_iff.mp (hN c hc) y₀).mp hy₀Y
    exact hH₀.ti y₀ hy₀H hy₀1 c (hYH₀ hcY)
  have hdvd : Nat.card Ha ∣ Nat.card H₀ := by
    have h := Subgroup.card_dvd_of_le hDle
    rw [hHa.card_centralizer haH ha1 ha2, hH₀.card_normalizer] at h
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
  have hcard : Nat.card Ha = Nat.card H₀ := eq_of_dvd_of_mem ht hcardA hcard₀ hdvd
  have heq : centralizer {a} = normalizer (H₀ : Set G) := by
    refine Subgroup.eq_of_le_of_card_ge hDle ?_
    rw [hHa.card_centralizer haH ha1 ha2, hH₀.card_normalizer, hcard]
  intro y hy
  have hyD : y ∈ centralizer {a} := by
    rw [heq]
    exact le_normalizer (hYH₀ hy)
  exact mem_centralizer_singleton_iff.mp hyD

end CFSG.GH74.GLS.Stage2.Signalizer.L48
