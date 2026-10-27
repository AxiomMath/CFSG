module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Final

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

namespace SAU

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f s y n : G} {S₀ : Subgroup G}

theorem conj_f_cases (hF : FourHyp G L f) {x : G} (hx : x * f ^ 2 = f ^ 2 * x) :
    x * f * x⁻¹ = f ∨ x * f * x⁻¹ = f⁻¹ := by
  have hxn : x ∈ normalizer (L : Set G) := by
    rw [← hF.norm]
    exact mem_centralizer_singleton_iff.2 hx
  have hmem : x * f * x⁻¹ ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    have hl' : x⁻¹ * l * x⁻¹⁻¹ ∈ L := (mem_normalizer_iff.1 (inv_mem hxn) l).1 hl
    have hc : x⁻¹ * l * x⁻¹⁻¹ * f = f * (x⁻¹ * l * x⁻¹⁻¹) :=
      mem_centralizer_iff.1 hF.mem_cent _ hl'
    simp only [inv_inv] at hc
    calc l * (x * f * x⁻¹) = x * ((x⁻¹ * l * x) * f) * x⁻¹ := by group
      _ = x * (f * (x⁻¹ * l * x)) * x⁻¹ := by rw [hc]
      _ = x * f * x⁻¹ * l := by group
  rw [hF.cent] at hmem
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
  have hsq : (x * f * x⁻¹) ^ 2 = f ^ 2 := by
    rw [conj_pow]
    calc x * f ^ 2 * x⁻¹ = (f ^ 2 * x) * x⁻¹ := by rw [hx]
      _ = f ^ 2 := by group
  rw [← hk] at hsq
  have h0 : f ^ (k * 2) = f ^ (2 : ℤ) := by
    rw [_root_.zpow_mul]
    simpa using hsq
  have h1 : f ^ (k * 2 - 2) = 1 := by
    rw [_root_.zpow_sub, h0, mul_inv_cancel]
  have h2 : ((orderOf f : ℕ) : ℤ) ∣ k * 2 - 2 := orderOf_dvd_iff_zpow_eq_one.2 h1
  rw [hF.order] at h2
  have h3 : f ^ (k % 4) = f ^ k := by
    have := zpow_mod_orderOf f k
    rw [hF.order] at this
    simpa using this
  have hk4 : k % 4 = 1 ∨ k % 4 = 3 := by
    push_cast at h2
    omega
  have h4 : f ^ (4 : ℤ) = 1 := by
    have := hF.pow_four
    exact_mod_cast this
  rw [← hk, ← h3]
  rcases hk4 with h | h
  · left
    rw [h, zpow_one]
  · right
    rw [h]
    have : f ^ (3 : ℤ) * f = 1 := by
      calc f ^ (3 : ℤ) * f = f ^ (4 : ℤ) := by rw [← _root_.zpow_add_one]; norm_num
        _ = 1 := h4
    exact eq_inv_of_mul_eq_one_left this

section Hyps

variable (H : Sect7Hyps G L f s y S₀ n)
include H

theorem hcom : ∀ l ∈ L, l * f = f * l := fun l hl => mem_centralizer_iff.1 H.four.mem_cent l hl

theorem hyL : y ∈ normalizer (L : Set G) := by
  rw [← H.four.norm, H.cent_eq]
  exact Subgroup.mem_sup_right (mem_zpowers y)

theorem hC : ∀ x : G, x * f = f * x → x ∈ L ⊔ zpowers f := fun _ hx =>
  mem_sup_zpowers_of_commute_of_centralizer_eq H.four.order (hcom H) H.yy H.yf (hyL H) H.cent_eq hx

theorem mem_normalizer_L {x : G} (hx : x * f ^ 2 = f ^ 2 * x) : x ∈ normalizer (L : Set G) := by
  rw [← H.four.norm]
  exact mem_centralizer_singleton_iff.2 hx

theorem y_conj_mem_LF : ∀ a ∈ L ⊔ zpowers f, y * a * y⁻¹ ∈ L ⊔ zpowers f := by
  intro a ha
  obtain ⟨l, hl, i, rfl⟩ := exists_mul_zpow_of_mem_sup (hcom H) ha
  have e : y * (l * f ^ i) * y⁻¹ = (y * l * y⁻¹) * (y * f * y⁻¹) ^ i := by
    rw [conj_zpow]; group
  rw [e, H.yf]
  exact Subgroup.mul_mem_sup ((mem_normalizer_iff.1 (hyL H) l).1 hl)
    (zpow_mem (inv_mem (mem_zpowers f)) i)

theorem sq_mem_L {a : G} (ha : a * f ^ 2 = f ^ 2 * a) : a * a ∈ L := by
  have hf2 : f ^ 2 ∈ L := H.four.sq_mem
  have haN : a ∈ centralizer ({f ^ 2} : Set G) := mem_centralizer_singleton_iff.2 ha
  rw [H.cent_eq] at haN
  rcases mem_or_exists_of_mem_sup_zpowers H.yy (y_conj_mem_LF H) haN with h | ⟨b, hb, rfl⟩
  · have := sq_mem_of_mem_sup_zpowers (hcom H) hf2 h
    rwa [sq] at this
  · obtain ⟨l, hl, i, rfl⟩ := exists_mul_zpow_of_mem_sup (hcom H) hb
    have hyb : y * (l * f ^ i) * y⁻¹ = (y * l * y⁻¹) * f⁻¹ ^ i := by
      rw [← H.yf, conj_zpow]; group
    have hl' : y * l * y⁻¹ ∈ L := (mem_normalizer_iff.1 (hyL H) l).1 hl
    have hc : Commute (y * l * y⁻¹) f := hcom H _ hl'
    have h1 : f ^ i * (y * l * y⁻¹) = (y * l * y⁻¹) * f ^ i := (hc.zpow_right i).eq.symm
    have hyy : y * y = 1 := H.yy
    have hcalc : l * f ^ i * y * (l * f ^ i * y) = l * (y * l * y⁻¹) := by
      calc l * f ^ i * y * (l * f ^ i * y)
          = l * f ^ i * (y * (l * f ^ i) * y⁻¹) * (y * y) := by group
        _ = l * f ^ i * ((y * l * y⁻¹) * f⁻¹ ^ i) := by rw [hyb, hyy, mul_one]
        _ = l * (y * l * y⁻¹) := by
            calc l * f ^ i * ((y * l * y⁻¹) * f⁻¹ ^ i)
                = l * (f ^ i * (y * l * y⁻¹)) * f⁻¹ ^ i := by group
              _ = l * ((y * l * y⁻¹) * f ^ i) * f⁻¹ ^ i := by rw [h1]
              _ = l * (y * l * y⁻¹) := by group
    rw [hcalc]
    exact L.mul_mem hl hl'

theorem comm_mem_L {e x : G} (he : e ∈ L ⊔ zpowers f) (hx : x * f ^ 2 = f ^ 2 * x) :
    e * x * e⁻¹ * x⁻¹ ∈ L := by
  have hf2 : f ^ 2 ∈ L := H.four.sq_mem
  obtain ⟨l, hl, i, rfl⟩ := exists_mul_zpow_of_mem_sup (hcom H) he
  have hxn := mem_normalizer_L H hx
  have hl' : x * l * x⁻¹ ∈ L := (mem_normalizer_iff.1 hxn l).1 hl
  have hxe : x * (l * f ^ i) * x⁻¹ = (x * l * x⁻¹) * (x * f * x⁻¹) ^ i := by
    rw [conj_zpow]; group
  have hrw : l * f ^ i * x * (l * f ^ i)⁻¹ * x⁻¹ = (l * f ^ i) * (x * (l * f ^ i) * x⁻¹)⁻¹ := by
    group
  rw [hrw, hxe]
  rcases conj_f_cases H.four hx with h | h
  · rw [h]
    have : l * f ^ i * ((x * l * x⁻¹) * f ^ i)⁻¹ = l * (x * l * x⁻¹)⁻¹ := by group
    rw [this]
    exact L.mul_mem hl (L.inv_mem hl')
  · rw [h]
    have : l * f ^ i * ((x * l * x⁻¹) * f⁻¹ ^ i)⁻¹ = l * (f ^ 2) ^ i * (x * l * x⁻¹)⁻¹ := by
      rw [show (f ^ 2) ^ i = f ^ (2 * i) by rw [← zpow_natCast, ← zpow_mul]; norm_cast]
      group
    rw [this]
    exact L.mul_mem (L.mul_mem hl (zpow_mem hf2 i)) (L.inv_mem hl')

theorem H1_cases {x : G} (hx : x ∈ L ⊔ zpowers y) : x ∈ L ∨ ∃ a ∈ L, x = a * y :=
  mem_or_exists_of_mem_sup_zpowers H.yy
    (fun a ha => (mem_normalizer_iff.1 (hyL H) a).1 ha) hx

theorem f_not_mem_H1 : f ∉ L ⊔ zpowers y := by
  intro hf
  rcases H1_cases H hf with h | ⟨a, ha, hfa⟩
  · rcases H.four.eq_one_or_eq_sq_of_mem h H.four.mem_cent with h1 | h1
    · have h2 : f = 1 := h1
      have := H.four.order
      rw [h2] at this
      simp at this
    · have h4 : orderOf f ∣ 1 := by
        apply orderOf_dvd_of_pow_eq_one
        have : f ^ 1 = f ^ 2 := by simpa using h1
        have h3 : f ^ 2 = f ^ 1 := this.symm
        calc f ^ 1 = f ^ 2 * f⁻¹ := by group
          _ = f ^ 1 * f⁻¹ := by rw [h3]
          _ = 1 := by group
      rw [H.four.order] at h4
      omega
  · apply H.y_not
    have : y = a⁻¹ * f := by
      calc y = a⁻¹ * (a * y) := by group
        _ = a⁻¹ * f := by rw [← hfa]
    rw [this]
    exact Subgroup.mul_mem_sup (L.inv_mem ha) (mem_zpowers f)

end Hyps

end SAU

end CFSG.EvenSporadicStandard.TwoHS
