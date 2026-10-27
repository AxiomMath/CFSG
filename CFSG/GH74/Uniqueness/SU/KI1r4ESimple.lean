module

public import CFSG.GH74.Uniqueness.SU.KI1r3Simple

public section

namespace CFSG.GH74.Uniqueness.SU.K.R3

open Subgroup CFSG CFSG.GH74.Uniqueness.SU
open CFSG.LocalCores

variable {H : Type} [Group H] [Finite H]

theorem Cfg.false_of_centerless_component {T : Sylow 2 H} {x : H} (h : Cfg H T x)
    {L : Subgroup H} (hL : IsComponent L)
    (hZL : ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z = 1) {u : H} (hu1 : u ≠ 1) (hu2 : u * u = 1)
    (hxu : x * u * x⁻¹ = u) (huC : u ∈ centralizer (L : Set H)) : False := by
  have hxx := h.mul_self_x
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hxL := h.component_normalized_of_centerless hL hZL
  obtain ⟨hLsimple, hLnab⟩ := component_simple_data hL hZL
  have := hLsimple
  have hLeven : Even (Nat.card ↥L) := CFSG.GH74.even_card_of_nonabelian_simple hLnab
  obtain ⟨v, hvL, hv1, hv2, hxv⟩ := exists_fixed_involution_of_even (X := L)
    (even_iff_two_dvd.mp hLeven) hxx hxL
  have huv : u * v = v * u := (Subgroup.mem_centralizer_iff.mp huC v hvL).symm
  have hnot : v ∉ zpowers u := by
    intro hmem
    rcases LemmaYAux.eq_one_or_eq_of_mem_zpowers hu2 hmem with h1 | h1
    · exact hv1 h1
    · apply hu1
      refine hZL u (by rw [← h1]; exact hvL) (fun l hl => ?_)
      exact (Subgroup.mem_centralizer_iff.mp huC l hl).symm
  obtain ⟨hEel, hEcard⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two (a := u) (y := v)
    (by rw [pow_two]; exact hu2) (by rw [pow_two]; exact hv2) hu1 hnot huv
  have hEx : ∀ e ∈ zpowers u ⊔ zpowers v, e * x = x * e := by
    have : zpowers u ⊔ zpowers v ≤ centralizer ({x} : Set H) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        symm
        calc x * u = x * u * x⁻¹ * x := by group
          _ = u * x := by rw [hxu]
      · rw [Subgroup.mem_centralizer_singleton_iff]
        symm
        calc x * v = x * v * x⁻¹ * x := by group
          _ = v * x := by rw [hxv]
    intro e he
    exact Subgroup.mem_centralizer_singleton_iff.mp (this he)
  have hxE : x ∉ zpowers u ⊔ zpowers v := by
    intro hx
    have hcomm' : ∀ a ∈ zpowers u, ∀ b ∈ zpowers v, a * b = b * a := by
      rintro a ⟨m, rfl⟩ b ⟨n, rfl⟩
      exact ((Commute.zpow_zpow (show Commute u v from huv) m n)).eq
    obtain ⟨a, ha, b, hb, hab⟩ := SU1.mem_sup_of_commute hcomm' hx
    rcases LemmaYAux.eq_one_or_eq_of_mem_zpowers hu2 ha with ha1 | ha1
    · rcases LemmaYAux.eq_one_or_eq_of_mem_zpowers hv2 hb with hb1 | hb1
      ·
        have := h.x2
        rw [ha1, hb1, one_mul] at hab
        rw [← hab, orderOf_one] at this
        omega
      ·
        rw [ha1, hb1, one_mul] at hab
        exact h.x_notMem_component hL (hab ▸ hvL)
    · rcases LemmaYAux.eq_one_or_eq_of_mem_zpowers hv2 hb with hb1 | hb1
      ·
        rw [ha1, hb1, mul_one] at hab
        apply h.component_not_inner_of_centerless hL hZL hxL
        refine ⟨1, one_mem _, fun l hl => ?_⟩
        have := Subgroup.mem_centralizer_iff.mp (hab ▸ huC) l hl
        calc x * l * x⁻¹ = l * x * x⁻¹ := by rw [← this]
          _ = 1 * l * 1⁻¹ := by group
      ·
        rw [ha1, hb1] at hab
        apply h.component_not_inner_of_centerless hL hZL hxL
        refine ⟨v, hvL, fun l hl => ?_⟩
        rw [← hab]
        calc u * v * l * (u * v)⁻¹ = u * (v * l * v⁻¹) * u⁻¹ := by group
          _ = v * l * v⁻¹ := by
            have hvl : v * l * v⁻¹ ∈ L := L.mul_mem (L.mul_mem hvL hl) (L.inv_mem hvL)
            have := (Subgroup.mem_centralizer_iff.mp huC _ hvl)
            calc u * (v * l * v⁻¹) * u⁻¹ = (v * l * v⁻¹) * u * u⁻¹ := by rw [this]
              _ = v * l * v⁻¹ := by group
  obtain ⟨hel, hc8⟩ := sup_zpowers_ge_eight hEel (by rw [hEcard]; norm_num) hxx hEx hxE
  exact h.no_E8 hel hc8 1 (by simpa using Subgroup.mem_sup_right (mem_zpowers x))

theorem Cfg.component_center_nontrivial {T : Sylow 2 H} {x : H} (h : Cfg H T x) {u : H}
    (hu1 : u ≠ 1) (hu2 : u * u = 1) (hxu : x * u * x⁻¹ = u)
    (huE : ∀ g ∈ layer H, u * g = g * u) {K : Subgroup H} (hK : IsComponent K) :
    ∃ z ∈ K, (∀ k ∈ K, z * k = k * z) ∧ z ≠ 1 := by
  by_contra hno
  push Not at hno
  refine h.false_of_centerless_component hK hno hu1 hu2 hxu ?_
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact (huE k (le_sSup (show K ∈ {K : Subgroup H | IsComponent K} from hK) hk)).symm

end CFSG.GH74.Uniqueness.SU.K.R3
