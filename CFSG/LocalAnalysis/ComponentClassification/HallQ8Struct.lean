module

public import CFSG.LocalAnalysis.ComponentClassification.HallQ8Norm

public section

namespace CFSG.ComponentClassification.Foote5.HallGen

open CFSG Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {c : G}

namespace Q8Cfg

theorem four_dvd_add_one (h : Q8Cfg D c) {w : G} {j : ℤ} (hj : w * c * w⁻¹ = c ^ j)
    (hwy : w * cy c * w⁻¹ = (cy c)⁻¹) : (4 : ℤ) ∣ j + 1 := by
  obtain ⟨q, hq⟩ := h.h4
  have hq0 : 0 < q := by
    have := h.k_pos
    omega
  have hq4 : orderOf c / 4 = q := by omega
  have h1 : w * cy c * w⁻¹ = c ^ (j * (q : ℤ)) := by
    rw [cy, hq4, ← conj_pow, hj, ← zpow_natCast, ← zpow_mul]
  have h2 : c ^ ((j + 1) * (q : ℤ)) = 1 := by
    rw [add_mul, zpow_add, ← h1, hwy, one_mul, cy, hq4, zpow_natCast, inv_mul_cancel]
  have h3 := orderOf_dvd_iff_zpow_eq_one.mpr h2
  rw [hq] at h3
  push_cast at h3
  exact Int.dvd_of_mul_dvd_mul_right (by exact_mod_cast hq0.ne') h3

theorem struct_inv (h : Q8Cfg D c) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hDS : D ≤ S)
    {y' : G} (hyS : y' ∈ S) (hy : Th c y') (hyD : y' ∉ D) {u : G} (hu : u ∈ D)
    (huK : u ∉ zpowers c) {l : ℤ} (hl : y' * u * y'⁻¹ = c ^ l * u) :
    y' * c * y'⁻¹ = c⁻¹ ∧ Odd l := by
  have hSN := h.le_normalizer hS.isPGroup hDS
  have hyN : y' ∈ normalizer (D : Set G) := hSN hyS
  obtain ⟨j, hj⟩ := conj_c h hyN
  have hy2 : y' * y' = cz c := Th_sq h hy
  have hnc : ¬ y' * cy c = cy c * y' := fun hc => hyD (c2 h hS hDS hyS hy hc)
  have hyinv : y' * cy c * y'⁻¹ = (cy c)⁻¹ := by
    have hmem : y' * cy c * y'⁻¹ ∈ zpowers c := conj_K h hyN (cy_mem h)
    have hsq : (y' * cy c * y'⁻¹) * (y' * cy c * y'⁻¹) = cz c := by
      rw [show y' * cy c * y'⁻¹ * (y' * cy c * y'⁻¹) = y' * (cy c * cy c) * y'⁻¹ by group,
        cy_mul_cy h]
      have := h.central y'
      calc y' * cz c * y'⁻¹ = cz c * y' * y'⁻¹ := by rw [this]
        _ = cz c := by group
    rcases eq_cy_or_inv h hmem hsq with e | e
    · exact absurd (by rw [mul_inv_eq_iff_eq_mul] at e; exact e) hnc
    · exact e
  have h4 := four_dvd_add_one h hj hyinv
  have hlj : c ^ (l * (j + 1)) = 1 := by
    have hz : (y' * y') * u * (y' * y')⁻¹ = u := by
      rw [hy2]
      have := h.central u
      calc cz c * u * (cz c)⁻¹ = u * cz c * (cz c)⁻¹ := by rw [← this]
        _ = u := by group
    have hc : (y' * y') * u * (y' * y')⁻¹ = c ^ (j * l) * (c ^ l * u) := by
      calc (y' * y') * u * (y' * y')⁻¹ = y' * (y' * u * y'⁻¹) * y'⁻¹ := by group
        _ = y' * (c ^ l * u) * y'⁻¹ := by rw [hl]
        _ = (y' * c ^ l * y'⁻¹) * (y' * u * y'⁻¹) := by group
        _ = c ^ (j * l) * (c ^ l * u) := by rw [← conj_zpow, hj, ← zpow_mul, hl]
    have h1 : c ^ (j * l + l) * u = u := by
      rw [zpow_add, mul_assoc, ← hc, hz]
    have h2 : c ^ (j * l + l) = 1 := by
      have := mul_right_cancel (h1.trans (one_mul u).symm)
      exact this
    rw [← h2]
    congr 1
    ring
  have hlodd : Odd l := by
    by_contra hne
    rw [Int.not_odd_iff_even] at hne
    obtain ⟨l', hl'⟩ := hne
    obtain ⟨b, hb⟩ := h4
    set o₂ : ℤ := 2 * b - 1 with ho₂
    have hjo : j - 1 = 2 * o₂ := by omega
    have hodd : Odd o₂ := ⟨b - 1, by omega⟩
    have hx : c ^ (2 : ℤ) ∈ zpowers (c ^ (j - 1)) := by
      have := h.mem_zpowers_zpow_odd_K (x := c ^ (2 : ℤ)) (zpow_mem (mem_zpowers c) _) hodd
      rwa [← zpow_mul, ← hjo] at this
    have hcl : c ^ l ∈ zpowers (c ^ (j - 1)) := by
      have : c ^ l = (c ^ (2 : ℤ)) ^ l' := by rw [← zpow_mul, hl']; congr 1; ring
      rw [this]
      exact zpow_mem hx l'
    obtain ⟨i', hi'⟩ := mem_zpowers_iff.mp hcl
    have h2 : c ^ ((j - 1) * (-i') + l) = 1 := by
      rw [zpow_add, mul_neg, zpow_neg, zpow_mul, hi', inv_mul_cancel]
    have h3 : c ^ (j * (-i') + l) = c ^ (-i') := by
      have : j * (-i') + l = ((j - 1) * (-i') + l) + (-i') := by ring
      rw [this, zpow_add, h2, one_mul]
    have hcomm : y' * (c ^ (-i') * u) * y'⁻¹ = c ^ (-i') * u := by
      calc y' * (c ^ (-i') * u) * y'⁻¹ = (y' * c ^ (-i') * y'⁻¹) * (y' * u * y'⁻¹) := by group
        _ = c ^ (j * (-i')) * (c ^ l * u) := by rw [← conj_zpow, hj, ← zpow_mul, hl]
        _ = c ^ (j * (-i') + l) * u := by rw [zpow_add, mul_assoc]
        _ = c ^ (-i') * u := by rw [h3]
    have hdD : c ^ (-i') * u ∈ D := mul_mem (zpow_mem h.mem _) hu
    have hdK : c ^ (-i') * u ∉ zpowers c := fun hK => huK (by
      have := mul_mem (inv_mem (zpow_mem (mem_zpowers c) (-i'))) hK
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this)
    have hd2 : (c ^ (-i') * u) * (c ^ (-i') * u) = 1 := (refl_data h hdD hdK).1
    obtain ⟨k, hk⟩ := hy
    have hc1 := c1 h hS hDS (d := c ^ (-i') * u) (g := 1) (k := k) hdD hd2 (by
      rw [inv_one, one_mul, mul_one, hk]
      have := mul_inv_eq_iff_eq_mul.mp hcomm
      exact this.symm)
    rcases hc1 with e | e
    · exact hdK (by rw [e]; exact one_mem _)
    · exact hdK (by rw [e]; exact cz_mem' h)
  refine ⟨?_, hlodd⟩
  have h5 : (c ^ (j + 1)) ^ l = 1 := by rw [← zpow_mul, mul_comm]; exact hlj
  have h6 : c ^ (j + 1) = 1 :=
    eq_one_of_zpow_odd_K h (zpow_mem (mem_zpowers c) _) hlodd h5
  rw [hj]
  rw [zpow_add_one] at h6
  exact mul_eq_one_iff_eq_inv.mp h6

end Q8Cfg

section Algebra

variable {y' u : G} {l : ℤ}

structure Yrel (c u y' : G) (l : ℤ) : Prop where
  inv : y' * c * y'⁻¹ = c⁻¹
  refl : y' * u * y'⁻¹ = c ^ l * u
  sq : y' * y' = cz c
  usq : u * u = 1
  uc : u * c * u⁻¹ = c⁻¹

namespace Yrel

variable (r : Yrel c u y' l)
include r

omit [Finite G] in
theorem conj_zpow_c (i : ℤ) : y' * c ^ i * y'⁻¹ = c ^ (-i) := by
  rw [← conj_zpow, r.inv, inv_zpow']

omit [Finite G] in
theorem inv_conj_zpow_c (i : ℤ) : y'⁻¹ * c ^ i * y' = c ^ (-i) := by
  have := r.conj_zpow_c (-i)
  rw [neg_neg] at this
  calc y'⁻¹ * c ^ i * y' = y'⁻¹ * (y' * c ^ (-i) * y'⁻¹) * y' := by rw [this]
    _ = c ^ (-i) := by group

omit [Finite G] in
theorem u_conj_zpow_c (i : ℤ) : u * c ^ i * u⁻¹ = c ^ (-i) := by
  rw [← conj_zpow, r.uc, inv_zpow']

omit [Finite G] in
theorem inv_refl : y'⁻¹ * u * y' = c ^ l * u := by
  have h1 : u = c ^ (-l) * (y'⁻¹ * u * y') := by
    calc u = y'⁻¹ * (y' * u * y'⁻¹) * y' := by group
      _ = y'⁻¹ * (c ^ l * u) * y' := by rw [r.refl]
      _ = (y'⁻¹ * c ^ l * y') * (y'⁻¹ * u * y') := by group
      _ = c ^ (-l) * (y'⁻¹ * u * y') := by rw [r.inv_conj_zpow_c]
  have h2 : y'⁻¹ * u * y' = c ^ l * u := by
    calc y'⁻¹ * u * y' = c ^ l * (c ^ (-l) * (y'⁻¹ * u * y')) := by group
      _ = c ^ l * u := by rw [← h1]
  exact h2

omit [Finite G] in
theorem u_conj_y : u * y' * u⁻¹ = y' * c ^ l := by
  calc u * y' * u⁻¹ = y' * (y'⁻¹ * u * y') * u⁻¹ := by group
    _ = y' * (c ^ l * u) * u⁻¹ := by rw [r.inv_refl]
    _ = y' * c ^ l := by group

omit [Finite G] in
theorem y_c_y (i : ℤ) : y' * c ^ i * y' = cz c * c ^ (-i) := by
  calc y' * c ^ i * y' = (y' * y') * (y'⁻¹ * c ^ i * y') := by group
    _ = cz c * c ^ (-i) := by rw [r.sq, r.inv_conj_zpow_c]

omit [Finite G] in
theorem sq_y_c (i : ℤ) : (y' * c ^ i) * (y' * c ^ i) = cz c := by
  calc (y' * c ^ i) * (y' * c ^ i) = (y' * c ^ i * y') * c ^ i := by group
    _ = cz c := by rw [r.y_c_y]; group

omit [Finite G] in
theorem sq_y_c_u (i : ℤ) : (y' * c ^ i * u) * (y' * c ^ i * u) = cz c * c ^ (l - 2 * i) := by
  calc (y' * c ^ i * u) * (y' * c ^ i * u)
      = y' * c ^ i * (u * y' * u⁻¹) * (u * c ^ i * u⁻¹) * (u * u) := by group
    _ = y' * c ^ i * (y' * c ^ l) * c ^ (-i) * 1 := by rw [r.u_conj_y, r.u_conj_zpow_c, r.usq]
    _ = (y' * c ^ i * y') * c ^ (l - i) := by group
    _ = cz c * c ^ (l - 2 * i) := by
        rw [r.y_c_y, mul_assoc, ← zpow_add]
        congr 2
        ring

omit [Finite G] in
theorem y_c_eq (a : ℤ) : y' * c ^ (2 * a) = (c ^ a)⁻¹ * y' * c ^ a := by
  have h1 := r.inv_conj_zpow_c (-a)
  rw [neg_neg] at h1
  calc y' * c ^ (2 * a) = y' * c ^ a * c ^ a := by rw [two_mul, zpow_add, mul_assoc]
    _ = (c ^ a)⁻¹ * y' * c ^ a := by
        have : y' * c ^ a = (c ^ a)⁻¹ * y' := by
          calc y' * c ^ a = (y' * c ^ a * y'⁻¹) * y' := by group
            _ = (c ^ a)⁻¹ * y' := by rw [r.conj_zpow_c, zpow_neg]
        rw [this]

end Yrel

end Algebra

end CFSG.ComponentClassification.Foote5.HallGen
