module

public import CFSG.LocalAnalysis.EvenSmallLie.OddTranspAlt.Component
public import CFSG.LocalAnalysis.EvenSmallLie.OddTranspAlt.Isolated

public section

namespace CFSG.EvenSmallLie.OddTranspAlt

open Equiv Equiv.Perm CFSG.Open

namespace Cfg

variable {G : Type} [Group G] [Finite G] {n : ℕ} (c : Cfg G n) {x y f d h : G}

omit [Finite G] in
theorem Dt_subset_cls (hx : x ∈ c.Dt) : x ∈ cls c.t := hx.1

omit [Finite G] in
private theorem φ_conj_of_mem_N (hy : y ∈ c.N) (hx : x ∈ c.N) :
    c.φ (y * x * y⁻¹) = c.φ y * c.φ x * (c.φ y)⁻¹ := by
  rw [c.φ_mul (mul_mem hy hx) (inv_mem hy), c.φ_mul hy hx, c.φ_inv hy]

omit [Finite G] in
private theorem conj_mem_Dt_of_commute (hx : x ∈ c.Dt) (hy : c.t * y = y * c.t) :
    y * x * y⁻¹ ∈ c.Dt := by
  have hty : Commute c.t y := hy
  refine ⟨conj_mem_cls hx.1 y, fun heq => hx.2.1 ?_,
    ((hty.mul_right hx.2.2).mul_right hty.inv_right).eq⟩
  calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
    _ = c.t := by rw [heq, mul_assoc, hy, inv_mul_cancel_left]

private theorem mul_conj_mem_Y (hx : x ∈ c.Dt) (hy : y ∈ c.Y) :
    x * (y * x * y⁻¹) ∈ c.Y ∧
      orderOf (x * (y * x * y⁻¹)) = orderOf (c.φ x * (c.ι y * c.φ x * (c.ι y)⁻¹)) := by
  have hxN := c.Dt_subset_N hx
  have hyN := c.Y_le_N hy
  have hmem : x * (y * x * y⁻¹) ∈ c.Y := by
    have heq : x * (y * x * y⁻¹) = x * y * x⁻¹ * y⁻¹ := by
      rw [c.inv_of_mem_cls hx.1]; simp only [mul_assoc]
    rw [heq]
    exact mul_mem (c.conj_mem_Y hxN hy) (inv_mem hy)
  refine ⟨hmem, ?_⟩
  rw [← c.orderOf_ι hmem, ← c.φ_of_mem_Y hmem,
    c.φ_mul hxN (mul_mem (mul_mem hyN hxN) (inv_mem hyN)), c.φ_conj_of_mem_N hyN hxN,
    c.φ_of_mem_Y hy]

theorem φ_isSwap (hx : x ∈ c.Dt) : (c.φ x).IsSwap := by
  have hxN := c.Dt_subset_N hx
  have h2 : c.φ x * c.φ x = 1 := by
    rw [← c.φ_mul hxN hxN, c.mul_self_of_mem_cls hx.1, c.φ_one]
  have h1 : c.φ x ≠ 1 := fun h1 => c.k2 x hx.1 hx.2.1 hx.2.2
    (Subgroup.mem_centralizer_iff.2 fun z hz => (c.commute_of_φ_eq_one hxN h1 z hz).symm)
  by_contra hsw
  obtain ⟨u, hu, hev, hgt⟩ := exists_alt_comm_order_even c.hn h2 h1 hsw
  obtain ⟨y, hy, rfl⟩ := c.exists_ι_eq hu
  rw [← (c.mul_conj_mem_Y hx hy).2] at hev hgt
  rcases c.ot_cls hx.1 (conj_mem_cls hx.1 y) with hodd | h2'
  · exact Nat.not_even_iff_odd.2 hodd hev
  · omega

omit [Finite G] in
theorem conj_Y_mem_Dt (hy : y ∈ c.Y) (hx : x ∈ c.Dt) : y * x * y⁻¹ ∈ c.Dt :=
  c.conj_mem_Dt_of_commute hx (c.Y_commute_t hy)

theorem φ_conj_Y (hy : y ∈ c.Y) (hx : x ∈ c.Dt) :
    c.φ (y * x * y⁻¹) = c.ι y * c.φ x * (c.ι y)⁻¹ := by
  rw [c.φ_conj_of_mem_N (c.Y_le_N hy) (c.Dt_subset_N hx), c.φ_of_mem_Y hy]

theorem φ_injOn : Set.InjOn c.φ c.Dt := by
  intro e he f hf hef
  have heN := c.Dt_subset_N he
  have hfN := c.Dt_subset_N hf
  have hτ := c.φ_isSwap he
  have hkY : ∀ z ∈ c.Y, e * f * z = z * (e * f) := c.commute_of_φ_eq_one (mul_mem heN hfN)
    (by rw [c.φ_mul heN hfN, ← hef, isSwap_mul_self hτ])
  have hid : ∀ y ∈ c.Y, e * (y * f * y⁻¹) = e * (y * e * y⁻¹) * (e * f) := by
    intro y hy
    calc e * (y * f * y⁻¹) = e * y * (e * e) * f * y⁻¹ := by
          rw [c.mul_self_of_mem_cls he.1]; group
      _ = e * y * e * (e * f * y⁻¹) := by group
      _ = e * (y * e * y⁻¹) * (e * f) := by rw [hkY y⁻¹ (inv_mem hy)]; group
  have main : ∀ u ∈ alternatingGroup (Fin n),
      (orderOf (c.φ e * (u * c.φ e * u⁻¹))).Coprime (orderOf (e * f)) →
      Odd (orderOf (c.φ e * (u * c.φ e * u⁻¹)) * orderOf (e * f)) ∨
        orderOf (c.φ e * (u * c.φ e * u⁻¹)) * orderOf (e * f) = 2 := by
    intro u hu hcop
    obtain ⟨y, hy, rfl⟩ := c.exists_ι_eq hu
    obtain ⟨hw, hwo⟩ := c.mul_conj_mem_Y he hy
    rw [← hwo] at hcop ⊢
    rw [← Commute.orderOf_mul_eq_mul_orderOf_of_coprime (hkY _ hw).symm hcop, ← hid y hy]
    exact c.ot_cls he.1 (conj_mem_cls hf.1 y)
  by_contra hne
  have hk1 : e * f ≠ 1 := fun h1 =>
    hne ((c.inv_of_mem_cls he.1).symm.trans (inv_eq_of_mul_eq_one_right h1))
  have h4 : 4 ≤ n := by have := c.hn; omega
  rcases c.ot_cls he.1 hf.1 with hodd | h2
  · obtain ⟨u, hu, hu2⟩ := exists_alt_comm_order_two h4 hτ
    have hm := main u hu (by rw [hu2]; exact Nat.coprime_two_left.2 hodd)
    rw [hu2] at hm
    rcases hm with hm | hm
    · exact Nat.not_even_iff_odd.2 hm (even_two_mul _)
    · exact hk1 (orderOf_eq_one_iff.1 (by omega))
  · obtain ⟨u, hu, hu3⟩ := exists_alt_comm_order_three h4 hτ
    have hm := main u hu (by rw [hu3, h2]; decide)
    rw [hu3, h2] at hm
    rcases hm with hm | hm
    · exact absurd hm (by decide)
    · omega

theorem exists_Dt_φ_eq {σ : Perm (Fin n)} (hσ : σ.IsSwap) : ∃ x ∈ c.Dt, c.φ x = σ := by
  obtain ⟨e, he⟩ := c.Dt_nonempty
  obtain ⟨u, hu, rfl⟩ := exists_alt_conj_swap (by have := c.hn; omega) (c.φ_isSwap he) hσ
  obtain ⟨y, hy, rfl⟩ := c.exists_ι_eq hu
  exact ⟨y * e * y⁻¹, c.conj_Y_mem_Dt hy he, c.φ_conj_Y hy he⟩

theorem mul_mem_Y_of_Dt (hx : x ∈ c.Dt) (hy : y ∈ c.Dt) :
    x * y ∈ c.Y ∧ c.ι (x * y) = c.φ x * c.φ y := by
  obtain ⟨u, hu, hxy⟩ :=
    exists_alt_conj_swap (by have := c.hn; omega) (c.φ_isSwap hx) (c.φ_isSwap hy)
  obtain ⟨z, hz, rfl⟩ := c.exists_ι_eq hu
  have hzy : z * x * z⁻¹ = y :=
    c.φ_injOn (c.conj_Y_mem_Dt hz hx) hy (by rw [c.φ_conj_Y hz hx, hxy])
  have hmem : x * y ∈ c.Y := hzy ▸ (c.mul_conj_mem_Y hx hz).1
  exact ⟨hmem, (c.φ_of_mem_Y hmem).symm.trans (c.φ_mul (c.Dt_subset_N hx) (c.Dt_subset_N hy))⟩

theorem comm_iff_Dt (hx : x ∈ c.Dt) (hy : y ∈ c.Dt) :
    x * y = y * x ↔ c.φ x * c.φ y = c.φ y * c.φ x := by
  have hxN := c.Dt_subset_N hx
  have hyN := c.Dt_subset_N hy
  refine ⟨fun h => by rw [← c.φ_mul hxN hyN, ← c.φ_mul hyN hxN, h], fun h => ?_⟩
  obtain ⟨hxy, hixy⟩ := c.mul_mem_Y_of_Dt hx hy
  obtain ⟨hyx, hiyx⟩ := c.mul_mem_Y_of_Dt hy hx
  exact c.ι_injOn hxy hyx ((hixy.trans h).trans hiyx.symm)

theorem orderOf_mul_Dt (hx : x ∈ c.Dt) (hy : y ∈ c.Dt) :
    orderOf (x * y) = orderOf (c.φ x * c.φ y) := by
  obtain ⟨hxy, hixy⟩ := c.mul_mem_Y_of_Dt hx hy
  rw [← c.orderOf_ι hxy, hixy]

theorem comm_of_disjoint (hx : x ∈ c.Dt) (hy : y ∈ c.Dt) (hd : (c.φ x).Disjoint (c.φ y)) :
    x * y = y * x :=
  (c.comm_iff_Dt hx hy).2 ((isSwap_commute_iff (c.φ_isSwap hx) (c.φ_isSwap hy)).2 (Or.inr hd))

theorem disjoint_of_comm (hx : x ∈ c.Dt) (hy : y ∈ c.Dt) (hne : x ≠ y) (hc : x * y = y * x) :
    (c.φ x).Disjoint (c.φ y) :=
  ((isSwap_commute_iff (c.φ_isSwap hx) (c.φ_isSwap hy)).1
    ((c.comm_iff_Dt hx hy).1 hc)).resolve_left fun h => hne (c.φ_injOn hx hy h)

theorem orderOf_mul_Dt_three (hx : x ∈ c.Dt) (hy : y ∈ c.Dt) (hnc : x * y ≠ y * x) :
    orderOf (x * y) = 3 := by
  have hsw := isSwap_commute_iff (c.φ_isSwap hx) (c.φ_isSwap hy)
  rw [c.orderOf_mul_Dt hx hy]
  refine isSwap_orderOf_mul_three (c.φ_isSwap hx) (c.φ_isSwap hy) (fun h => ?_) (fun h => ?_)
  · exact hnc ((c.comm_iff_Dt hx hy).2 (hsw.2 (Or.inl h)))
  · exact hnc ((c.comm_iff_Dt hx hy).2 (hsw.2 (Or.inr h)))

omit [Finite G] in
theorem conj_Dt_mem_Dt (hx : x ∈ c.Dt) (hy : y ∈ c.Dt) : y * x * y⁻¹ ∈ c.Dt :=
  c.conj_mem_Dt_of_commute hx hy.2.2

theorem φ_conj_Dt (hx : x ∈ c.Dt) (hy : y ∈ c.Dt) :
    c.φ (y * x * y⁻¹) = c.φ y * c.φ x * (c.φ y)⁻¹ :=
  c.φ_conj_of_mem_N (c.Dt_subset_N hy) (c.Dt_subset_N hx)

omit [Finite G] in
theorem Dloc_conj_iff : x ∈ c.Dloc d ↔ h * x * h⁻¹ ∈ c.Dloc (h * d * h⁻¹) := by
  have hcls : h * x * h⁻¹ ∈ cls c.t → x ∈ cls c.t := fun hx => by
    have hx' := conj_mem_cls hx h⁻¹
    rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at hx'
  have hne : h * x * h⁻¹ = h * d * h⁻¹ ↔ x = d := by rw [mul_left_inj, mul_right_inj]
  have hcomm : h * d * h⁻¹ * (h * x * h⁻¹) = h * x * h⁻¹ * (h * d * h⁻¹) ↔ d * x = x * d := by
    rw [show h * d * h⁻¹ * (h * x * h⁻¹) = h * (d * x) * h⁻¹ by group,
      show h * x * h⁻¹ * (h * d * h⁻¹) = h * (x * d) * h⁻¹ by group, mul_left_inj, mul_right_inj]
  exact ⟨fun hx => ⟨conj_mem_cls hx.1 h, fun he => hx.2.1 (hne.1 he), hcomm.2 hx.2.2⟩,
    fun hx => ⟨hcls hx.1, fun he => hx.2.1 (hne.2 he), hcomm.1 hx.2.2⟩⟩

theorem orderOf_mul_Dloc_three (hf : f ∈ cls c.t) (hx : x ∈ c.Dloc f) (hy : y ∈ c.Dloc f)
    (hnc : x * y ≠ y * x) : orderOf (x * y) = 3 := by
  obtain ⟨e, rfl⟩ := exists_conj_of_mem_cls hf
  have ht : e⁻¹ * (e * c.t * e⁻¹) * e⁻¹⁻¹ = c.t := by group
  have hx' := (c.Dloc_conj_iff (h := e⁻¹)).1 hx
  have hy' := (c.Dloc_conj_iff (h := e⁻¹)).1 hy
  rw [ht] at hx' hy'
  rw [← MulEquiv.orderOf_eq (MulAut.conj e⁻¹) (x * y)]
  simp only [map_mul, MulAut.conj_apply]
  refine c.orderOf_mul_Dt_three hx' hy' fun heq => hnc ((MulAut.conj e⁻¹).injective ?_)
  simpa only [map_mul, MulAut.conj_apply] using heq

end Cfg

end CFSG.EvenSmallLie.OddTranspAlt
