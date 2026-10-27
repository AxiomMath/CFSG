module

public import CFSG.CGT.Foote81L6.TStruct.ElemBound

public section

namespace CFSG.CGT.Foote81L6.TStruct

open Subgroup DihedralGroup

variable {G : Type*} [Group G]

theorem exists_mul_of_mulEquiv_dihedral {H : Subgroup G} {k : ℕ} (e : H ≃* DihedralGroup k)
    {y : G} (hy : y ∈ H) :
    ∃ x₁ ∈ H, ∃ x₂ ∈ H, x₁ * x₁ = 1 ∧ x₂ * x₂ = 1 ∧ y = x₁ * x₂ := by
  have hsr : ∀ i, (e.symm (sr i) : G) * e.symm (sr i) = 1 := fun i =>
    congrArg Subtype.val (show e.symm (sr i) * e.symm (sr i) = 1 by
      rw [← map_mul, sr_mul_self, map_one])
  rcases h : e ⟨y, hy⟩ with i | i
  · refine ⟨_, (e.symm (sr 0)).2, _, (e.symm (sr i)).2, hsr 0, hsr i, ?_⟩
    have h1 : e.symm (sr 0) * e.symm (sr i) = ⟨y, hy⟩ := by
      rw [← map_mul, sr_mul_sr, sub_zero, ← h, MulEquiv.symm_apply_apply]
    exact (congrArg Subtype.val h1).symm
  · refine ⟨y, hy, 1, one_mem _, ?_, mul_one 1, (mul_one y).symm⟩
    have h1 : (⟨y, hy⟩ : H) * ⟨y, hy⟩ = 1 :=
      e.injective (by rw [map_mul, h, sr_mul_self, map_one])
    exact congrArg Subtype.val h1

theorem exists_four_of_mulEquiv_dihedral {H : Subgroup G} {k : ℕ} (hk : 1 ≤ k)
    (e : H ≃* DihedralGroup (2 ^ k)) {x : G} (hx : x ∈ H) (hx2 : x * x = 1) :
    ∃ V : Subgroup G, V ≤ H ∧ (∀ v ∈ V, v * v = 1) ∧ Nat.card V = 4 ∧ x ∈ V := by
  have hzr : zc k = r ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k)) := by
    rw [← rho_pow hk, r_pow, one_mul]
  have hzH : (e.symm (zc k) : G) ∈ H := (e.symm (zc k)).2
  have hz2 : (e.symm (zc k) : G) * e.symm (zc k) = 1 :=
    congrArg Subtype.val (show e.symm (zc k) * e.symm (zc k) = 1 by
      rw [← map_mul, zc_mul_self hk, map_one])
  have hz1 : (e.symm (zc k) : G) ≠ 1 := by
    intro h
    have h' : e.symm (zc k) = e.symm 1 := by rw [map_one]; exact Subtype.ext h
    exact zc_ne_one hk (e.symm.injective h')
  have hzc : ∀ y ∈ H, y * e.symm (zc k) = e.symm (zc k) * y := by
    intro y hy
    have h := congrArg e.symm (zc_comm hk (e ⟨y, hy⟩))
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h
    exact congrArg Subtype.val h
  have hfour : ∀ v ∈ H, v * v = 1 → v ≠ 1 → v ≠ (e.symm (zc k) : G) →
      ∃ V : Subgroup G, V ≤ H ∧ (∀ g ∈ V, g * g = 1) ∧ Nat.card V = 4 ∧
        v ∈ V ∧ (e.symm (zc k) : G) ∈ V := by
    intro v hv hv2 hv1 hvz
    refine ⟨zpowers v ⊔ zpowers (e.symm (zc k) : G), sup_le (zpowers_le.2 hv) (zpowers_le.2 hzH),
      fun g hg => mul_self_of_mem_zpowers_sup_zpowers hv2 hz2 (hzc v hv) hg,
      card_zpowers_sup_zpowers hv2 hz2 hv1 hz1 hvz (hzc v hv),
      mem_sup_left (mem_zpowers v), mem_sup_right (mem_zpowers _)⟩
  by_cases hxz : x = 1 ∨ x = (e.symm (zc k) : G)
  · have hs2 : (e.symm (sr 0) : G) * e.symm (sr 0) = 1 :=
      congrArg Subtype.val (show e.symm (sr 0) * e.symm (sr 0) = 1 by
        rw [← map_mul, sr_mul_self, map_one])
    have hs1 : (e.symm (sr 0) : G) ≠ 1 := by
      intro h
      have h' : e.symm (sr 0) = e.symm 1 := by rw [map_one]; exact Subtype.ext h
      have h'' := e.symm.injective h'
      rw [one_def] at h''
      cases h''
    have hsz : (e.symm (sr 0) : G) ≠ e.symm (zc k) := by
      intro h
      have h'' := e.symm.injective (Subtype.ext h)
      rw [hzr] at h''
      cases h''
    obtain ⟨V, hVH, hV2, hV4, -, hzV⟩ := hfour _ (e.symm (sr 0)).2 hs2 hs1 hsz
    refine ⟨V, hVH, hV2, hV4, ?_⟩
    rcases hxz with rfl | rfl
    · exact one_mem _
    · exact hzV
  · rw [not_or] at hxz
    obtain ⟨V, hVH, hV2, hV4, hxV, -⟩ := hfour x hx hx2 hxz.1 hxz.2
    exact ⟨V, hVH, hV2, hV4, hxV⟩

theorem le_of_forall_four_le {H X : Subgroup G} {k : ℕ} (hk : 1 ≤ k)
    (e : H ≃* DihedralGroup (2 ^ k))
    (hX : ∀ V : Subgroup G, V ≤ H → (∀ v ∈ V, v * v = 1) → Nat.card V = 4 → V ≤ X) :
    H ≤ X := by
  intro y hy
  obtain ⟨x₁, h₁, x₂, h₂, hx₁, hx₂, rfl⟩ := exists_mul_of_mulEquiv_dihedral e hy
  obtain ⟨V₁, hV₁H, hV₁2, hV₁4, hxV₁⟩ := exists_four_of_mulEquiv_dihedral hk e h₁ hx₁
  obtain ⟨V₂, hV₂H, hV₂2, hV₂4, hxV₂⟩ := exists_four_of_mulEquiv_dihedral hk e h₂ hx₂
  exact mul_mem (hX V₁ hV₁H hV₁2 hV₁4 hxV₁) (hX V₂ hV₂H hV₂2 hV₂4 hxV₂)

theorem conj_of_not_mem_of_index_two {k : ℕ} (hk : 2 ≤ k)
    {H : Subgroup (DihedralGroup (2 ^ k))} (hH : H.index = 2) (hr : r 1 ∉ H)
    {u w : DihedralGroup (2 ^ k)} (hu : u ∉ H) (hw : w ∉ H) (hu2 : u * u = 1)
    (hw2 : w * w = 1) : ∃ h ∈ H, h * u * h⁻¹ = w := by
  obtain ⟨c₀, rfl⟩ : ∃ c₀, k = c₀ + 1 + 1 := ⟨k - 2, by omega⟩
  haveI : NeZero (2 ^ (c₀ + 1 + 1)) := ⟨by positivity⟩
  have hr2 : r 2 ∈ H := by
    have := mul_self_mem_of_index_two hH (r 1)
    rwa [r_mul_r, one_add_one_eq_two] at this
  have heven : ∀ c : ℕ, r (2 * (c : ZMod (2 ^ (c₀ + 1 + 1)))) ∈ H := fun c => by
    have := pow_mem hr2 c
    rwa [r_pow] at this
  have hrot : ∀ d : ZMod (2 ^ (c₀ + 1 + 1)), r d ∈ H →
      ∃ c : ℕ, d = 2 * (c : ZMod (2 ^ (c₀ + 1 + 1))) := by
    intro d hd
    rcases Nat.even_or_odd d.val with ⟨c, hc⟩ | ⟨c, hc⟩
    · refine ⟨c, ?_⟩
      rw [← ZMod.natCast_zmod_val d, hc]
      push_cast
      ring
    · exfalso
      apply hr
      have h1 : r 1 = (r (2 * (c : ZMod (2 ^ (c₀ + 1 + 1)))))⁻¹ * r d := by
        rw [inv_r, r_mul_r]
        congr 1
        rw [← ZMod.natCast_zmod_val d, hc]
        push_cast
        ring
      rw [h1]
      exact mul_mem (inv_mem (heven c)) hd
  have hrefl : ∀ v : DihedralGroup (2 ^ (c₀ + 1 + 1)), v ∉ H → v * v = 1 → ∃ p, v = sr p := by
    intro v hv hv2
    rcases v with i | p
    · exfalso
      apply hv
      rw [r_mul_r, one_def, r.injEq] at hv2
      rcases eq_zero_or_half hv2 with h0 | hh
      · rw [h0, ← one_def]
        exact one_mem _
      · have e : ((2 ^ (c₀ + 1) : ℕ) : ZMod (2 ^ (c₀ + 1 + 1))) =
            2 * ((2 ^ c₀ : ℕ) : ZMod (2 ^ (c₀ + 1 + 1))) := by
          push_cast
          ring
        rw [hh, e]
        exact heven _
    · exact ⟨p, rfl⟩
  obtain ⟨p, rfl⟩ := hrefl u hu hu2
  obtain ⟨q, rfl⟩ := hrefl w hw hw2
  have huw : sr p * sr q ∈ H := by
    rw [mul_mem_iff_of_index_two hH]
    exact iff_of_false hu hw
  rw [sr_mul_sr] at huw
  obtain ⟨c, hc⟩ := hrot _ huw
  have hconj : r (-(c : ZMod (2 ^ (c₀ + 1 + 1)))) * sr p * (r (-(c : ZMod (2 ^ (c₀ + 1 + 1)))))⁻¹ =
      sr q := by
    rw [inv_r, neg_neg, r_mul_sr, sr_mul_r]
    congr 1
    linear_combination -hc
  by_cases hh : r (-(c : ZMod (2 ^ (c₀ + 1 + 1)))) ∈ H
  · exact ⟨_, hh, hconj⟩
  · refine ⟨r (-(c : ZMod (2 ^ (c₀ + 1 + 1)))) * sr p, ?_, ?_⟩
    · rw [mul_mem_iff_of_index_two hH]
      exact iff_of_false hh hu
    · have e1 : r (-(c : ZMod (2 ^ (c₀ + 1 + 1)))) * sr p * sr p =
          r (-(c : ZMod (2 ^ (c₀ + 1 + 1)))) := by
        rw [mul_assoc, sr_mul_self, mul_one]
      rw [e1, mul_inv_rev, inv_sr, ← mul_assoc]
      exact hconj

end CFSG.CGT.Foote81L6.TStruct
