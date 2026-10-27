module

public import CFSG.CGT.M24S.ExtraspecialGroup
public import CFSG.CGT.M24S.Defs

public section

namespace CFSG.CGT.M24S

open Matrix CFSG.CGT.Timmesfeld75 GL4

variable {G : Type} [Group G]

theorem commutator_eq_one_or_of_sq {x y z : G} (hzy : y * z = z * y) (hz : z ^ 2 = 1)
    (hx : x ^ 2 = 1 ∨ x ^ 2 = z) (hy : y ^ 2 = 1 ∨ y ^ 2 = z)
    (hxy : (x * y) ^ 2 = 1 ∨ (x * y) ^ 2 = z) :
    x⁻¹ * y⁻¹ * x * y = 1 ∨ x⁻¹ * y⁻¹ * x * y = z := by
  have hzi : z⁻¹ = z := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hz]
  have key : x⁻¹ * y⁻¹ * x * y = y * (((x * y) ^ 2)⁻¹ * x ^ 2) * y := by
    simp only [pow_two]
    group
  obtain ⟨u, hu, hu'⟩ : ∃ u, (u = 1 ∨ u = z) ∧ ((x * y) ^ 2)⁻¹ * x ^ 2 = u := by
    rcases hxy with h | h <;> rcases hx with h' | h' <;> rw [h, h']
    · exact ⟨1, Or.inl rfl, by group⟩
    · exact ⟨z, Or.inr rfl, by group⟩
    · exact ⟨z, Or.inr rfl, by rw [hzi, mul_one]⟩
    · exact ⟨1, Or.inl rfl, by rw [inv_mul_cancel]⟩
  rw [key, hu']
  rcases hu with hu | hu <;> rw [hu]
  · rw [mul_one, ← pow_two]
    exact hy
  · rw [hzy, mul_assoc, ← pow_two]
    rcases hy with h | h <;> rw [h]
    · exact Or.inr (mul_one z)
    · exact Or.inl (by rw [← pow_two, hz])

variable {T H : Subgroup G} {z : G}

namespace NatCoord

variable (c : NatCoord T H z)

include c in
theorem mem_T_of_commute {x : G} (hx : x ∈ H) (h : ∀ t ∈ T, x * t = t * x) : x ∈ T := by
  rw [← c.mat_eq_one_iff hx]
  apply eq_one_of_forall_mulVec_eq
  intro w
  obtain ⟨t, ht, rfl⟩ := c.exists_vec_eq w
  rw [← c.vec_conj hx ht, h t ht, mul_inv_cancel_right]

theorem top_dotProduct_tail {x y : G} (hx : x ∈ T) (hy : y ∈ c.E) (h : y * x = x * y) :
    top (c.mat y) ⬝ᵥ tail (c.vec x) = 0 := by
  have h1 : c.mat y *ᵥ c.vec x = c.vec x := by
    rw [← c.vec_conj (c.mem_H_of_mem_E hy) hx, h, mul_inv_cancel_right]
  have h2 := mulVec_apply_zero _ (c.mulVec_e0_of_mem_E hy) (c.vec x)
  rw [h1] at h2
  exact add_eq_left.1 h2.symm

theorem eq_one_or_eq_z_of_central {x : G} (hx : x ∈ c.E) (h : ∀ y ∈ c.E, x * y = y * x) :
    x = 1 ∨ x = z := by
  have hxT : x ∈ T := c.mem_T_of_commute (c.mem_H_of_mem_E hx) fun t ht => h t (c.T_le_E ht)
  have htail : tail (c.vec x) = 0 := by
    ext j
    obtain ⟨y, hy, hya⟩ := c.exists_mem_E (Pi.single j 1)
    have h1 := c.top_dotProduct_tail hxT hy (h y hy).symm
    rwa [hya, top_mk4, single_one_dotProduct] at h1
  rcases eq_zero_or_eq_e0_of_tail_eq_zero htail with h0 | h0
  · exact Or.inl (c.eq_of_vec_eq hxT T.one_mem (h0.trans c.vec_one.symm))
  · exact Or.inr (c.eq_of_vec_eq hxT c.mem (h0.trans c.vec_z.symm))

theorem commute_z_of_mem_E {y : G} (hy : y ∈ c.E) : y * z = z * y :=
  Subgroup.mem_centralizer_singleton_iff.1 (c.E_le hy).2

theorem conj_mem_E {g x : G} (hg : g ∈ H ⊓ Subgroup.centralizer ({z} : Set G))
    (hx : x ∈ c.E) : g * x * g⁻¹ ∈ c.E :=
  Subgroup.mem_subgroupOf.1
    (c.normal_E.conj_mem ⟨x, c.E_le hx⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨g, hg⟩)

theorem sq_mem_T {x : G} (hx : x ∈ c.E) : x ^ 2 ∈ T := by
  have hH := c.mem_H_of_mem_E hx
  have he := c.mulVec_e0_of_mem_E hx
  rw [← c.mat_eq_one_iff (H.pow_mem hH 2), pow_two, c.mat_mul hH hH]
  refine eq_of_mulVec_e0 _ _ ?_ (one_mulVec e0) ?_ ?_
  · rw [← mulVec_mulVec, he, he]
  · rw [blk_mul _ _ he, c.blk_of_mem_E hx, mul_one, blk_one]
  · rw [top_mul _ _ he, c.blk_of_mem_E hx, vecMul_one, vec_add_self, top_one]

theorem tail_vec_sq_mul {x t : G} (hx : x ∈ c.E) (ht : t ∈ T) :
    tail (c.vec ((x * t) ^ 2)) = tail (c.vec (x ^ 2)) := by
  have hH := c.mem_H_of_mem_E hx
  have hxi : x⁻¹ ∈ c.E := c.E.inv_mem hx
  have hc : x⁻¹ * t * x⁻¹⁻¹ ∈ T := c.conj_mem (H.inv_mem hH) ht
  have heq : (x * t) ^ 2 = x ^ 2 * ((x⁻¹ * t * x⁻¹⁻¹) * t) := by
    simp only [pow_two]
    group
  rw [heq, c.vec_mul (c.sq_mem_T hx) (T.mul_mem hc ht), c.vec_mul hc ht,
    c.vec_conj (H.inv_mem hH) ht, tail_add, tail_add,
    tail_mulVec _ (c.mulVec_e0_of_mem_E hxi), c.blk_of_mem_E hxi, one_mulVec, vec_add_self,
    add_zero]

theorem tail_vec_sq_conj {g x : G} (hg : g ∈ H ⊓ Subgroup.centralizer ({z} : Set G))
    (hx : x ∈ c.E) :
    tail (c.vec ((g * x * g⁻¹) ^ 2)) = blk (c.mat g) *ᵥ tail (c.vec (x ^ 2)) := by
  have heq : (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := by
    simp only [pow_two]
    group
  rw [heq, c.vec_conj hg.1 (c.sq_mem_T hx), tail_mulVec _ (c.mat_mulVec_e0 hg)]

theorem vecMul_top_conj {g x : G} (hg : g ∈ H ⊓ Subgroup.centralizer ({z} : Set G))
    (hx : x ∈ c.E) :
    vecMul (top (c.mat (g * x * g⁻¹))) (blk (c.mat g)) = top (c.mat x) := by
  have hy := c.conj_mem_E hg hx
  have h1 : c.mat (g * x * g⁻¹) * c.mat g = c.mat g * c.mat x := by
    rw [← c.mat_mul (c.mem_H_of_mem_E hy) hg.1, ← c.mat_mul hg.1 (c.mem_H_of_mem_E hx),
      inv_mul_cancel_right]
  have h2 := congrArg top h1
  rw [top_mul _ _ (c.mulVec_e0_of_mem_E hy), top_mul _ _ (c.mat_mulVec_e0 hg),
    c.blk_of_mem_E hx, vecMul_one, add_comm (top (c.mat x))] at h2
  exact add_left_cancel h2

theorem tail_vec_sq_eq_zero {x : G} (hx : x ∈ c.E) : tail (c.vec (x ^ 2)) = 0 := by
  have hxH := c.mem_H_of_mem_E hx
  by_contra hw
  by_cases ha : top (c.mat x) = 0
  · apply hw
    have hxT : x ∈ T := by
      rw [← c.mat_eq_one_iff hxH, c.mat_eq_mk4_of_mem_E hx, ha, mk4_zero_one]
    rw [pow_two, c.vec_mul hxT hxT, vec_add_self, tail_zero]
  · obtain ⟨B, hBB, haB, hBw⟩ := exists_transvection ha hw
    obtain ⟨g, hg, hgB⟩ := c.exists_mem_cent B (det_eq_one_of_mul_self hBB)
    have hy := c.conj_mem_E hg hx
    have hyH := c.mem_H_of_mem_E hy
    have htop : top (c.mat (g * x * g⁻¹)) = top (c.mat x) := by
      have h1 := c.vecMul_top_conj hg hx
      rw [hgB] at h1
      calc top (c.mat (g * x * g⁻¹)) = vecMul (vecMul (top (c.mat (g * x * g⁻¹))) B) B := by
            rw [vecMul_vecMul, hBB, vecMul_one]
        _ = top (c.mat x) := by rw [h1, haB]
    have hmat : c.mat (g * x * g⁻¹) = c.mat x := by
      rw [c.mat_eq_mk4_of_mem_E hy, c.mat_eq_mk4_of_mem_E hx, htop]
    have ht : x⁻¹ * (g * x * g⁻¹) ∈ T := by
      rw [← c.mat_eq_one_iff (H.mul_mem (H.inv_mem hxH) hyH), c.mat_mul (H.inv_mem hxH) hyH,
        hmat, c.mat_inv_mul hxH]
    have h2 := c.tail_vec_sq_mul hx ht
    rw [mul_inv_cancel_left, c.tail_vec_sq_conj hg hx, hgB] at h2
    exact hBw h2

theorem sq_eq_one_or_eq_z {x : G} (hx : x ∈ c.E) : x ^ 2 = 1 ∨ x ^ 2 = z := by
  rcases eq_zero_or_eq_e0_of_tail_eq_zero (c.tail_vec_sq_eq_zero hx) with h | h
  · exact Or.inl (c.eq_of_vec_eq (c.sq_mem_T hx) T.one_mem (h.trans c.vec_one.symm))
  · exact Or.inr (c.eq_of_vec_eq (c.sq_mem_T hx) c.mem (h.trans c.vec_z.symm))

include c in
theorem z_sq : z ^ 2 = 1 :=
  c.eq_of_vec_eq (T.pow_mem c.mem 2) T.one_mem
    (by rw [pow_two, c.vec_mul c.mem c.mem, vec_add_self, c.vec_one])

include c in
theorem z_ne_one : z ≠ 1 := by
  intro h
  have h1 : c.vec z = c.vec 1 := congrArg c.vec h
  rw [c.vec_z, c.vec_one] at h1
  have h2 := congrFun h1 0
  simp at h2

theorem isExtraspecialAt_E : IsExtraspecialAt c.E z := by
  refine ⟨IsPGroup.of_card c.card_E, c.T_le_E c.mem, orderOf_eq_prime c.z_sq c.z_ne_one,
    fun x hx => ⟨c.eq_one_or_eq_z_of_central hx, ?_⟩, fun x hx => c.sq_eq_one_or_eq_z hx,
    fun x hx y hy => commutator_eq_one_or_of_sq (c.commute_z_of_mem_E hy) c.z_sq
      (c.sq_eq_one_or_eq_z hx) (c.sq_eq_one_or_eq_z hy) (c.sq_eq_one_or_eq_z (c.E.mul_mem hx hy))⟩
  rintro (h | h) y hy <;> rw [h]
  · rw [one_mul, mul_one]
  · exact (c.commute_z_of_mem_E hy).symm

end NatCoord

end CFSG.CGT.M24S
