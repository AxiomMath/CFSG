module

public import CFSG.LargeExtraspecial.AS35ZSDefs
public import CFSG.LargeExtraspecial.A2ModBasicPoint

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35ZS

open Module CFSG.RankThree.OrthogonalInvolutions CFSG.Fischer.Classification.Unitary
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary QuadraticMap
open CFSG.Blueprint.Fischer (K)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

section Cube

variable {c : V ≃ₗ[ZMod 2] V} (hc : ∀ v, c (c (c v)) = v)
include hc

omit hc in
theorem add_sq_mem_commSpace (w : V) : c w + c (c w) ∈ commSpace c := by
  refine mem_commSpace.mpr ⟨c w, ?_⟩
  rw [sub_eq_add_V, add_comm]

theorem fix_of_cube (w : V) : c (w + c w + c (c w)) = w + c w + c (c w) := by
  rw [map_add, map_add, hc]
  abel

theorem fixed_eq_zero_of_cube {v : V} (hv : v ∈ commSpace c) (hfix : c v = v) : v = 0 := by
  obtain ⟨u, rfl⟩ := mem_commSpace.mp hv
  have h1 : (c u - u) + c (c u - u) + c (c (c u - u)) = 0 := by
    simp only [map_sub, hc]
    abel
  rw [hfix, hfix] at h1
  have h3 : (c u - u) + (c u - u) + (c u - u) = c u - u := by
    rw [add_self_V, zero_add]
  rw [← h3, h1]

theorem apply_mem_commSpace_of_invert {d : V ≃ₗ[ZMod 2] V} (hdc : ∀ v, c (d (c v)) = d v)
    {v : V} (hv : v ∈ commSpace c) : d v ∈ commSpace c := by
  obtain ⟨u, rfl⟩ := mem_commSpace.mp hv
  refine mem_commSpace.mpr ⟨c (d u) + d u, ?_⟩
  have e1 : d (c u) = c (c (d u)) := by
    have := congrArg (fun w => c (c w)) (hdc u)
    simp only [hc] at this
    exact this
  rw [map_sub, e1, map_add]
  abel

theorem eq_zero_of_polar_commSpace {q : QuadraticForm (ZMod 2) V}
    (hq : (polarBilin q).Nondegenerate) (hiso : ∀ u v, polar q (c u) (c v) = polar q u v)
    {v : V} (hv : v ∈ commSpace c) (h0 : ∀ w ∈ commSpace c, polar q v w = 0) : v = 0 := by
  have h1 : ∀ u, polar q (c (c v) - v) u = 0 := by
    intro u
    have e1 : polar q v (c u) = polar q (c (c v)) u := by
      rw [← hiso (c (c v)) u, hc]
    have e2 := h0 _ (sub_mem_commSpace c u)
    have e3 : polar q v (c u - u) = polar q v (c u) - polar q v u := by
      simpa only [polarBilin_apply_apply] using map_sub (polarBilin q v) (c u) u
    have e4 : polar q (c (c v) - v) u = polar q (c (c v)) u - polar q v u := by
      simpa only [polarBilin_apply_apply] using LinearMap.map_sub₂ (polarBilin q) (c (c v)) v u
    rw [e4, ← e1, ← e3, e2]
  have h2 : c (c v) - v = 0 := hq.1 _ h1
  have h3 : c v = v := by
    have := congrArg c (sub_eq_zero.1 h2)
    rwa [hc, eq_comm] at this
  exact fixed_eq_zero_of_cube hc hv h3

end Cube

section Elt

variable {n : ℕ} {ρ : PG n →* (V ≃ₗ[ZMod 2] V)}

theorem tq_mul_tq_cube {x y : Fin n → K} (hx : herm frob x x = 0) (hy : herm frob y y = 0)
    (hxy : herm frob x y ≠ 0) : (tq x * tq y) ^ 3 = 1 := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, tvU_mul_tvU_pow_three hx hy hxy,
    QuotientGroup.mk_one]

theorem cube_apply {x y : Fin n → K} (hx : herm frob x x = 0) (hy : herm frob y y = 0)
    (hxy : herm frob x y ≠ 0) (v : V) :
    ρ (tq x * tq y) (ρ (tq x * tq y) (ρ (tq x * tq y) v)) = v := by
  have e : ρ (tq x * tq y) ^ 3 = 1 := by rw [← map_pow, tq_mul_tq_cube hx hy hxy, map_one]
  have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) e
  simp only [pow_succ, pow_zero, one_mul, LinearEquiv.mul_apply] at this
  exact this.trans rfl

theorem invert_apply {x y : Fin n → K} (hx : herm frob x x = 0) (hy : herm frob y y = 0)
    (v : V) : ρ (tq x * tq y) (ρ (tq x) (ρ (tq x * tq y) v)) = ρ (tq x) v := by
  have e : (tq x * tq y) * tq x * (tq x * tq y) = tq x := by
    calc (tq x * tq y) * tq x * (tq x * tq y) = tq x * tq y * (tq x * tq x) * tq y := by group
      _ = tq x := by rw [tq_mul_self hx, mul_one, mul_assoc, tq_mul_self hy, mul_one]
  rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul, e]

end Elt

namespace ZSHyp

variable {n : ℕ} {ρ : PG n →* (V ≃ₗ[ZMod 2] V)} {q : QuadraticForm (ZMod 2) V}
  [FiniteDimensional (ZMod 2) V] (h : ZSHyp n q ρ)
include h

theorem inf_lineA_eq_bot {x y : Fin n → K} (hx0 : x ≠ 0) (hx : herm frob x x = 0)
    (hy0 : y ≠ 0) (hy : herm frob y y = 0) (hxy : herm frob x y ≠ 0) :
    lineA ρ x ⊓ lineA ρ y = ⊥ := by
  rw [eq_bot_iff]
  intro P hP
  rw [Submodule.mem_bot]
  by_contra hP0
  have hA : A2Mod.A2Action ({tq x, tq y} : Set (PG n)) q ρ :=
    h.a2.mono (by
      rintro d (rfl | rfl)
      · exact tq_mem_DG hx0 hx
      · exact tq_mem_DG hy0 hy)
  have hPD : ∀ d ∈ ({tq x, tq y} : Set (PG n)), P ∈ commSpace (ρ d) := by
    rintro d (rfl | rfl)
    · exact (Submodule.mem_inf.1 hP).1
    · exact (Submodule.mem_inf.1 hP).2
  have hcomm := hA.commute_of_common_point hP0 hPD
    (Subgroup.subset_closure (Set.mem_insert _ _))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  exact hxy ((tq_commute_iff h.three_le hx0 hx hy0 hy).1 hcomm)

theorem lineA_le_commSpace {x y : Fin n → K} (hx0 : x ≠ 0) (hx : herm frob x x = 0)
    (hy0 : y ≠ 0) (hy : herm frob y y = 0) (hxy : herm frob x y ≠ 0) :
    lineA ρ x ≤ commSpace (ρ (tq x * tq y)) := by
  set c := ρ (tq x * tq y) with hcdef
  set d := ρ (tq x) with hd
  have hc := cube_apply (ρ := ρ) hx hy hxy
  intro a ha
  obtain ⟨w, rfl⟩ := mem_commSpace.mp ha
  set wC := w + c w + c (c w) with hwC
  set wB := c w + c (c w) with hwB
  have hw : w = wC + wB := by
    rw [hwC, hwB, add_assoc w, add_assoc w, add_self_V, add_zero]
  have hfix : c wC = wC := fix_of_cube hc w
  have hde : d wC = ρ (tq y) wC := by
    have e1 : d (ρ (tq y) wC) = wC := by
      rw [← LinearEquiv.mul_apply, ← map_mul]
      exact hfix
    have e2 := congrArg d e1
    rwa [apply_apply_of_mul_self (tq_mul_self' hx), eq_comm] at e2
  have hC : d wC - wC = 0 := by
    have h1 : d wC - wC ∈ lineA ρ x := sub_mem_commSpace _ _
    have h2 : d wC - wC ∈ lineA ρ y := by rw [hde]; exact sub_mem_commSpace _ _
    have := Submodule.mem_inf.2 ⟨h1, h2⟩
    rwa [h.inf_lineA_eq_bot hx0 hx hy0 hy hxy, Submodule.mem_bot] at this
  have hB : wB ∈ commSpace c := add_sq_mem_commSpace w
  have hdB : d wB ∈ commSpace c := apply_mem_commSpace_of_invert hc (invert_apply hx hy) hB
  rw [hw, map_add, show d wC + d wB - (wC + wB) = (d wC - wC) + (d wB - wB) by abel, hC,
    zero_add]
  exact (commSpace c).sub_mem hdB hB

theorem commSpace_eq_sup {x y : Fin n → K} (hx0 : x ≠ 0) (hx : herm frob x x = 0)
    (hy0 : y ≠ 0) (hy : herm frob y y = 0) (hxy : herm frob x y ≠ 0) :
    commSpace (ρ (tq x * tq y)) = lineA ρ x ⊔ lineA ρ y := by
  apply le_antisymm
  · intro v hv
    obtain ⟨u, rfl⟩ := mem_commSpace.mp hv
    rw [map_mul, LinearEquiv.mul_apply,
      show ρ (tq x) (ρ (tq y) u) - u = (ρ (tq x) (ρ (tq y) u) - ρ (tq y) u) + (ρ (tq y) u - u)
        by abel]
    exact Submodule.add_mem_sup (sub_mem_commSpace _ _) (sub_mem_commSpace _ _)
  · have hyx : herm frob y x ≠ 0 := fun h0 => hxy (herm_eq_zero_comm frob frob_frob h0)
    refine sup_le (h.lineA_le_commSpace hx0 hx hy0 hy hxy) ?_
    have h2 := h.lineA_le_commSpace hy0 hy hx0 hx hyx
    have e : commSpace (ρ (tq y * tq x)) = commSpace (ρ (tq x * tq y)) := by
      have hinv : tq y * tq x = (tq x * tq y)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (tq_mul_self hx),
          inv_eq_of_mul_eq_one_right (tq_mul_self hy)]
      rw [hinv, map_inv]
      exact A2Mod.commSpace_inv_eq _
    rwa [e] at h2

theorem finrank_sup_lineA {x y : Fin n → K} (hx0 : x ≠ 0) (hx : herm frob x x = 0)
    (hy0 : y ≠ 0) (hy : herm frob y y = 0) (hxy : herm frob x y ≠ 0) :
    finrank (ZMod 2) ↥(lineA ρ x ⊔ lineA ρ y) = 4 := by
  have := Submodule.finrank_sup_add_finrank_inf_eq (lineA ρ x) (lineA ρ y)
  rw [h.inf_lineA_eq_bot hx0 hx hy0 hy hxy, finrank_bot, add_zero, h.finrank_lineA hx0 hx,
    h.finrank_lineA hy0 hy] at this
  exact this

theorem eq_zero_of_polar_sup {x y : Fin n → K} (hx0 : x ≠ 0) (hx : herm frob x x = 0)
    (hy0 : y ≠ 0) (hy : herm frob y y = 0) (hxy : herm frob x y ≠ 0) {v : V}
    (hv : v ∈ lineA ρ x ⊔ lineA ρ y) (h0 : ∀ w ∈ lineA ρ x ⊔ lineA ρ y, polar q v w = 0) :
    v = 0 := by
  rw [← h.commSpace_eq_sup hx0 hx hy0 hy hxy] at hv h0
  exact eq_zero_of_polar_commSpace (cube_apply hx hy hxy) h.nondeg
    (fun u w => h.polar_apply _ u w) hv h0

end ZSHyp

end CFSG.LargeExtraspecial.AS35ZS
