module

public import CFSG.Permutation.FiveTransitive.CharacteristicAutomorphism
public import CFSG.CharacterTheory.Wreathed.OriginalCoordinates
public import CFSG.CharacterTheory.Wreathed.VQuotientCycle

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical
open CFSG.FiveTransitive.CharacteristicAutomorphism

universe u

@[expose] def centerFixingAutomorphisms (G : Type u) [Group G] : Subgroup (MulAut G) :=
  (restrict (Subgroup.center G)).ker

theorem mem_centerFixingAutomorphisms_iff {G : Type u} [Group G] (a : MulAut G) :
    a ∈ centerFixingAutomorphisms G ↔ ∀ c ∈ Subgroup.center G, a c = c := by
  change restrict (Subgroup.center G) a = 1 ↔ _
  constructor
  · intro h c hc
    exact congrArg (fun f : MulAut (Subgroup.center G) => (f ⟨c, hc⟩).val) h
  · intro h
    apply MulEquiv.ext
    intro c
    exact Subtype.ext (h c c.property)

@[expose] def centerFixingQuotientAction (G : Type u) [Group G] :
    centerFixingAutomorphisms G →* MulAut (G ⧸ Subgroup.center G) :=
  (quotient (Subgroup.center G)).comp (centerFixingAutomorphisms G).subtype

theorem centerFixingQuotientAction_mk {G : Type u} [Group G]
    (a : centerFixingAutomorphisms G) (g : G) :
    centerFixingQuotientAction G a ((QuotientGroup.mk' (Subgroup.center G)) g) =
      (QuotientGroup.mk' (Subgroup.center G)) (a.val g) :=
  quotient_apply_mk (Subgroup.center G) a.val g

@[expose] def innerToCenterFixing (G : Type u) [Group G] :
    G →* centerFixingAutomorphisms G :=
  (MulAut.conj : G →* MulAut G).codRestrict (centerFixingAutomorphisms G) (by
    intro g
    rw [mem_centerFixingAutomorphisms_iff]
    intro c hc
    rw [MulAut.conj_apply, Subgroup.mem_center_iff.mp hc g, mul_inv_cancel_right])

theorem innerToCenterFixing_coe {G : Type u} [Group G] (g x : G) :
    (innerToCenterFixing G g).val x = g * x * g⁻¹ := rfl

theorem exists_central_multiplier_of_quotient_eq {G : Type u} [Group G]
    (a : MulAut G) (g : G)
    (h : (QuotientGroup.mk' (Subgroup.center G)) (a g) =
      (QuotientGroup.mk' (Subgroup.center G)) g) :
    ∃ c : Subgroup.center G, a g = c.val * g := by
  have hc : a g / g ∈ Subgroup.center G := QuotientGroup.eq_iff_div_mem.mp h
  exact ⟨⟨a g / g, hc⟩, (div_mul_cancel (a g) g).symm⟩

theorem central_multiplier_square_eq_one {G : Type u} [Group G]
    (a : MulAut G) (g : G) (c : Subgroup.center G)
    (hg : g ^ 2 = 1) (h : a g = c.val * g) : c.val ^ 2 = 1 := by
  have hcomm : Commute c.val g := (Subgroup.mem_center_iff.mp c.property g).symm
  have hpow : (c.val * g) ^ 2 = 1 := by rw [← h, ← map_pow, hg, map_one]
  rwa [hcomm.mul_pow, hg, mul_one] at hpow

@[expose] def vDiagonalElement (l : ℕ) (c : ZMod (4 * l)) : vSubgroup l :=
  ⟨element (4 * l) c c 0, by simp⟩

@[expose] def vHalfElement (l : ℕ) : vSubgroup l :=
  ⟨element (4 * l) (2 * l : ℕ) 0 0, by simp⟩

@[expose] def vSwapElement (l : ℕ) : vSubgroup l :=
  ⟨element (4 * l) 0 0 1, by simp⟩

theorem vDiagonalElement_central (l : ℕ) (hl : 0 < l) (c : ZMod (4 * l)) :
    vDiagonalElement l c ∈ Subgroup.center (vSubgroup l) := by
  rw [v_mem_center_iff l hl]
  exact (element_mem_center_iff _ (by omega) _ _ _).mpr ⟨rfl, rfl⟩

theorem vHalfElement_square (l : ℕ) : vHalfElement l ^ 2 = 1 := by
  apply Subtype.ext
  change element (4 * l) (2 * l : ℕ) 0 0 ^ 2 = 1
  rw [element_base_pow, two_nsmul, twice_quarter_add_self, smul_zero, element_zero]

theorem vSwapElement_square (l : ℕ) : vSwapElement l ^ 2 = 1 := by
  apply Subtype.ext
  change element (4 * l) 0 0 1 ^ 2 = 1
  rw [element_swap_sq, zero_add, element_zero]

theorem v_central_square_one_cases (l : ℕ) (hl : 0 < l)
    (c : Subgroup.center (vSubgroup l)) (hc : c.val ^ 2 = 1) :
    c.val = 1 ∨ c.val = vDiagonalElement l (2 * l : ℕ) := by
  have hcenter := (v_mem_center_iff l hl c.val).mp c.property
  obtain ⟨⟨a, b, e⟩, heq⟩ := (coordinateEquiv (4 * l)).symm.surjective c.val.val
  change element (4 * l) a b e = c.val.val at heq
  rw [← heq, element_mem_center_iff _ (by omega)] at hcenter
  rcases hcenter with ⟨rfl, rfl⟩
  have hkill := congrArg (fun g : vSubgroup l => g.val) hc
  change c.val.val ^ 2 = 1 at hkill
  rw [← heq, element_base_pow, element_base_eq_one_iff] at hkill
  rcases (two_smul_eq_zero_half_quarter l hl a).mp hkill.1 with hb | hb
  · left
    apply Subtype.ext
    rw [← heq, hb, element_zero]
    rfl
  · right
    apply Subtype.ext
    rw [← heq, hb]
    rfl

theorem vCoordinateMap_eq_generators (l : ℕ) (c : ZMod (4 * l)) (b : Bool)
    (e : ZMod 2) :
    vCoordinateMap l (c, b, e) =
      vDiagonalElement l c * (if b then vHalfElement l else 1) * vSwapElement l ^ e.val := by
  apply Subtype.ext
  cases b <;> rcases swap_exponent_cases e with rfl | rfl <;>
    simp [vCoordinateMap, vDiagonalElement, vHalfElement, vSwapElement,
      show (1 : ZMod 2).val = 1 by decide, element_base_mul]

theorem v_hom_ext_of_center_half_swap (l : ℕ) (hl : 0 < l)
    (a b : MulAut (vSubgroup l))
    (ha : ∀ c ∈ Subgroup.center (vSubgroup l), a c = c)
    (hb : ∀ c ∈ Subgroup.center (vSubgroup l), b c = c)
    (hhalf : a (vHalfElement l) = b (vHalfElement l))
    (hswap : a (vSwapElement l) = b (vSwapElement l)) : a = b := by
  apply MulEquiv.ext
  intro g
  obtain ⟨⟨c, t, e⟩, rfl⟩ := vCoordinateMap_surjective l g
  rw [vCoordinateMap_eq_generators]
  have hdiag := vDiagonalElement_central l hl c
  rw [map_mul, map_mul, map_mul, map_mul, ha _ hdiag, hb _ hdiag, map_pow, map_pow, hswap]
  cases t <;> simp only [Bool.false_eq_true, ↓reduceIte, map_one, hhalf]

theorem v_kernel_involution_image_cases (l : ℕ) (hl : 0 < l)
    (a : MulAut (vSubgroup l)) (g : vSubgroup l) (hg : g ^ 2 = 1)
    (hq : (QuotientGroup.mk' (Subgroup.center (vSubgroup l))) (a g) =
      (QuotientGroup.mk' (Subgroup.center (vSubgroup l))) g) :
    a g = g ∨ a g = vDiagonalElement l (2 * l : ℕ) * g := by
  obtain ⟨c, hc⟩ := exists_central_multiplier_of_quotient_eq a g hq
  have hcs := central_multiplier_square_eq_one a g c hg hc
  rcases v_central_square_one_cases l hl c hcs with h | h
  · exact Or.inl (hc.trans (by rw [h, one_mul]))
  · exact Or.inr (hc.trans (by rw [h]))

theorem inner_fixes_center {G : Type u} [Group G] (g : G) :
    ∀ c ∈ Subgroup.center G, (MulAut.conj g) c = c :=
  (mem_centerFixingAutomorphisms_iff (MulAut.conj g)).mp
    (innerToCenterFixing G g).property

theorem vHalf_conjugate_half (l : ℕ) :
    (MulAut.conj (vHalfElement l)) (vHalfElement l) = vHalfElement l := by
  rw [MulAut.conj_apply, mul_inv_cancel_right]

theorem vSwap_conjugate_swap (l : ℕ) :
    (MulAut.conj (vSwapElement l)) (vSwapElement l) = vSwapElement l := by
  rw [MulAut.conj_apply, mul_inv_cancel_right]

theorem vHalf_conjugate_swap (l : ℕ) :
    (MulAut.conj (vHalfElement l)) (vSwapElement l) =
      vDiagonalElement l (2 * l : ℕ) * vSwapElement l := by
  apply Subtype.ext
  change element (4 * l) (2 * l : ℕ) 0 0 * element (4 * l) 0 0 1 *
    (element (4 * l) (2 * l : ℕ) 0 0)⁻¹ =
      element (4 * l) (2 * l : ℕ) (2 * l : ℕ) 0 * element (4 * l) 0 0 1
  rw [conjugate_swap_by_base, element_base_mul]
  simp only [zero_add, add_zero, zero_sub, sub_zero]
  congr 1
  exact neg_eq_iff_add_eq_zero.mpr (twice_quarter_add_self l)

theorem vSwap_conjugate_half (l : ℕ) :
    (MulAut.conj (vSwapElement l)) (vHalfElement l) =
      vDiagonalElement l (2 * l : ℕ) * vHalfElement l := by
  apply Subtype.ext
  change element (4 * l) 0 0 1 * element (4 * l) (2 * l : ℕ) 0 0 *
    (element (4 * l) 0 0 1)⁻¹ =
      element (4 * l) (2 * l : ℕ) (2 * l : ℕ) 0 *
        element (4 * l) (2 * l : ℕ) 0 0
  rw [conjugate_base_by_swap, element_base_mul, twice_quarter_add_self, add_zero]

theorem vHalfSwap_conjugate_half (l : ℕ) (hl : 0 < l) :
    (MulAut.conj (vHalfElement l * vSwapElement l)) (vHalfElement l) =
      vDiagonalElement l (2 * l : ℕ) * vHalfElement l := by
  rw [map_mul]
  change (MulAut.conj (vHalfElement l))
    ((MulAut.conj (vSwapElement l)) (vHalfElement l)) = _
  rw [vSwap_conjugate_half, map_mul,
    inner_fixes_center _ _ (vDiagonalElement_central l hl _), vHalf_conjugate_half]

theorem vHalfSwap_conjugate_swap (l : ℕ) :
    (MulAut.conj (vHalfElement l * vSwapElement l)) (vSwapElement l) =
      vDiagonalElement l (2 * l : ℕ) * vSwapElement l := by
  rw [map_mul]
  change (MulAut.conj (vHalfElement l))
    ((MulAut.conj (vSwapElement l)) (vSwapElement l)) = _
  rw [vSwap_conjugate_swap, vHalf_conjugate_swap]

theorem v_center_quotient_kernel_inner_atQuarter (l : ℕ) (hl : 0 < l)
    (a : MulAut (vSubgroup l))
    (hcenter : ∀ c ∈ Subgroup.center (vSubgroup l), a c = c)
    (hquotient : ∀ g : vSubgroup l,
      (QuotientGroup.mk' (Subgroup.center (vSubgroup l))) (a g) =
        (QuotientGroup.mk' (Subgroup.center (vSubgroup l))) g) :
    ∃ v : vSubgroup l, a = MulAut.conj v := by
  have hhalf := v_kernel_involution_image_cases l hl a (vHalfElement l)
    (vHalfElement_square l) (hquotient _)
  have hswap := v_kernel_involution_image_cases l hl a (vSwapElement l)
    (vSwapElement_square l) (hquotient _)
  rcases hhalf with hhalf | hhalf <;> rcases hswap with hswap | hswap
  · refine ⟨1, v_hom_ext_of_center_half_swap l hl a (MulAut.conj 1)
      hcenter (inner_fixes_center 1) ?_ ?_⟩
    · simpa only [map_one, MulAut.one_apply] using hhalf
    · simpa only [map_one, MulAut.one_apply] using hswap
  · refine ⟨vHalfElement l, v_hom_ext_of_center_half_swap l hl a _
      hcenter (inner_fixes_center _) ?_ ?_⟩
    · rw [vHalf_conjugate_half]
      exact hhalf
    · rw [vHalf_conjugate_swap]
      exact hswap
  · refine ⟨vSwapElement l, v_hom_ext_of_center_half_swap l hl a _
      hcenter (inner_fixes_center _) ?_ ?_⟩
    · rw [vSwap_conjugate_half]
      exact hhalf
    · rw [vSwap_conjugate_swap]
      exact hswap
  · refine ⟨vHalfElement l * vSwapElement l, v_hom_ext_of_center_half_swap l hl a _
      hcenter (inner_fixes_center _) ?_ ?_⟩
    · rw [vHalfSwap_conjugate_half l hl]
      exact hhalf
    · rw [vHalfSwap_conjugate_swap]
      exact hswap

theorem original_v_center_quotient_kernel_inner (n : ℕ) (hn : 2 ≤ n)
    (a : MulAut (Original.V (2 ^ n)))
    (hcenter : ∀ c ∈ Subgroup.center (Original.V (2 ^ n)), a c = c)
    (hquotient : ∀ g : Original.V (2 ^ n),
      (QuotientGroup.mk' (Subgroup.center (Original.V (2 ^ n)))) (a g) =
        (QuotientGroup.mk' (Subgroup.center (Original.V (2 ^ n)))) g) :
    ∃ v : Original.V (2 ^ n), a = MulAut.conj v := by
  have hm : 2 ^ n = 4 * 2 ^ (n - 2) := by
    have hheight : n = (n - 2) + 2 := by omega
    calc
      2 ^ n = 2 ^ ((n - 2) + 2) := congrArg (fun j : ℕ => 2 ^ j) hheight
      _ = 4 * 2 ^ (n - 2) := by rw [pow_add]; norm_num; ring
  revert a
  rw [hm, Original.V_atQuarter]
  exact v_center_quotient_kernel_inner_atQuarter _ (pow_pos (by decide) _)

theorem original_v_center_quotient_kernel_inner_pointwise (n : ℕ) (hn : 2 ≤ n)
    (a : MulAut (Original.V (2 ^ n)))
    (hcenter : ∀ c ∈ Subgroup.center (Original.V (2 ^ n)), a c = c)
    (hquotient : ∀ g : Original.V (2 ^ n),
      (QuotientGroup.mk' (Subgroup.center (Original.V (2 ^ n)))) (a g) =
        (QuotientGroup.mk' (Subgroup.center (Original.V (2 ^ n)))) g) :
    ∃ v : Original.V (2 ^ n), ∀ g : Original.V (2 ^ n), a g = v * g * v⁻¹ := by
  obtain ⟨v, hv⟩ := original_v_center_quotient_kernel_inner n hn a hcenter hquotient
  exact ⟨v, fun g => by rw [hv, MulAut.conj_apply]⟩

theorem mem_centerFixingQuotientAction_ker_iff {G : Type u} [Group G]
    (a : centerFixingAutomorphisms G) :
    a ∈ (centerFixingQuotientAction G).ker ↔
      ∀ g : G, (QuotientGroup.mk' (Subgroup.center G)) (a.val g) =
        (QuotientGroup.mk' (Subgroup.center G)) g := by
  change centerFixingQuotientAction G a = 1 ↔ _
  constructor
  · intro h g
    have hh := DFunLike.congr_fun h ((QuotientGroup.mk' (Subgroup.center G)) g)
    simpa only [centerFixingQuotientAction_mk, MulAut.one_apply] using hh
  · intro h
    apply MulEquiv.ext
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) q
    exact (centerFixingQuotientAction_mk a g).trans (h g)

theorem innerToCenterFixing_mem_quotient_ker {G : Type u} [Group G]
    (g : G) (hcomm : IsMulCommutative (G ⧸ Subgroup.center G)) :
    innerToCenterFixing G g ∈ (centerFixingQuotientAction G).ker := by
  rw [mem_centerFixingQuotientAction_ker_iff]
  intro x
  rw [innerToCenterFixing_coe, map_mul, map_mul, map_inv]
  rw [isMulCommutative_iff.mp hcomm ((QuotientGroup.mk' (Subgroup.center G)) g)
    ((QuotientGroup.mk' (Subgroup.center G)) x), mul_inv_cancel_right]

theorem original_v_center_quotient_abelian (n : ℕ) (hn : 2 ≤ n) :
    IsMulCommutative (Original.V (2 ^ n) ⧸ Subgroup.center (Original.V (2 ^ n))) := by
  have hm : 2 ^ n = 4 * 2 ^ (n - 2) := by
    have hheight : n = (n - 2) + 2 := by omega
    calc
      2 ^ n = 2 ^ ((n - 2) + 2) := congrArg (fun j : ℕ => 2 ^ j) hheight
      _ = 4 * 2 ^ (n - 2) := by rw [pow_add]; norm_num; ring
  rw [hm, Original.V_atQuarter]
  rw [isMulCommutative_iff]
  intro x y
  obtain ⟨q, rfl⟩ :=
    vQuotientQuaternionProjection_surjective _ (pow_pos (by decide) _) x
  obtain ⟨r, rfl⟩ :=
    vQuotientQuaternionProjection_surjective _ (pow_pos (by decide) _) y
  rw [← map_mul, ← map_mul,
    vQuotientQuaternionProjection_eq_iff _ (pow_pos (by decide) _)]
  exact (show ∀ q r : QuaternionGroup 2,
    q * r / (r * q) = 1 ∨ q * r / (r * q) = QuaternionGroup.a 2 by decide) q r

theorem original_v_centerFixingQuotientAction_ker (n : ℕ) (hn : 2 ≤ n) :
    (centerFixingQuotientAction (Original.V (2 ^ n))).ker =
      (innerToCenterFixing (Original.V (2 ^ n))).range := by
  ext a
  constructor
  · intro ha
    obtain ⟨v, hv⟩ := original_v_center_quotient_kernel_inner n hn a.val
      ((mem_centerFixingAutomorphisms_iff a.val).mp a.property)
      ((mem_centerFixingQuotientAction_ker_iff a).mp ha)
    exact ⟨v, Subtype.ext hv.symm⟩
  · rintro ⟨v, rfl⟩
    exact innerToCenterFixing_mem_quotient_ker v (original_v_center_quotient_abelian n hn)

end CFSG.Wreathed
