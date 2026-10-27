module

public import CFSG.ClassicalInvolution.Q3.Q3TSetup
public import CFSG.ClassicalInvolution.Q3.Q3WANoA1

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.RouteD
open scoped MatrixGroups commutatorElement

namespace Q3NT

theorem mul_self_eq_one_of_orderOf_eq_two {H : Type*} [Group H] {x : H} (h : orderOf x = 2) :
    x * x = 1 := by
  rw [← sq]
  exact (orderOf_eq_prime_iff.mp h).1

theorem eq_one_of_mem_oddCore_of_mul_self_eq_one {H : Type} [Group H] [Finite H] {y : H}
    (hy : y ∈ classicalInvolutionOddCore H) (h : y * y = 1) : y = 1 := by
  by_contra hne
  have h2 : orderOf y = 2 := orderOf_eq_prime (by rwa [← sq] at h) hne
  have h3 : orderOf (⟨y, hy⟩ : classicalInvolutionOddCore H) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact h2
  have h5 := orderOf_dvd_natCard (⟨y, hy⟩ : classicalInvolutionOddCore H)
  rw [h3] at h5
  exact (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card H))
    (even_iff_two_dvd.mpr h5)

theorem inv_mul_mul_self_eq_one {H : Type*} [Group H] {x y : H} (hxy : x * y = y * x)
    (hx : x * x = 1) (hy : y * y = 1) : (x⁻¹ * y) * (x⁻¹ * y) = 1 := by
  rw [inv_eq_of_mul_eq_one_right hx]
  calc x * y * (x * y) = x * (y * x) * y := by group
    _ = x * (x * y) * y := by rw [hxy]
    _ = (x * x) * (y * y) := by group
    _ = 1 := by rw [hx, hy, one_mul]

theorem commutator_mul_self_eq_one_of_commute {H : Type*} [Group H] {u w : H} (hw : w * w = 1)
    (hc : w * ⁅u, w⁆ = ⁅u, w⁆ * w) : ⁅u, w⁆ * ⁅u, w⁆ = 1 := by
  have h1 : (⁅u, w⁆ * w) * (⁅u, w⁆ * w) = 1 := by
    have : ⁅u, w⁆ * w = u * w * u⁻¹ := by rw [commutatorElement_def]; group
    rw [this]
    calc u * w * u⁻¹ * (u * w * u⁻¹) = u * (w * w) * u⁻¹ := by group
      _ = 1 := by rw [hw]; group
  obtain ⟨c, hcdef⟩ : ∃ c, c = ⁅u, w⁆ := ⟨_, rfl⟩
  rw [← hcdef] at hc h1 ⊢
  calc c * c = c * c * (w * w) := by rw [hw, mul_one]
    _ = c * (c * w) * w := by simp only [mul_assoc]
    _ = c * (w * c) * w := by rw [← hc]
    _ = (c * w) * (c * w) := by simp only [mul_assoc]
    _ = 1 := h1

theorem sl2Three_involutions_eq {s t : SL(2, ZMod 3)} (hs : s * s = 1) (ht : t * t = 1)
    (hs1 : s ≠ 1) (ht1 : t ≠ 1) : s = t := by
  have key : ∀ s t : SL(2, ZMod 3), s * s = 1 → t * t = 1 → s ≠ 1 → t ≠ 1 → s = t := by
    decide +kernel
  exact key s t hs ht hs1 ht1

theorem eq_of_involutions_of_natCard_range_eq_sl2Three {X : Type} [Group X]
    (φ : SL(2, ZMod 3) →* X) (hcard : Nat.card φ.range = 24) {x y : X} (hx : x ∈ φ.range)
    (hy : y ∈ φ.range) (hx2 : x * x = 1) (hy2 : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    x = y := by
  have hbij : Function.Bijective φ.rangeRestrict :=
    (Nat.bijective_iff_surjective_and_card _).mpr
      ⟨φ.rangeRestrict_surjective, by rw [hcard, natCard_sl2Three]⟩
  have hinj : Function.Injective φ := fun a b hab => hbij.1 (Subtype.ext hab)
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  have hs : s * s = 1 := hinj (by rw [map_mul, map_one]; exact hx2)
  have ht : t * t = 1 := hinj (by rw [map_mul, map_one]; exact hy2)
  have hs1 : s ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have ht1 : t ≠ 1 := fun h => hy1 (by rw [h, map_one])
  rw [sl2Three_involutions_eq hs ht hs1 ht1]

theorem eq_of_involutions_of_kind_eq_sl23 {X : Type} [Group X] (c : CompData)
    (hc : c = CompData.sl23) (φ : c.G →* X) (hcard : Nat.card φ.range = 24) {x y : X}
    (hx : x ∈ φ.range) (hy : y ∈ φ.range) (hx2 : x * x = 1) (hy2 : y * y = 1) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) : x = y := by
  subst hc
  exact eq_of_involutions_of_natCard_range_eq_sl2Three φ hcard hx hy hx2 hy2 hx1 hy1

end Q3NT

section Component

variable {G : Type} [Group G]


theorem exists_kind_eq_sl23 [Finite G] (hMFZ : RouteD.Gaps.FundNoncentral 3)
    {Ω : Set (Subgroup G)} {ι : Type} {z : G}
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z)) {K : Subgroup G}
    (hK : K ∈ centralizingMembers Ω {z}) (hz : IsClassicalMember3 K z) :
    ∃ i, D.kind i = CompData.sl23 ∧ locImg Ω z K = (D.hom i).range := by
  have hmem : locImg Ω z K ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨K, hK, rfl⟩
  obtain ⟨i, R, hRf, hRK⟩ := D.fundamental _ hmem
  have hzY : z ∈ locLayer Ω z := le_centralizingLayer hK hz.mem
  have hxK : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) ⟨z, hzY⟩ ∈
      locImg Ω z K := ⟨⟨z, hzY⟩, Subgroup.mem_subgroupOf.mpr hz.mem, rfl⟩
  rw [hRK] at hxK
  obtain ⟨r, hrR, hr⟩ := hxK
  have hc : D.kind i = CompData.sl23 := by
    by_contra hc
    have hr1 : r = 1 :=
      Q3W.eq_one_of_central_comp3 hMFZ (D.kind i) (D.valid i) hc (D.hom i) (D.ker_le_center i)
        hRf hrR fun y => by
          rw [hr]
          exact (Q3W.mk_involution_central3 Ω z hzY (D.hom i y)).symm
    rw [hr1, map_one] at hr
    exact Q3W.mk_involution_ne_one3 Ω hz.orderOf_eq_two hzY hr.symm
  refine ⟨i, hc, ?_⟩
  have hRtop : R = ⊤ := by
    have key : ∀ c' : CompData, c' = CompData.sl23 → ∀ R' : Subgroup c'.G, R' ∈ c'.fund →
        R' = ⊤ := by
      rintro c' rfl R' hR'
      exact hR'
    exact key _ hc R hRf
  rw [hRK, hRtop, Subgroup.map_top]

theorem le_centralizer_of_alphaCore_eq_bot3 [Finite G] [IsSimpleGroup G]
    (hMFZ : RouteD.Gaps.FundNoncentral 3) (hnab : ∃ a b : G, a * b ≠ b * a)
    {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (hIH : LocalLieSystems3 Ω)
    {K₁ L : Subgroup G} {z₁ w : G} (hK₁ : K₁ ∈ Ω) (hL : L ∈ Ω)
    (hz₁ : IsClassicalMember3 K₁ z₁) (hw : IsClassicalMember3 L w) (hne : z₁ ≠ w)
    (hLz : L ≤ Subgroup.centralizer ({z₁} : Set G))
    (hα : alphaCore (Subgroup.closure ({z₁, w} : Set G)) = ⊥) :
    K₁ ≤ Subgroup.centralizer ({w} : Set G) := by
  have hnc : ¬ ({z₁} : Set G) ⊆ Subgroup.center G := not_subset_center_of_ne_one hnab hz₁.ne_one
  obtain ⟨ι, hι, ⟨D⟩⟩ := hIH {z₁} hnc
  have hK₁mem : K₁ ∈ centralizingMembers Ω {z₁} := ⟨hK₁, isSubnormal_le hz₁.subnormal⟩
  have hLmem : L ∈ centralizingMembers Ω {z₁} := ⟨hL, hLz⟩
  have hzY : z₁ ∈ locLayer Ω z₁ := le_centralizingLayer hK₁mem hz₁.mem
  have hwY : w ∈ locLayer Ω z₁ := le_centralizingLayer hLmem hw.mem
  have hz₁2 : z₁ * z₁ = 1 := Q3NT.mul_self_eq_one_of_orderOf_eq_two hz₁.orderOf_eq_two
  have hw2 : w * w = 1 := Q3NT.mul_self_eq_one_of_orderOf_eq_two hw.orderOf_eq_two
  have hzw : z₁ * w = w * z₁ := (Subgroup.mem_centralizer_singleton_iff.mp (hLz hw.mem)).symm
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z₁)) with hπ
  set a : ↥(locLayer Ω z₁) := ⟨z₁, hzY⟩ with ha
  set b : ↥(locLayer Ω z₁) := ⟨w, hwY⟩ with hb
  have ha2 : a * a = 1 := Subtype.ext hz₁2
  have hb2 : b * b = 1 := Subtype.ext hw2
  have hab : a * b = b * a := Subtype.ext hzw
  obtain ⟨i, hi, hKbar⟩ := exists_kind_eq_sl23 hMFZ D hK₁mem hz₁
  have hπK : ∀ (u : G) (hu : u ∈ K₁), π ⟨u, le_centralizingLayer hK₁mem hu⟩ ∈ (D.hom i).range :=
    fun u hu => by
      rw [← hKbar]
      exact ⟨_, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  obtain ⟨j, R', -, hLbar⟩ := D.fundamental _ (mem_locFamily_iff.mpr ⟨L, hLmem, rfl⟩ :
    locImg Ω z₁ L ∈ locFamily Ω z₁)
  have hπb : π b ∈ (D.hom j).range := by
    have : π b ∈ locImg Ω z₁ L := ⟨b, Subgroup.mem_subgroupOf.mpr hw.mem, rfl⟩
    rw [hLbar] at this
    obtain ⟨r, -, hr⟩ := this
    exact ⟨r, hr⟩
  by_cases hji : j = i
  ·
    exfalso
    subst hji
    have hcard : Nat.card (D.hom j).range = 24 := by
      rw [← hKbar]
      exact D.card_eq _ (mem_locFamily_iff.mpr ⟨K₁, hK₁mem, rfl⟩)
    have hπa1 : π a ≠ 1 := Q3W.mk_involution_ne_one3 Ω hz₁.orderOf_eq_two hzY
    have hπb1 : π b ≠ 1 := fun h => by
      have := Q3NT.eq_one_of_mem_oddCore_of_mul_self_eq_one ((QuotientGroup.eq_one_iff _).mp h) hb2
      exact hw.ne_one (congrArg Subtype.val this)
    have hπab : π a = π b :=
      Q3NT.eq_of_involutions_of_kind_eq_sl23 (D.kind j) hi (D.hom j) hcard (hπK z₁ hz₁.mem) hπb
        (by rw [← map_mul, ha2, map_one]) (by rw [← map_mul, hb2, map_one]) hπa1 hπb1
    have hmem : a⁻¹ * b ∈ classicalInvolutionOddCore ↥(locLayer Ω z₁) := QuotientGroup.eq.mp hπab
    have h1 : a⁻¹ * b = 1 := Q3NT.eq_one_of_mem_oddCore_of_mul_self_eq_one hmem
      (Q3NT.inv_mul_mul_self_eq_one hab ha2 hb2)
    exact hne (congrArg Subtype.val (inv_mul_eq_one.mp h1))
  ·
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    set ua : ↥(locLayer Ω z₁) := ⟨u, le_centralizingLayer hK₁mem hu⟩ with hua
    obtain ⟨x, hx⟩ := hπK u hu
    obtain ⟨y, hy⟩ := hπb
    have hcm : π ua * π b = π b * π ua := by
      rw [← hx, ← hy]
      exact D.commute i j (Ne.symm hji) x y
    have hc : ua * b * ua⁻¹ * b⁻¹ ∈ classicalInvolutionOddCore ↥(locLayer Ω z₁) := by
      rw [← QuotientGroup.eq_one_iff]
      show π (ua * b * ua⁻¹ * b⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcm]
      group
    have hcG : ⁅u, w⁆ ∈ oddCoreIn (centralizingLayer Ω {z₁}) :=
      ⟨ua * b * ua⁻¹ * b⁻¹, hc, rfl⟩
    have hcF := oddCoreIn_centralizer_le_centralizer_of_alphaCore_eq_bot3
      (F := Subgroup.closure ({z₁, w} : Set G)) (x := z₁)
      (Subgroup.subset_closure (by simp)) hz₁.ne_one hα
      (oddCoreIn_centralizingLayer_le hΩ z₁ hcG)
    have hwc : w * ⁅u, w⁆ = ⁅u, w⁆ * w :=
      Subgroup.mem_centralizer_iff.mp hcF w (Subgroup.subset_closure (by simp))
    have hsq : ⁅u, w⁆ * ⁅u, w⁆ = 1 := Q3NT.commutator_mul_self_eq_one_of_commute hw2 hwc
    have h1 : ua * b * ua⁻¹ * b⁻¹ = 1 :=
      Q3NT.eq_one_of_mem_oddCore_of_mul_self_eq_one hc (Subtype.ext hsq)
    have h2 : ⁅u, w⁆ = 1 := congrArg Subtype.val h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h2

end Component

end CFSG.ClassicalInvolution.Q3
