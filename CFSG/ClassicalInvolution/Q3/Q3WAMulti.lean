module

public import CFSG.ClassicalInvolution.Q3.Q3WAStarMain
public import CFSG.ClassicalInvolution.Q3.Q3WAD4

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

section Relation

variable {G : Type} [Group G] [Finite G] {ι : Type}

theorem not_central_locElt_of_nonA13 (hMFZ : RouteD.Gaps.FundNoncentral 3) {Ω : Set (Subgroup G)}
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {x : G} (hP1 : LocalOddCentral Ω {x})
    (hO3 : LocalOddThreeFree3 Ω x) (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x))
    {N : Subgroup G} (hN : N ∈ centralizingMembers Ω {x}) {i : ι}
    (hi : locImg Ω x N ≤ (D.hom i).range) (hnA1 : ¬ IsA1Comp3 D i) {w : G}
    (hw : IsClassicalMember3 N w)
    (hcent : ∀ y ∈ (D.hom i).range, locElt Ω x w (le_centralizingLayer hN hw.mem) * y =
      y * locElt Ω x w (le_centralizingLayer hN hw.mem)) : False := by
  have hwx : w ∈ locLayer Ω x := le_centralizingLayer hN hw.mem
  have hmem : locImg Ω x N ∈ locFamily Ω x := mem_locFamily_iff.mpr ⟨N, hN, rfl⟩
  obtain ⟨j, R, hR, hRN⟩ := D.fundamental _ hmem
  have hj : locImg Ω x N ≤ (D.hom j).range := hRN ▸ Subgroup.map_le_range _ _
  have hji : j = i := eq_of_locImg_le_range3 hΩ hex hP1 hO3 D hN hj hi
  subst hji
  have hwmem : locElt Ω x w hwx ∈ R.map (D.hom j) :=
    hRN ▸ locElt_mem_locImg (le_centralizingLayer hN) hw.mem
  obtain ⟨r, hrR, hr⟩ := hwmem
  have hr1 : r = 1 :=
    eq_one_of_central_comp3 hMFZ (D.kind j) (D.valid j) hnA1 (D.hom j) (D.ker_le_center j) hR hrR
      fun y => by
        rw [hr]
        exact hcent (D.hom j y) ⟨y, rfl⟩
  rw [hr1, map_one] at hr
  have h2 := orderOf_locElt hwx hw.orderOf_eq_two
  rw [← hr, orderOf_one] at h2
  omega

theorem false_of_involution_relation3 (hMFZ : RouteD.Gaps.FundNoncentral 3) {K : Subgroup G}
    {z : G} (hc : LocCtx3 K z)
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z) (locFamily (conjClass3 K) z))
    {i₁ i₂ : ι} (hi : i₁ ≠ i₂) (hn₁ : ¬ IsA1Comp3 D i₁) (hn₂ : ¬ IsA1Comp3 D i₂)
    {a₁ a₂ a₃ : Subgroup G} (h₁ : a₁ ∈ centralizingMembers (conjClass3 K) {z})
    (h₂ : a₂ ∈ centralizingMembers (conjClass3 K) {z})
    (h₃ : a₃ ∈ centralizingMembers (conjClass3 K) {z}) {w₁ w₂ : G}
    (hw₁ : IsClassicalMember3 a₁ w₁) (hw₂ : IsClassicalMember3 a₂ w₂)
    (hw₃ : IsClassicalMember3 a₃ (z * w₁ * w₂))
    (ha₁ : locImg (conjClass3 K) z a₁ ≤ (D.hom i₁).range)
    (ha₂ : locImg (conjClass3 K) z a₂ ≤ (D.hom i₂).range) : False := by
  have hΩ := hc.hΩ
  have hex := hc.hex
  have hP1 := hc.hP1
  have hO3 := hc.hO3
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hKz : K ∈ centralizingMembers (conjClass3 K) {z} := ⟨hK, isSubnormal_le hc.hz.subnormal⟩
  have hzY : z ∈ locLayer (conjClass3 K) z := le_centralizingLayer hKz hc.hz.mem
  have hw₁Y : w₁ ∈ locLayer (conjClass3 K) z := le_centralizingLayer h₁ hw₁.mem
  have hw₂Y : w₂ ∈ locLayer (conjClass3 K) z := le_centralizingLayer h₂ hw₂.mem
  have hw₃Y : z * w₁ * w₂ ∈ locLayer (conjClass3 K) z := le_centralizingLayer h₃ hw₃.mem
  have hzc : ∀ q : locQuot (conjClass3 K) z,
      locElt (conjClass3 K) z z hzY * q = q * locElt (conjClass3 K) z z hzY := fun q =>
    (mk_involution_central3 (conjClass3 K) z hzY q).symm
  have hrel : locElt (conjClass3 K) z (z * w₁ * w₂) hw₃Y =
      locElt (conjClass3 K) z z hzY * locElt (conjClass3 K) z w₁ hw₁Y *
        locElt (conjClass3 K) z w₂ hw₂Y := by
    rw [locElt_mul, locElt_mul]
  obtain ⟨i₃, hi₃⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨a₃, h₃, rfl⟩)
  have hm₃ : locElt (conjClass3 K) z (z * w₁ * w₂) hw₃Y ∈ (D.hom i₃).range :=
    hi₃ (locElt_mem_locImg (le_centralizingLayer h₃) hw₃.mem)
  have hm₁ : locElt (conjClass3 K) z w₁ hw₁Y ∈ (D.hom i₁).range :=
    ha₁ (locElt_mem_locImg (le_centralizingLayer h₁) hw₁.mem)
  have hm₂ : locElt (conjClass3 K) z w₂ hw₂Y ∈ (D.hom i₂).range :=
    ha₂ (locElt_mem_locImg (le_centralizingLayer h₂) hw₂.mem)
  by_cases h31 : i₃ = i₁
  ·
    rw [h31] at hm₃
    refine not_central_locElt_of_nonA13 hMFZ hΩ hex hP1 hO3 D h₂ ha₂ hn₂ hw₂ fun y hy => ?_
    have h3 := (commutes_range3 D (Ne.symm hi) y hy _ hm₃).symm
    have h1 := (commutes_range3 D (Ne.symm hi) y hy _ hm₁).symm
    exact commute_right_of_relation hzc hrel h3 h1
  ·
    refine not_central_locElt_of_nonA13 hMFZ hΩ hex hP1 hO3 D h₁ ha₁ hn₁ hw₁ fun y hy => ?_
    have h3 := (commutes_range3 D (Ne.symm h31) y hy _ hm₃).symm
    have h2 := (commutes_range3 D hi y hy _ hm₂).symm
    exact commute_left_of_relation hzc hrel h3 h2

end Relation

section Piece

theorem multiPiece3_of_star (h3 : OddThreeFreeInput) (hstar : MultiStar3) :
    MultiPiece3 := by
  have hd4 := d4Frame3_holds
  intro G _ _ _ hnab K z hR hshape
  obtain ⟨ι, hι, D, hmulti⟩ := hshape
  have hMFZ := RouteD.Gaps.fundNoncentral 3
  have hO3 := h3 G K z hR
  obtain ⟨i₁, i₂, a₁, a₂, β, hi, hn₁, hn₂, ha₁, ha₂, hβ, hKβ, ha₁β, ha₂β⟩ :=
    hstar G hnab K z hR hO3 D hmulti
  have hc : LocCtx3 K z :=
    ⟨hR.inClass, (CoreAssembly.deltaConnected_iff K).mp hR.conn, hR.setup.1, hR.setup.2, hO3,
      hR.cls⟩
  have hΩ := hc.hΩ
  have hex := hc.hex
  have hP1 := hc.hP1
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hKz : K ∈ centralizingMembers (conjClass3 K) {z} := ⟨hK, isSubnormal_le hR.cls.subnormal⟩
  obtain ⟨w₁, hw₁⟩ := hΩ.classical a₁ ha₁.1.1
  obtain ⟨w₂, hw₂⟩ := hΩ.classical a₂ ha₂.1.1
  have hcomm : ∀ {a : Subgroup G} {i : ι}, a ∈ compMembers3 (conjClass3 K) z D i →
      ¬ IsA1Comp3 D i → Commutes K a := by
    intro a i ha hni
    rcases commutes_or_eq_of_involution3 hMFZ hΩ hex hP1 hO3 D hKz ha.1 hR.cls with hc' | heq
    · exact hc'
    · exfalso
      obtain ⟨iK, hKA1, hiK⟩ := locImg_eq_range_of_involution3 (D := D) hMFZ hKz hR.cls
      have h1 : locImg (conjClass3 K) z a ≤ (D.hom iK).range := by
        rw [heq]
        exact hiK.le
      have hiiK := eq_of_locImg_le_range3 hΩ hex hP1 hO3 D ha.1 ha.2 h1
      rw [hiiK] at hni
      exact hni hKA1
  have hKa₁ := hcomm ha₁ hn₁
  have hKa₂ := hcomm ha₂ hn₂
  have ha₁a₂ : Commutes a₁ a₂ := commutes_of_ne_comp3 hΩ hex hP1 hO3 D hi ha₁ ha₂
  obtain ⟨a₃, ha₃, hc₀, hc₁, hc₂, hw₃⟩ := hd4 G (conjClass3 K) hΩ.conjInvariant K a₁ a₂ β z w₁ w₂
    hK ha₁.1.1 ha₂.1.1 hβ hR.cls hw₁ hw₂ hKa₁ hKa₂ ha₁a₂ hKβ ha₁β ha₂β
  have ha₃z : a₃ ∈ centralizingMembers (conjClass3 K) {z} :=
    ⟨ha₃, fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hc₀ x hx z hR.cls.mem)⟩
  exact (false_of_involution_relation3 hMFZ hc D hi hn₁ hn₂ ha₁.1 ha₂.1 ha₃z hw₁ hw₂ hw₃
    ha₁.2 ha₂.2).elim

end Piece

end CFSG.ClassicalInvolution.Q3.Q3W
