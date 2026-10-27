module

public import CFSG.ClassicalInvolution.Q3.Q3NTLemmaD
public import CFSG.ClassicalInvolution.Q3.Q3WAComp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NL

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

section Elements

variable {G : Type} [Group G]

theorem locElt_eq_iff {Ω : Set (Subgroup G)} {z x y : G} (hx : x ∈ locLayer Ω z)
    (hy : y ∈ locLayer Ω z) :
    locElt Ω z x hx = locElt Ω z y hy ↔ x⁻¹ * y ∈ oddCoreIn (locLayer Ω z) := by
  unfold locElt
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  constructor
  · intro h
    exact ⟨_, h, by simp⟩
  · rintro ⟨w, hw, hwe⟩
    have : w = (⟨x, hx⟩ : ↥(locLayer Ω z))⁻¹ * ⟨y, hy⟩ := Subtype.ext (by simpa using hwe)
    rwa [this] at hw

theorem commutes_locImg_iff {Ω : Set (Subgroup G)} {z : G} {N₁ N₂ : Subgroup G}
    (h₁ : N₁ ∈ centralizingMembers Ω {z}) (h₂ : N₂ ∈ centralizingMembers Ω {z}) :
    Commutes (locImg Ω z N₁) (locImg Ω z N₂) ↔
      ∀ x ∈ N₁, ∀ y ∈ N₂, ⁅x, y⁆ ∈ oddCoreIn (centralizingLayer Ω {z}) := by
  constructor
  · intro h x hx y hy
    have := h _ (locElt_mem_locImg (le_centralizingLayer h₁) hx) _
      (locElt_mem_locImg (le_centralizingLayer h₂) hy)
    exact (mk_comm_eq_iff (le_centralizingLayer h₁ hx) (le_centralizingLayer h₂ hy)).mp this
  · rintro h _ ⟨⟨x, hxY⟩, hx, rfl⟩ _ ⟨⟨y, hyY⟩, hy, rfl⟩
    exact (mk_comm_eq_iff hxY hyY).mpr (h x (Subgroup.mem_subgroupOf.mp hx) y
      (Subgroup.mem_subgroupOf.mp hy))

end Elements

section Involutions

variable {G : Type} [Group G] [Finite G]

theorem mul_self_eq_one_of_member {N : Subgroup G} {n : G} (h : IsClassicalMember3 N n) :
    n * n = 1 :=
  Q3NT.mul_self_eq_one_of_orderOf_eq_two h.orderOf_eq_two

theorem mem_locLayer_of_member {Ω : Set (Subgroup G)} {z : G} {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z}) {n : G} (h : IsClassicalMember3 N n) :
    n ∈ locLayer Ω z :=
  le_centralizingLayer hN h.mem

theorem mul_comm_of_member {Ω : Set (Subgroup G)} {z : G} {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z}) {n : G} (h : IsClassicalMember3 N n) :
    n * z = z * n :=
  (Subgroup.mem_centralizer_singleton_iff.mp (hN.2 h.mem))

theorem orderOf_locElt_of_member {Ω : Set (Subgroup G)} {z : G} {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z}) {n : G} (h : IsClassicalMember3 N n) :
    orderOf (locElt Ω z n (mem_locLayer_of_member hN h)) = 2 :=
  orderOf_locElt _ h.orderOf_eq_two

theorem eq_of_locElt_eq {Ω : Set (Subgroup G)} {z n : G} (hn : n ∈ locLayer Ω z)
    (hz : z ∈ locLayer Ω z) (hn2 : n * n = 1) (hz2 : z * z = 1) (hnz : n * z = z * n)
    (h : locElt Ω z n hn = locElt Ω z z hz) : n = z := by
  have hmem := (locElt_eq_iff hn hz).mp h
  obtain ⟨w, hw, hwe⟩ := hmem
  have h1 : (⟨n, hn⟩ : ↥(locLayer Ω z))⁻¹ * ⟨z, hz⟩ ∈
      classicalInvolutionOddCore ↥(locLayer Ω z) := by
    have : w = (⟨n, hn⟩ : ↥(locLayer Ω z))⁻¹ * ⟨z, hz⟩ := Subtype.ext (by simpa using hwe)
    rwa [this] at hw
  have hn2' : (⟨n, hn⟩ : ↥(locLayer Ω z)) * ⟨n, hn⟩ = 1 := Subtype.ext hn2
  have hz2' : (⟨z, hz⟩ : ↥(locLayer Ω z)) * ⟨z, hz⟩ = 1 := Subtype.ext hz2
  have hnz' : (⟨n, hn⟩ : ↥(locLayer Ω z)) * ⟨z, hz⟩ = ⟨z, hz⟩ * ⟨n, hn⟩ := Subtype.ext hnz
  have h2 := Q3NT.eq_one_of_mem_oddCore_of_mul_self_eq_one h1
    (Q3NT.inv_mul_mul_self_eq_one hnz' hn2' hz2')
  exact congrArg Subtype.val (inv_mul_eq_one.mp h2)

end Involutions

section Nonabelian

variable {G : Type} [Group G] [Finite G]

theorem not_commutes_locImg_self {Ω : Set (Subgroup G)} {z : G} {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z}) {n : G} (hn : IsClassicalMember3 N n) :
    ¬ Commutes (locImg Ω z N) (locImg Ω z N) := by
  intro hc
  have hcomm := (commutes_locImg_iff hN hN).mp hc
  have hNY : N ≤ locLayer Ω z := le_centralizingLayer hN
  have hS : ∀ x ∈ N, ∀ y ∈ N, ⁅x, y⁆ ∈ oddCoreIn N := by
    intro x hx y hy
    have hxy : ⁅x, y⁆ ∈ N :=
      N.mul_mem (N.mul_mem (N.mul_mem hx hy) (N.inv_mem hx)) (N.inv_mem hy)
    have hle : N ⊓ oddCoreIn (locLayer Ω z) ≤ oddCoreIn N := by
      refine le_oddCoreIn_of_normalizes inf_le_left ?_ ?_
      · intro u hu
        rw [Subgroup.mem_normalizer_iff]
        intro h
        have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hu)) h
        have h2 := (Subgroup.mem_normalizer_iff.mp (normalizer_oddCoreIn (locLayer Ω z)
          (hNY hu))) h
        simp only [Subgroup.mem_inf]
        exact and_congr h1 h2
      · have hdvd : Nat.card (N ⊓ oddCoreIn (locLayer Ω z) : Subgroup G) ∣
            Nat.card (oddCoreIn (locLayer Ω z)) :=
          Subgroup.card_dvd_of_le inf_le_right
        exact Odd.of_dvd_nat (odd_card_oddCoreIn _) hdvd
    exact hle ⟨hxy, hcomm x hx y hy⟩
  obtain ⟨e⟩ := hn.nonempty_equiv
  have hab : ∀ a b : SL(2, ZMod 3), a * b = b * a := by
    intro a b
    obtain ⟨a', ha'⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore N) (e.symm a)
    obtain ⟨b', hb'⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore N) (e.symm b)
    apply e.symm.injective
    rw [map_mul, map_mul, ← ha', ← hb']
    exact (mk_comm_eq_iff (Y := N) a'.2 b'.2).mpr (hS _ a'.2 _ b'.2)
  exact sl2Three_not_comm hab

end Nonabelian

section Indep

variable {G : Type} [Group G]

@[expose] def IndepModOdd (Ω : Set (Subgroup G)) (z n₁ n₂ : G) : Prop :=
  n₁⁻¹ * z ∉ oddCoreIn (locLayer Ω z) ∧ n₂⁻¹ * z ∉ oddCoreIn (locLayer Ω z) ∧
    n₁⁻¹ * n₂ ∉ oddCoreIn (locLayer Ω z) ∧ (n₁ * n₂)⁻¹ * z ∉ oddCoreIn (locLayer Ω z)

theorem indepModOdd_of_images {Ω : Set (Subgroup G)} {z n₁ n₂ : G} (h₁ : n₁ ∈ locLayer Ω z)
    (h₂ : n₂ ∈ locLayer Ω z) (hz : z ∈ locLayer Ω z)
    (a : locElt Ω z n₁ h₁ ≠ locElt Ω z z hz) (b : locElt Ω z n₂ h₂ ≠ locElt Ω z z hz)
    (c : locElt Ω z n₁ h₁ ≠ locElt Ω z n₂ h₂)
    (d : locElt Ω z n₁ h₁ * locElt Ω z n₂ h₂ ≠ locElt Ω z z hz) : IndepModOdd Ω z n₁ n₂ :=
  ⟨fun h => a ((locElt_eq_iff h₁ hz).mpr h), fun h => b ((locElt_eq_iff h₂ hz).mpr h),
    fun h => c ((locElt_eq_iff h₁ h₂).mpr h), fun h => d (by
      rw [locElt_mul h₁ h₂]
      exact (locElt_eq_iff _ hz).mpr h)⟩

theorem IndepModOdd.ne {Ω : Set (Subgroup G)} {z n₁ n₂ : G} (h : IndepModOdd Ω z n₁ n₂) :
    n₁ ≠ z ∧ n₂ ≠ z ∧ n₁ ≠ n₂ ∧ n₁ * n₂ ≠ z :=
  ⟨fun e => h.1 (by rw [e, inv_mul_cancel]; exact Subgroup.one_mem _),
    fun e => h.2.1 (by rw [e, inv_mul_cancel]; exact Subgroup.one_mem _),
    fun e => h.2.2.1 (by rw [e, inv_mul_cancel]; exact Subgroup.one_mem _),
    fun e => h.2.2.2 (by rw [e, inv_mul_cancel]; exact Subgroup.one_mem _)⟩

end Indep

section GroupLemma

theorem indep_of_noncommute {X : Type*} [Group X] {a b zb y : X} (hay : a * y ≠ y * a)
    (hby : b * y = y * b) (hzy : zb * y = y * zb) : a ≠ zb ∧ a ≠ b ∧ a * b ≠ zb := by
  refine ⟨fun h => hay (by rw [h]; exact hzy), fun h => hay (by rw [h]; exact hby), ?_⟩
  intro h
  apply hay
  have ha : a = zb * b⁻¹ := by rw [← h]; group
  rw [ha]
  have hby' : b⁻¹ * y = y * b⁻¹ := by
    calc b⁻¹ * y = b⁻¹ * (y * b) * b⁻¹ := by group
      _ = b⁻¹ * (b * y) * b⁻¹ := by rw [hby]
      _ = y * b⁻¹ := by group
  calc zb * b⁻¹ * y = zb * (b⁻¹ * y) := by group
    _ = zb * (y * b⁻¹) := by rw [hby']
    _ = (zb * y) * b⁻¹ := by group
    _ = (y * zb) * b⁻¹ := by rw [hzy]
    _ = y * (zb * b⁻¹) := by group

end GroupLemma

section Branch


structure NTCommon3 {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop where
  nonab : ∃ a b : G, a * b ≠ b * a
  cls : IsClassicalMember3 K z
  below : CIT3Below (Nat.card G)
  rank : 3 ≤ twoRank G
  large : ¬ TwoSubgroupsFourGenerated G
  delta : DeltaConnected K

structure NTHyps3 {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop where
  common : NTCommon3 K z
  data : BootData3 (conjClass3 K)
  noTriple : ¬ IndepTriple3 (conjClass3 K)

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem NTCommon3.inClass (h : NTCommon3 K z) : InClass3 (conjClass3 K) :=
  inClass3_conjugates h.cls

theorem NTCommon3.lieSystems (h : NTCommon3 K z) : LocalLieSystems3 (conjClass3 K) :=
  localLieSystems3_of_cit3Below h.inClass h.below

theorem NTCommon3.mem_centralizingMembers (h : NTCommon3 K z) :
    K ∈ centralizingMembers (conjClass3 K) {z} :=
  ⟨⟨1, conjSub_one K⟩, isSubnormal_le h.cls.subnormal⟩

theorem NTCommon3.mem_locLayer (h : NTCommon3 K z) : z ∈ locLayer (conjClass3 K) z :=
  le_centralizingLayer h.mem_centralizingMembers h.cls.mem

theorem NTCommon3.not_subset_center (h : NTCommon3 K z) :
    ¬ ({z} : Set G) ⊆ Subgroup.center G :=
  Q3W.not_subset_center_of_ne_one h.nonab h.cls.ne_one

end Branch

section Components


variable {G : Type} [Group G] [Finite G] {ι : Type} {Ω : Set (Subgroup G)} {z : G}
  (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z))

theorem exists_hom_elt_of_corr {i : ι} {N : Subgroup G} {R : Subgroup (D.kind i).G}
    (hc : Q3W.Corr3 Ω z D i N R) {x : G} (hx : x ∈ N) :
    ∃ r ∈ R, D.hom i r = locElt Ω z x (le_centralizingLayer hc.1 hx) := by
  obtain ⟨hNm, -, hNR⟩ := hc
  have h := locElt_mem_locImg (le_centralizingLayer hNm) hx
  rw [hNR] at h
  obtain ⟨r, hr, hre⟩ := h
  exact ⟨r, hr, hre⟩

theorem exists_noncommute_of_nonA1 (hMFZ : RouteD.Gaps.FundNoncentral 3) {i : ι}
    (hi : D.kind i ≠ CompData.sl23) {N : Subgroup G} {R : Subgroup (D.kind i).G}
    (hc : Q3W.Corr3 Ω z D i N R) {n : G} (hn : IsClassicalMember3 N n) :
    ∃ y : (D.kind i).G, locElt Ω z n (mem_locLayer_of_member hc.1 hn) * D.hom i y ≠
      D.hom i y * locElt Ω z n (mem_locLayer_of_member hc.1 hn) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨r, hrR, hr⟩ := exists_hom_elt_of_corr D hc hn.mem
  have hr1 : r = 1 :=
    Q3W.eq_one_of_central_comp3 hMFZ (D.kind i) (D.valid i) hi (D.hom i) (D.ker_le_center i)
      hc.2.1 hrR fun y => by
        rw [hr]
        exact hcon y
  have h1 : locElt Ω z n (mem_locLayer_of_member hc.1 hn) = 1 := by
    rw [← hr, hr1, map_one]
  have h2 := orderOf_locElt_of_member hc.1 hn
  rw [h1, orderOf_one] at h2
  omega

theorem locElt_self_central (hz : z ∈ locLayer Ω z) (w : locQuot Ω z) :
    w * locElt Ω z z hz = locElt Ω z z hz * w :=
  Q3W.mk_involution_central3 Ω z hz w

theorem indep_images_of_nonA1 (hMFZ : RouteD.Gaps.FundNoncentral 3) {i k : ι} (hik : i ≠ k)
    (hi : D.kind i ≠ CompData.sl23) {N : Subgroup G} {R : Subgroup (D.kind i).G}
    (hc : Q3W.Corr3 Ω z D i N R) {n : G} (hn : IsClassicalMember3 N n) {M : Subgroup G}
    (hM : M ∈ centralizingMembers Ω {z}) (hMk : locImg Ω z M ≤ (D.hom k).range) {m : G}
    (hm : IsClassicalMember3 M m) {zb : locQuot Ω z} (hzb : ∀ w, w * zb = zb * w) :
    locElt Ω z n (mem_locLayer_of_member hc.1 hn) ≠ zb ∧
      locElt Ω z n (mem_locLayer_of_member hc.1 hn) ≠ locElt Ω z m (mem_locLayer_of_member hM hm) ∧
      locElt Ω z n (mem_locLayer_of_member hc.1 hn) *
        locElt Ω z m (mem_locLayer_of_member hM hm) ≠ zb := by
  obtain ⟨y, hy⟩ := exists_noncommute_of_nonA1 D hMFZ hi hc hn
  have hmk : locElt Ω z m (mem_locLayer_of_member hM hm) ∈ (D.hom k).range :=
    hMk (locElt_mem_locImg (le_centralizingLayer hM) hm.mem)
  obtain ⟨x, hx⟩ := hmk
  have hby : locElt Ω z m (mem_locLayer_of_member hM hm) * D.hom i y =
      D.hom i y * locElt Ω z m (mem_locLayer_of_member hM hm) := by
    rw [← hx]
    exact D.commute k i hik.symm x y
  exact indep_of_noncommute hy hby (hzb _).symm

theorem exists_corr_of_meets (k : ι) :
    ∃ (M : Subgroup G) (R : Subgroup (D.kind k).G), Q3W.Corr3 Ω z D k M R := by
  obtain ⟨R, hR, hmem⟩ := D.meets k
  obtain ⟨M, hM, hMR⟩ := mem_locFamily_iff.mp hmem
  exact ⟨M, R, hM, hR, hMR⟩

theorem commutes_locImg_of_ne {i k : ι} (hik : i ≠ k) {N M : Subgroup G}
    (hN : locImg Ω z N ≤ (D.hom i).range) (hM : locImg Ω z M ≤ (D.hom k).range) :
    Commutes (locImg Ω z N) (locImg Ω z M) :=
  fun a ha b hb => Q3W.commutes_range3 D hik a (hN ha) b (hM hb)

end Components

end CFSG.ClassicalInvolution.Q3.Q3NL
