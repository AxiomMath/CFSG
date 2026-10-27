module

public import CFSG.ClassicalInvolution.Q3.Q3WANoA1
public import CFSG.ClassicalInvolution.Q3.Q3WAPow

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open scoped MatrixGroups commutatorElement

section Basic


variable {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem commutes_range3 (D : LieSystemData3 ι X Φ) {i j : ι} (h : i ≠ j) :
    Commutes (D.hom i).range (D.hom j).range := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  exact D.commute i j h a b

theorem exists_range_of_mem3 (D : LieSystemData3 ι X Φ) {L : Subgroup X}
    (hL : L ∈ Φ) : ∃ i, L ≤ (D.hom i).range := by
  obtain ⟨i, R, -, rfl⟩ := D.fundamental L hL
  exact ⟨i, Subgroup.map_le_range _ _⟩

theorem range_normal3 (D : LieSystemData3 ι X Φ) (i : ι) :
    ((D.hom i).range).Normal := by
  have hnormlz : ⨆ j, (D.hom j).range ≤ Subgroup.normalizer ((D.hom i).range : Set X) := by
    refine iSup_le fun j => ?_
    by_cases hji : j = i
    · subst hji
      exact Subgroup.le_normalizer
    · intro w hw
      rw [Subgroup.mem_normalizer_iff]
      have hfix : ∀ v ∈ (D.hom j).range, ∀ n ∈ (D.hom i).range, v * n * v⁻¹ = n := by
        intro v hv n hn
        have := commutes_range3 D hji v hv n hn
        calc v * n * v⁻¹ = (n * v) * v⁻¹ := by rw [this]
          _ = n := by group
      intro n
      constructor
      · intro hn
        rw [hfix w hw n hn]
        exact hn
      · intro hn
        have h2 := hfix w⁻¹ ((D.hom j).range.inv_mem hw) _ hn
        have h3 : n = w⁻¹ * (w * n * w⁻¹) * w⁻¹⁻¹ := by group
        rw [h3, h2]
        exact hn
  refine ⟨fun n hn g => ?_⟩
  have hg : g ∈ Subgroup.normalizer ((D.hom i).range : Set X) := by
    apply hnormlz
    rw [D.generate]
    exact Subgroup.mem_top g
  exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn

end Basic

section Members


variable {G : Type} [Group G] {ι : Type}

theorem locImg_not_commutes3 [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω)
    (hex : ExactMembers3 Ω) {x : G} (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    {N : Subgroup G} (hN : N ∈ centralizingMembers Ω {x}) :
    ¬ Commutes (locImg Ω x N) (locImg Ω x N) := by
  intro h
  obtain ⟨w, hw⟩ := hΩ.classical N hN.1
  exact not_commutes_self3 hw (commutes_of_commutes_locImg3 hΩ hex hP1 hO3 hN hN h)

@[expose] def compMembers3 (Ω : Set (Subgroup G)) (x : G)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) (i : ι) : Set (Subgroup G) :=
  {N | N ∈ centralizingMembers Ω {x} ∧ locImg Ω x N ≤ (D.hom i).range}

@[expose] def Corr3 (Ω : Set (Subgroup G)) (x : G)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) (i : ι) (N : Subgroup G)
    (R : Subgroup (D.kind i).G) : Prop :=
  N ∈ centralizingMembers Ω {x} ∧ R ∈ (D.kind i).fund ∧ locImg Ω x N = R.map (D.hom i)

variable [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem eq_of_locImg_le_range3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {i j : ι} {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {x}) (hi : locImg Ω x N ≤ (D.hom i).range)
    (hj : locImg Ω x N ≤ (D.hom j).range) : i = j := by
  by_contra hij
  exact locImg_not_commutes3 hΩ hex hP1 hO3 hN fun a ha b hb =>
    commutes_range3 D hij a (hi ha) b (hj hb)

theorem exists_corr_left3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {i : ι} {N : Subgroup G}
    (hN : N ∈ compMembers3 Ω x D i) : ∃ R, Corr3 Ω x D i N R := by
  obtain ⟨hNm, hi⟩ := hN
  obtain ⟨j, R, hR, hRN⟩ := D.fundamental _ (mem_locFamily_iff.mpr ⟨N, hNm, rfl⟩)
  have hj : locImg Ω x N ≤ (D.hom j).range := hRN ▸ Subgroup.map_le_range _ _
  have hij := eq_of_locImg_le_range3 hΩ hex hP1 hO3 D hNm hj hi
  subst hij
  exact ⟨R, hNm, hR, hRN⟩

theorem exists_unique_comp3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {x}) : ∃! i, N ∈ compMembers3 Ω x D i := by
  obtain ⟨i, hi⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
  exact ⟨i, ⟨hN, hi⟩, fun j hj => eq_of_locImg_le_range3 hΩ hex hP1 hO3 D hN hj.2 hi⟩

theorem commutes_of_ne_comp3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {i j : ι} (hij : i ≠ j)
    {N N' : Subgroup G} (hN : N ∈ compMembers3 Ω x D i) (hN' : N' ∈ compMembers3 Ω x D j) :
    Commutes N N' :=
  commutes_of_commutes_locImg3 hΩ hex hP1 hO3 hN.1 hN'.1 fun a ha b hb =>
    commutes_range3 D hij a (hN.2 ha) b (hN'.2 hb)

omit [Finite G] in
theorem exists_corr_right3 (hΩ : InClass3 Ω) (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x))
    {i : ι} (hsc : ∀ R ∈ (D.kind i).fund, ∀ R' ∈ (D.kind i).fund, ∃ g, R' = conjSub g R)
    {R : Subgroup (D.kind i).G} (hR : R ∈ (D.kind i).fund) : ∃ N, Corr3 Ω x D i N R := by
  obtain ⟨R₁, hR₁, hmem⟩ := D.meets i
  obtain ⟨N₁, hN₁, hN₁R⟩ := mem_locFamily_iff.mp hmem
  obtain ⟨g, hg⟩ := hsc R₁ hR₁ R hR
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (D.hom i g)
  have hyx : (y : G) ∈ Subgroup.centralizer ({x} : Set G) :=
    centralizingLayer_le_centralizer Ω {x} y.2
  refine ⟨conjSub (y : G) N₁, ⟨hΩ.conjInvariant _ N₁ hN₁.1, fun a ha => ?_⟩, hR, ?_⟩
  · rw [mem_conjSub_iff] at ha
    have hx' := hN₁.2 ha
    have : a = (y : G) * ((y : G)⁻¹ * a * (y : G)) * (y : G)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyx hx') ((Subgroup.inv_mem _) hyx)
  · rw [Gaps.locImg_conjSub_layer, hN₁R, show Gaps.locMk Ω x y = D.hom i g from hy, hg]
    unfold conjSub
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext a
    simp

theorem corr_unique_right3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    {D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)} {i : ι} {N N' : Subgroup G}
    {R : Subgroup (D.kind i).G} (h : Corr3 Ω x D i N R) (h' : Corr3 Ω x D i N' R) : N = N' :=
  locImg_injOn3 hΩ hex hP1 hO3 h.1 h'.1 (h.2.2.trans h'.2.2.symm)

end Members

section Kinds


structure PowCop3 (c : CompData) : Prop where
  pow3 : ∀ R ∈ c.fund, Pow3 R
  cop : ∀ w ∈ Subgroup.center c.G, ¬ 3 ∣ orderOf w

theorem not_three_dvd_orderOf_of_isPGroup_two {A : Type} [Group A]
    (h : IsPGroup 2 (Subgroup.center A)) : ∀ w ∈ Subgroup.center A, ¬ 3 ∣ orderOf w := by
  intro w hw h3
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h) ⟨w, hw⟩
  rw [Subgroup.orderOf_mk] at hk
  rw [hk] at h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem powCop3_model {t : StatedLieTag} {n : ℕ} (hft : IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) :
    PowCop3 (CompData.model t n) where
  pow3 := fun R hR => by
    obtain ⟨e⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3)
      (by norm_num) hft hadm hG2 hD4 hR
    exact pow_three_mem_commutator_of_equiv card_gf3 e
  cop := not_three_dvd_orderOf_of_isPGroup_two
    (modelFiniteCenterTwoGroup3 t n Nat.prime_three hft hadm).2

theorem powCop3_sl23 : PowCop3 CompData.sl23 where
  pow3 := fun R hR => by
    have hR' : R = ⊤ := hR
    subst hR'
    exact pow_three_mem_commutator_of_equiv (K := ZMod 3) (by simp)
      (Subgroup.topEquiv (G := SL(2, ZMod 3)))
  cop := fun w hw h3 => by
    rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff w).mp hw with h | h
    · rw [h, orderOf_one] at h3
      omega
    · have h2 : (-1 : SL(2, ZMod 3)) ^ 2 = 1 := by
        rw [pow_two]
        have := mul_inv_cancel (-1 : SL(2, ZMod 3))
        rwa [CFSG.ClassicalInvolution.Generic.neg_one_inv] at this
      have := Nat.le_of_dvd (by norm_num) (h3.trans (h ▸ orderOf_dvd_of_pow_eq_one h2))
      omega

theorem powCop3_m11 : PowCop3 CompData.m11 where
  pow3 := fun R hR => by
    obtain ⟨w, hw⟩ := hR
    have hcard : Nat.card R = 24 :=
      hw.card_eq_of_mulEquiv_m11 (MulEquiv.refl ↥CFSG.Blueprint.NativeSporadic.M11)
    obtain ⟨e'⟩ := hw.nonempty_equiv
    have hq : Nat.card (R ⧸ classicalInvolutionOddCore R) = 24 := by
      rw [Nat.card_congr e'.toEquiv, natCard_sl2Three]
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore R)
    rw [hq, hcard] at hmul
    have h1 : Nat.card (classicalInvolutionOddCore R) = 1 := by omega
    have hO : classicalInvolutionOddCore R = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    obtain ⟨e⟩ := hw.nonempty_equiv_sl2 hO
    exact pow_three_mem_commutator_of_equiv (K := ZMod 3) (by simp) e
  cop := fun w hw h3 => by
    rw [center_m11_eq_bot, Subgroup.mem_bot] at hw
    subst hw
    rw [orderOf_one] at h3
    omega

end Kinds

section Corr


variable {G : Type} [Group G] {ι : Type} {Ω : Set (Subgroup G)} {x : G}

theorem corr_unique_left3 {D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)} {i : ι}
    (hk : PowCop3 (D.kind i)) {N : Subgroup G} {R R' : Subgroup (D.kind i).G}
    (h : Corr3 Ω x D i N R) (h' : Corr3 Ω x D i N R') : R = R' :=
  eq_of_map_eq_of_pow3 (D.hom i) (D.ker_le_center i)
    (fun w hw => hk.cop w (D.ker_le_center i hw)) (hk.pow3 R h.2.1) (hk.pow3 R' h'.2.1)
    (h.2.2.symm.trans h'.2.2)

variable [Finite G]

theorem corr_commutes3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) (hP1 : LocalOddCentral Ω {x})
    (hO3 : LocalOddThreeFree3 Ω x) {D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)} {i : ι}
    (hk : PowCop3 (D.kind i)) {N N' : Subgroup G} {R R' : Subgroup (D.kind i).G}
    (h : Corr3 Ω x D i N R) (h' : Corr3 Ω x D i N' R') : Commutes N N' ↔ Commutes R R' := by
  constructor
  · intro hc
    have h1 := commutes_locImg_of_commutes (x := x) (Ω := Ω) hc
    rw [h.2.2, h'.2.2] at h1
    intro a ha b hb
    exact (commutes_of_map_commute_exponent3 (D.hom i) (D.ker_le_center i)
      (fun w hw => hk.cop w (D.ker_le_center i hw)) (A := R') (L := R) (hk.pow3 R h.2.1)
      (fun a' ha' l hl => (h1 _ ⟨l, hl, rfl⟩ _ ⟨a', ha', rfl⟩).symm) b hb a ha).symm
  · intro hc
    refine commutes_of_commutes_locImg3 hΩ hex hP1 hO3 h.1 h'.1 ?_
    rw [h.2.2, h'.2.2]
    exact commutes_map_of_commutes _ hc

end Corr

section Blocks


variable {G : Type} [Group G] {ι : Type} {Ω : Set (Subgroup G)} {x : G}

theorem conjSub_mem_compMembers3 (hΩ : InClass3 Ω)
    {D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)} {i : ι} {N : Subgroup G}
    (hN : N ∈ compMembers3 Ω x D i) (y : ↥(locLayer Ω x)) :
    conjSub (y : G) N ∈ compMembers3 Ω x D i := by
  obtain ⟨⟨hNΩ, hNC⟩, hNi⟩ := hN
  refine ⟨⟨hΩ.conjInvariant _ _ hNΩ,
    conjSub_le_centralizer_of_mem (centralizingLayer_le_centralizer Ω {x} y.2) hNC⟩, ?_⟩
  rw [Gaps.locImg_conjSub_layer]
  intro u hu
  obtain ⟨a, ha, rfl⟩ := hu
  exact (range_normal3 D i).conj_mem _ (hNi ha) _

variable [Finite G]

theorem range_le_iSup_locImg3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    {D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)} {i : ι}
    (hq : CFSG.Open.IsQuasisimple (D.hom i).range) {a : Subgroup G}
    (ha : a ∈ compMembers3 Ω x D i) :
    (D.hom i).range ≤ ⨆ N : ↥(compMembers3 Ω x D i), locImg Ω x N.1 := by
  set H : Subgroup (locQuot Ω x) := ⨆ N : ↥(compMembers3 Ω x D i), locImg Ω x N.1 with hHdef
  have hHle : H ≤ (D.hom i).range := iSup_le fun N => N.2.2
  have hnorm : H.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    induction hn using Subgroup.iSup_induction' with
    | hp N u hu =>
      have hmem : conjSub (y : G) N.1 ∈ compMembers3 Ω x D i :=
        conjSub_mem_compMembers3 hΩ N.2 y
      have h1 : Gaps.locMk Ω x y * u * (Gaps.locMk Ω x y)⁻¹ ∈
          locImg Ω x (conjSub (y : G) N.1) := by
        rw [Gaps.locImg_conjSub_layer]
        exact ⟨u, hu, rfl⟩
      exact (le_iSup (fun N : ↥(compMembers3 Ω x D i) => locImg Ω x N.1)
        ⟨conjSub (y : G) N.1, hmem⟩) h1
    | h1 => simp
    | hmul u v _ _ hu hv =>
      have e : (y : locQuot Ω x) * (u * v) * (y : locQuot Ω x)⁻¹ =
          ((y : locQuot Ω x) * u * (y : locQuot Ω x)⁻¹) *
            ((y : locQuot Ω x) * v * (y : locQuot Ω x)⁻¹) := by group
      rw [e]
      exact H.mul_mem hu hv
  have hsub : (H.subgroupOf (D.hom i).range).Normal := hnorm.subgroupOf _
  rcases normal_eq_top_or_le_center hq hsub with h | h
  · exact Subgroup.subgroupOf_eq_top.mp h
  · exfalso
    refine locImg_not_commutes3 hΩ hex hP1 hO3 ha.1 fun u hu v hv => ?_
    have hu' : (⟨u, ha.2 hu⟩ : ↥(D.hom i).range) ∈ H.subgroupOf (D.hom i).range :=
      Subgroup.mem_subgroupOf.mpr ((le_iSup (fun N : ↥(compMembers3 Ω x D i) =>
        locImg Ω x N.1) ⟨a, ha⟩) hu)
    have := Subgroup.mem_center_iff.mp (h hu') ⟨v, ha.2 hv⟩
    exact congrArg Subtype.val this.symm

theorem eq_of_not_commutes3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {A B : Subgroup G} {i j : ι}
    (hA : A ∈ compMembers3 Ω x D i) (hB : B ∈ compMembers3 Ω x D j) (hnc : ¬ Commutes A B) :
    i = j := by
  by_contra hij
  exact hnc (commutes_of_ne_comp3 hΩ hex hP1 hO3 D hij hA hB)

theorem linked_le_range3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {A B : Subgroup G}
    (h : NonClassical.Linked Ω x A B) {i : ι} (hA : locImg Ω x A ≤ (D.hom i).range) :
    locImg Ω x B ≤ (D.hom i).range := by
  induction h with
  | refl => exact hA
  | @tail b c _ hbc ih =>
    obtain ⟨hb, hc, hnc⟩ := hbc
    obtain ⟨j, hj⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨c, hc, rfl⟩)
    have := eq_of_not_commutes3 hΩ hex hP1 hO3 D (A := b) (B := c) ⟨hb, ih⟩ ⟨hc, hj⟩ hnc
    exact this ▸ hj

theorem linked_of_mem_compMembers3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    {D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)} {i : ι}
    (hq : CFSG.Open.IsQuasisimple (D.hom i).range) {a b : Subgroup G}
    (ha : a ∈ compMembers3 Ω x D i) (hb : b ∈ compMembers3 Ω x D i) :
    NonClassical.Linked Ω x a b := by
  by_contra hnb
  let E : Set (Subgroup G) := {N | N ∈ compMembers3 Ω x D i ∧ NonClassical.Linked Ω x a N}
  let E' : Set (Subgroup G) := {N | N ∈ compMembers3 Ω x D i ∧ ¬ NonClassical.Linked Ω x a N}
  let H₁ : Subgroup (locQuot Ω x) := ⨆ N : ↥E, locImg Ω x N.1
  let H₂ : Subgroup (locQuot Ω x) := ⨆ N : ↥E', locImg Ω x N.1
  have hcomm : Commutes H₁ H₂ := by
    refine commutes_iSup_iSup fun N N' => commutes_locImg_of_commutes ?_
    by_contra hc
    exact N'.2.2 (N.2.2.trans (NonClassical.Linked.single ⟨N.2.1.1, N'.2.1.1, hc⟩))
  have hcover : (D.hom i).range ≤ H₁ ⊔ H₂ := by
    refine (range_le_iSup_locImg3 hΩ hex hP1 hO3 hq ha).trans (iSup_le fun N => ?_)
    by_cases hN : NonClassical.Linked Ω x a N.1
    · exact (le_iSup (fun N : ↥E => locImg Ω x N.1) ⟨N.1, N.2, hN⟩).trans le_sup_left
    · exact (le_iSup (fun N : ↥E' => locImg Ω x N.1) ⟨N.1, N.2, hN⟩).trans le_sup_right
  have hH₁le : H₁ ≤ (D.hom i).range := iSup_le fun N => N.2.1.2
  have hnormlz : H₁ ⊔ H₂ ≤ Subgroup.normalizer (H₁ : Set (locQuot Ω x)) := by
    refine sup_le Subgroup.le_normalizer fun w hw => ?_
    rw [Subgroup.mem_normalizer_iff]
    have hfix : ∀ w ∈ H₂, ∀ h ∈ H₁, w * h * w⁻¹ = h := by
      intro w hw h hh
      have := hcomm h hh w hw
      calc w * h * w⁻¹ = (h * w) * w⁻¹ := by rw [this]
        _ = h := by group
    intro n
    constructor
    · intro hn
      rw [hfix w hw n hn]
      exact hn
    · intro hn
      have h2 := hfix w⁻¹ (H₂.inv_mem hw) _ hn
      have h3 : n = w⁻¹ * (w * n * w⁻¹) * w⁻¹⁻¹ := by group
      rw [h3, h2]
      exact hn
  have hsub : (H₁.subgroupOf (D.hom i).range).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hnormlz (hcover g.2)) n).mp hn
    exact this
  have haE : a ∈ E := ⟨ha, Relation.ReflTransGen.refl⟩
  have haH₁ : locImg Ω x a ≤ H₁ := le_iSup (fun N : ↥E => locImg Ω x N.1) ⟨a, haE⟩
  have hrange : (D.hom i).range ≤ H₁ := by
    rcases normal_eq_top_or_le_center hq hsub with h | h
    · exact Subgroup.subgroupOf_eq_top.mp h
    · exfalso
      refine locImg_not_commutes3 hΩ hex hP1 hO3 ha.1 fun u hu v hv => ?_
      have hu' : (⟨u, ha.2 hu⟩ : ↥(D.hom i).range) ∈ H₁.subgroupOf (D.hom i).range :=
        Subgroup.mem_subgroupOf.mpr (haH₁ hu)
      have := Subgroup.mem_center_iff.mp (h hu') ⟨v, ha.2 hv⟩
      exact congrArg Subtype.val this.symm
  have hbE' : b ∈ E' := ⟨hb, hnb⟩
  have hbH₂ : locImg Ω x b ≤ H₂ := le_iSup (fun N : ↥E' => locImg Ω x N.1) ⟨b, hbE'⟩
  refine locImg_not_commutes3 hΩ hex hP1 hO3 hb.1 fun u hu v hv => ?_
  exact hcomm u (hrange (hb.2 hu)) v (hbH₂ hv)

omit [Finite G] in
theorem exists_mem_compMembers3 {D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)} (i : ι) :
    ∃ N, N ∈ compMembers3 Ω x D i := by
  obtain ⟨R, -, hR⟩ := D.meets i
  obtain ⟨N, hN, hNR⟩ := mem_locFamily_iff.mp hR
  exact ⟨N, hN, hNR ▸ Subgroup.map_le_range _ _⟩

end Blocks

section KindCases


variable {G : Type} [Group G] {ι : Type} {Ω : Set (Subgroup G)} {x : G}

theorem isQuasisimple_range3 {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) (i : ι) (hq : CFSG.Open.IsQuasisimple (D.kind i).G) :
    CFSG.Open.IsQuasisimple (D.hom i).range := by
  have hq' := CFSG.ComponentClassification.Quasisimple.central_quotient hq (D.hom i).ker
    (D.ker_le_center i)
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (QuotientGroup.quotientKerEquivRange (D.hom i)).symm hq'

theorem eq_top_of_mem_fund_sl23 {c : CompData} (hc : c = CompData.sl23) {R : Subgroup c.G}
    (hR : R ∈ c.fund) : R = ⊤ := by
  subst hc
  exact hR

theorem kind_cases_of_not_a1 {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) {i : ι} (hi : ¬ IsA1Comp3 D i) :
    (∃ (t : StatedLieTag) (n : ℕ), IsFundTag t ∧ StatedLieAdmissible t n 3 1 ∧
      D.kind i = CompData.model t n) ∨ D.kind i = CompData.m11 := by
  rcases D.valid i with h | h | h
  · exact Or.inl h
  · exact absurd h hi
  · exact Or.inr h

variable [Finite G]

theorem eq_of_mem_compMembers_a13 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    {D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)} {i : ι} (hi : IsA1Comp3 D i)
    {N N' : Subgroup G} (hN : N ∈ compMembers3 Ω x D i) (hN' : N' ∈ compMembers3 Ω x D i) :
    N = N' := by
  have key : ∀ M ∈ compMembers3 Ω x D i, locImg Ω x M = (D.hom i).range := by
    intro M hM
    obtain ⟨R, hRM⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hM
    rw [hRM.2.2, eq_top_of_mem_fund_sl23 hi hRM.2.1, Subgroup.map_top]
  exact locImg_injOn3 hΩ hex hP1 hO3 hN.1 hN'.1 ((key N hN).trans (key N' hN').symm)

theorem linked_iff_mem_compMembers3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    {D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)} {i : ι}
    (hqk : CFSG.Open.IsQuasisimple (D.kind i).G ∨ IsA1Comp3 D i) {a B : Subgroup G}
    (ha : a ∈ compMembers3 Ω x D i) :
    NonClassical.Linked Ω x a B ↔ B ∈ compMembers3 Ω x D i := by
  refine ⟨fun h => ⟨h.mem_centralizingMembers ha.1, linked_le_range3 hΩ hex hP1 hO3 D h ha.2⟩,
    fun h => ?_⟩
  rcases hqk with hq | hA
  · exact linked_of_mem_compMembers3 hΩ hex hP1 hO3 (isQuasisimple_range3 D i hq) ha h
  · have := eq_of_mem_compMembers_a13 hΩ hex hP1 hO3 hA ha h
    subst this
    exact Relation.ReflTransGen.refl

end KindCases

section M11Facts

theorem isQuasisimple_m11 : CFSG.Open.IsQuasisimple ↥CFSG.Blueprint.NativeSporadic.M11 := by
  have hs : IsSimpleGroup ↥CFSG.Blueprint.NativeSporadic.M11 := isSimpleGroup_m11_kernel
  have hZ := center_m11_eq_bot
  have hcomm : commutator ↥CFSG.Blueprint.NativeSporadic.M11 = ⊤ := by
    rcases hs.eq_bot_or_eq_top_of_normal (commutator ↥CFSG.Blueprint.NativeSporadic.M11) with
      h | h
    · exfalso
      have hab : ∀ a b : ↥CFSG.Blueprint.NativeSporadic.M11, a * b = b * a := by
        intro a b
        have : ⁅a, b⁆ ∈ commutator ↥CFSG.Blueprint.NativeSporadic.M11 :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
        exact this
      have hcen : (⊤ : Subgroup ↥CFSG.Blueprint.NativeSporadic.M11) ≤
          Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M11 := fun a _ =>
        Subgroup.mem_center_iff.mpr fun b => hab b a
      rw [hZ] at hcen
      have : Subsingleton ↥CFSG.Blueprint.NativeSporadic.M11 :=
        ⟨fun a b => by
          have ha := hcen (Subgroup.mem_top a)
          have hb := hcen (Subgroup.mem_top b)
          rw [Subgroup.mem_bot] at ha hb
          rw [ha, hb]⟩
      exact not_subsingleton _ ‹_›
    · exact h
  refine ⟨hcomm, ?_⟩
  let e : (↥CFSG.Blueprint.NativeSporadic.M11 ⧸
      Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M11) ≃*
      ↥CFSG.Blueprint.NativeSporadic.M11 :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact e.isSimpleGroup_congr.mpr hs

theorem modelFacts_isFundTag {t : StatedLieTag} (h : IsFundTag t) : ModelFacts.IsFundTag t := by
  cases t <;> trivial

theorem not_psl_two_of_admissible3 {t : StatedLieTag} {n : ℕ}
    (hadm : StatedLieAdmissible t n 3 1) : ¬ (t = .PSL ∧ n = 2) :=
  CFSG.Open.StatedAPI.not_psl_two_of_statedLieAdmissible_three_one hadm

end M11Facts

section NotA1



variable {G : Type} [Group G] {ι : Type} {Ω : Set (Subgroup G)} {x : G}

theorem isQuasisimple_of_not_a1 {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) {i : ι} (hi : ¬ IsA1Comp3 D i) :
    CFSG.Open.IsQuasisimple (D.kind i).G := by
  rcases kind_cases_of_not_a1 D hi with ⟨t, n, hft, hadm, hk⟩ | hk
  · have key : ∀ c : CompData, c = CompData.model t n → CFSG.Open.IsQuasisimple c.G := by
      rintro c rfl
      exact (ModelFacts.modelClauseZero t n 3 1 Nat.prime_three (modelFacts_isFundTag hft)
        hadm).1
    exact key _ hk
  · have key : ∀ c : CompData, c = CompData.m11 → CFSG.Open.IsQuasisimple c.G := by
      rintro c rfl
      exact isQuasisimple_m11
    exact key _ hk

variable [Finite G]

theorem exists_ne_of_not_isA1Comp3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    {D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)} {i : ι} (hi : ¬ IsA1Comp3 D i) :
    ∃ N N' : Subgroup G, N ∈ compMembers3 Ω x D i ∧ N' ∈ compMembers3 Ω x D i ∧ N ≠ N' := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha⟩ := exists_mem_compMembers3 (D := D) (x := x) (Ω := Ω) i
  have hq := isQuasisimple_of_not_a1 D hi
  have hrange : (D.hom i).range ≤ locImg Ω x a := by
    refine (range_le_iSup_locImg3 hΩ hex hP1 hO3 (isQuasisimple_range3 D i hq) ha).trans
      (iSup_le fun N => ?_)
    have : N.1 = a := hcon N.1 a N.2 ha
    rw [this]
  obtain ⟨R, hRM⟩ := exists_corr_left3 hΩ hex hP1 hO3 D ha
  have hperf : (⊤ : Subgroup (D.kind i).G) ≤ ⁅(⊤ : Subgroup (D.kind i).G), ⊤⁆ := by
    rw [← _root_.commutator_def, hq.1]
  have hsup : (⊤ : Subgroup (D.kind i).G) ≤ R ⊔ (D.hom i).ker := by
    intro k _
    have hk' : D.hom i k ∈ R.map (D.hom i) := hRM.2.2 ▸ hrange ⟨k, rfl⟩
    obtain ⟨r, hr, hrk⟩ := hk'
    have hmem : r⁻¹ * k ∈ (D.hom i).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hrk, inv_mul_cancel]
    have : k = r * (r⁻¹ * k) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right hmem)
  have hRtop : R = ⊤ :=
    eq_top_iff.mpr (le_of_perfect_of_le_sup_center (D.ker_le_center i) hperf hsup)
  rcases kind_cases_of_not_a1 D hi with ⟨t, n, hft, hadm, hk⟩ | hk
  · have key : ∀ c : CompData, c = CompData.model t n → ∀ R : Subgroup c.G, R ∈ c.fund →
        R ≠ ⊤ := by
      rintro c rfl R hR
      exact (ModelFacts.fundamentalIsWhole_modelUniv t n 3 1 Nat.prime_three
        (modelFacts_isFundTag hft) hadm).2 (not_psl_two_of_admissible3 hadm) R hR
    exact key _ hk R hRM.2.1 hRtop
  · have key : ∀ c : CompData, c = CompData.m11 → ∀ R : Subgroup c.G, R ∈ c.fund → R ≠ ⊤ := by
      rintro c rfl R hR hRt
      obtain ⟨w, hw⟩ := hR
      have h24 : Nat.card R = 24 :=
        hw.card_eq_of_mulEquiv_m11 (MulEquiv.refl ↥CFSG.Blueprint.NativeSporadic.M11)
      rw [hRt, Subgroup.card_top, card_m11_kernel] at h24
      omega
    exact key _ hk R hRM.2.1 hRtop

end NotA1

section Involution


variable {G : Type} [Group G] {ι : Type} {Ω : Set (Subgroup G)} {x : G}

theorem localOddThreeFree3_conj (hΩ : ConjInvariant Ω) (g x : G)
    (h : LocalOddThreeFree3 Ω x) : LocalOddThreeFree3 Ω (g * x * g⁻¹) := by
  have hO : (classicalInvolutionOddCore ↥(locLayer Ω x)).map
      (Gaps.locLayerConj hΩ g x).toMonoidHom =
      classicalInvolutionOddCore ↥(locLayer Ω (g * x * g⁻¹)) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant (Gaps.locLayerConj hΩ g x)
  unfold LocalOddThreeFree3 at h ⊢
  rw [← hO, Subgroup.card_map_of_injective (f := (Gaps.locLayerConj hΩ g x).toMonoidHom)
    (Gaps.locLayerConj hΩ g x).injective]
  exact h

theorem linearBlockStandardPair_of_corr3 [Finite G] (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    {D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)} {i : ι} {N N' : Subgroup G}
    {R R' : Subgroup (D.kind i).G} (h : Corr3 Ω x D i N R) (h' : Corr3 Ω x D i N' R')
    (hpair : ∃ W, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W R R') :
    ∃ W' : Subgroup G, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W' N N' := by
  obtain ⟨W, hW⟩ := hpair
  have h1 := linearBlockStandardPair_map_central hW (D.hom i) (D.ker_le_center i)
  rw [← h.2.2, ← h'.2.2] at h1
  exact linearBlockStandardPair_of_locImg3' hΩ hex hP1 hO3 h.1 h'.1 h1

theorem locImg_eq_range_of_involution3 (hMFZ : RouteD.Gaps.FundNoncentral 3) [Finite G]
    {D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)} {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {x}) (hx : IsClassicalMember3 N x) :
    ∃ i, IsA1Comp3 D i ∧ locImg Ω x N = (D.hom i).range := by
  have hmem : locImg Ω x N ∈ locFamily Ω x := mem_locFamily_iff.mpr ⟨N, hN, rfl⟩
  obtain ⟨i, R, hR, hRN⟩ := D.fundamental _ hmem
  have hxY : x ∈ locLayer Ω x := le_centralizingLayer hN hx.mem
  have hxN : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨x, hxY⟩ ∈
      locImg Ω x N := ⟨⟨x, hxY⟩, Subgroup.mem_subgroupOf.mpr hx.mem, rfl⟩
  rw [hRN] at hxN
  obtain ⟨r, hrR, hr⟩ := hxN
  by_cases hc : D.kind i = CompData.sl23
  · refine ⟨i, hc, ?_⟩
    rw [hRN, eq_top_of_mem_fund_sl23 hc hR, Subgroup.map_top]
  · exfalso
    have hr1 : r = 1 :=
      eq_one_of_central_comp3 hMFZ (D.kind i) (D.valid i) hc (D.hom i) (D.ker_le_center i) hR hrR
        fun y => by
          rw [hr]
          exact (mk_involution_central3 Ω x hxY (D.hom i y)).symm
    rw [hr1, map_one] at hr
    exact mk_involution_ne_one3 Ω hx.orderOf_eq_two hxY hr.symm

theorem commutes_or_eq_of_involution3 (hMFZ : RouteD.Gaps.FundNoncentral 3) [Finite G]
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) (hP1 : LocalOddCentral Ω {x})
    (hO3 : LocalOddThreeFree3 Ω x) (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x))
    {N L : Subgroup G} (hN : N ∈ centralizingMembers Ω {x}) (hL : L ∈ centralizingMembers Ω {x})
    (hx : IsClassicalMember3 N x) : Commutes N L ∨ L = N := by
  obtain ⟨i, hA, hi⟩ := locImg_eq_range_of_involution3 (D := D) hMFZ hN hx
  obtain ⟨j, hj⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨L, hL, rfl⟩)
  by_cases hij : j = i
  · subst hij
    exact Or.inr (eq_of_mem_compMembers_a13 hΩ hex hP1 hO3 hA ⟨hL, hj⟩ ⟨hN, hi.le⟩)
  · exact Or.inl (commutes_of_ne_comp3 hΩ hex hP1 hO3 D (Ne.symm hij) ⟨hN, hi.le⟩ ⟨hL, hj⟩)

end Involution

end CFSG.ClassicalInvolution.Q3.Q3W
