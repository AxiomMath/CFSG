module

public import CFSG.ClassicalInvolution.Q3.Q3PPKlein
public import CFSG.ClassicalInvolution.Q3.Q3PPEdgeTwo

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Q3.Q3W


section Data

structure KleinData (c : CompData) : Prop where
  center : Subgroup.center c.G = ⊥
  unique_inv : ∀ R ∈ c.fund, ∀ a ∈ R, ∀ b ∈ R, a * a = 1 → b * b = 1 → a ≠ 1 → b ≠ 1 → a = b
  conj_fund : ∀ R ∈ c.fund, ∀ g : c.G, conjSub g R ∈ c.fund
  klein : ∀ R ∈ c.fund, ∀ r ∈ R, r * r = 1 → r ≠ 1 →
    ∃ r' g' g'' : c.G, r' = g' * r * g'⁻¹ ∧ r * r' = g'' * r * g''⁻¹ ∧ r' * r = r * r' ∧
      r' ≠ r

end Data

section Members

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G} {ι : Type}

theorem exists_corr_conj3 (hΩ : InClass3 Ω)
    {D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)} {i : ι} {N : Subgroup G}
    {R : Subgroup (D.kind i).G} (h : Corr3 Ω x D i N R) (g : (D.kind i).G)
    (hfund : conjSub g R ∈ (D.kind i).fund) : ∃ N', Corr3 Ω x D i N' (conjSub g R) := by
  obtain ⟨hNm, -, hNR⟩ := h
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (D.hom i g)
  have hyx : (y : G) ∈ Subgroup.centralizer ({x} : Set G) :=
    centralizingLayer_le_centralizer Ω {x} y.2
  refine ⟨conjSub (y : G) N, ⟨hΩ.conjInvariant _ N hNm.1, fun a ha => ?_⟩, hfund, ?_⟩
  · rw [mem_conjSub_iff] at ha
    have hx' := hNm.2 ha
    have : a = (y : G) * ((y : G)⁻¹ * a * (y : G)) * (y : G)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyx hx') ((Subgroup.inv_mem _) hyx)
  · rw [Gaps.locImg_conjSub_layer, hNR, show Gaps.locMk Ω x y = D.hom i g from hy]
    unfold conjSub
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext a
    simp

theorem exists_klein_members (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (hOY : classicalInvolutionOddCore ↥(locLayer Ω x) = ⊥)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {i : ι} (hKd : KleinData (D.kind i))
    {N : Subgroup G} {u : G} (hN : N ∈ compMembers3 Ω x D i) (hu : IsClassicalMember3 N u) :
    ∃ (M₁ M₂ : Subgroup G) (w : G), M₁ ∈ compMembers3 Ω x D i ∧ M₂ ∈ compMembers3 Ω x D i ∧
      IsClassicalMember3 M₁ w ∧ IsClassicalMember3 M₂ (u * w) ∧ w * u = u * w ∧ w ≠ u := by
  classical
  have hπinj : ∀ a b : ↥(locLayer Ω x),
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) a =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) b → a = b := by
    intro a b h
    have h1 : a⁻¹ * b ∈ classicalInvolutionOddCore ↥(locLayer Ω x) := QuotientGroup.eq.mp h
    rw [hOY, Subgroup.mem_bot] at h1
    exact inv_mul_eq_one.mp h1
  have hψinj : Function.Injective (D.hom i) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    have := D.ker_le_center i ha
    rw [hKd.center] at this
    exact this
  obtain ⟨R, hNm, hRf, hNR⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hN
  have hNY : N ≤ locLayer Ω x := le_centralizingLayer hNm
  have hu' : u ∈ locLayer Ω x := hNY hu.mem
  have hclN : IsClassicalMember3 (locImg Ω x N)
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨u, hu'⟩) :=
    (hu.subgroupOf hNY).map_oddQuotient
  have hsqw : ∀ {M : Subgroup G} {w : G}, IsClassicalMember3 M w → w * w = 1 := fun hw =>
    Q3NT.mul_self_eq_one_of_orderOf_eq_two hw.orderOf_eq_two
  have himg : ∀ {M : Subgroup G} {w : G} (hM : M ∈ centralizingMembers Ω {x})
      (hw : IsClassicalMember3 M w) (R' : Subgroup (D.kind i).G) (r' : (D.kind i).G),
      locImg Ω x M = R'.map (D.hom i) → R' ∈ (D.kind i).fund → r' ∈ R' → r' * r' = 1 →
      r' ≠ 1 → ∀ hw' : w ∈ locLayer Ω x,
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w, hw'⟩ = D.hom i r' := by
    intro M w hM hw R' r' hMR hR'f hr'R hr'2 hr'1 hw'
    have hcl : IsClassicalMember3 (locImg Ω x M)
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w, hw'⟩) :=
      (hw.subgroupOf (le_centralizingLayer hM)).map_oddQuotient
    have hmem : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w, hw'⟩ ∈
        R'.map (D.hom i) := by
      rw [← hMR]
      exact hcl.mem
    obtain ⟨s, hsR, hs⟩ := hmem
    have hw2 : (⟨w, hw'⟩ : ↥(locLayer Ω x)) * ⟨w, hw'⟩ = 1 := Subtype.ext (hsqw hw)
    have hsq' : D.hom i (s * s) = 1 := by
      rw [map_mul, hs, ← map_mul, hw2, map_one]
    have hs2 : s * s = 1 := hψinj (by rw [hsq', map_one])
    have hs1 : s ≠ 1 := by
      intro h1
      apply hcl.ne_one
      rw [← hs, h1, map_one]
    have hsr : s = r' := hKd.unique_inv R' hR'f s hsR r' hr'R hs2 hr'2 hs1 hr'1
    rw [← hs, hsr]
  have hmemN : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨u, hu'⟩ ∈
      R.map (D.hom i) := by
    rw [← hNR]
    exact hclN.mem
  obtain ⟨r, hrR, hr⟩ := hmemN
  have hu2 : (⟨u, hu'⟩ : ↥(locLayer Ω x)) * ⟨u, hu'⟩ = 1 := Subtype.ext (hsqw hu)
  have hr2 : r * r = 1 := hψinj (by rw [map_mul, hr, ← map_mul, hu2, map_one, map_one])
  have hr1 : r ≠ 1 := by
    intro h1
    apply hclN.ne_one
    rw [← hr, h1, map_one]
  obtain ⟨r', g', g'', hr'def, hrr'def, hr'comm, hr'ne⟩ := hKd.klein R hRf r hrR hr2 hr1
  have hR'f : conjSub g' R ∈ (D.kind i).fund := hKd.conj_fund R hRf g'
  have hR''f : conjSub g'' R ∈ (D.kind i).fund := hKd.conj_fund R hRf g''
  have hr'R' : r' ∈ conjSub g' R := by
    rw [hr'def]
    exact conj_mem_conjSub hrR
  have hr'2 : r' * r' = 1 := by
    rw [hr'def]
    calc g' * r * g'⁻¹ * (g' * r * g'⁻¹) = g' * (r * r) * g'⁻¹ := by group
      _ = 1 := by rw [hr2]; group
  have hr'1 : r' ≠ 1 := by
    intro h1
    apply hr1
    have : r = g'⁻¹ * (g' * r * g'⁻¹) * g' := by group
    rw [this, ← hr'def, h1]
    group
  have hrr'R'' : r * r' ∈ conjSub g'' R := by
    rw [hrr'def]
    exact conj_mem_conjSub hrR
  have hrr'2 : (r * r') * (r * r') = 1 := by
    rw [hrr'def]
    calc g'' * r * g''⁻¹ * (g'' * r * g''⁻¹) = g'' * (r * r) * g''⁻¹ := by group
      _ = 1 := by rw [hr2]; group
  have hrr'1 : r * r' ≠ 1 := by
    intro h1
    apply hr1
    have : r = g''⁻¹ * (g'' * r * g''⁻¹) * g'' := by group
    rw [this, ← hrr'def, h1]
    group
  obtain ⟨M₁, hM₁m, -, hM₁R⟩ := exists_corr_conj3 hΩ ⟨hNm, hRf, hNR⟩ g' hR'f
  obtain ⟨M₂, hM₂m, -, hM₂R⟩ := exists_corr_conj3 hΩ ⟨hNm, hRf, hNR⟩ g'' hR''f
  obtain ⟨w, hw⟩ := hΩ.classical M₁ hM₁m.1
  obtain ⟨v, hv⟩ := hΩ.classical M₂ hM₂m.1
  have hw' : w ∈ locLayer Ω x := le_centralizingLayer hM₁m hw.mem
  have hv' : v ∈ locLayer Ω x := le_centralizingLayer hM₂m hv.mem
  have hπw : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w, hw'⟩ =
      D.hom i r' := himg hM₁m hw (conjSub g' R) r' hM₁R hR'f hr'R' hr'2 hr'1 hw'
  have hπv : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨v, hv'⟩ =
      D.hom i (r * r') := himg hM₂m hv (conjSub g'' R) (r * r') hM₂R hR''f hrr'R'' hrr'2 hrr'1 hv'
  have hwu : w * u = u * w := by
    have h1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x))
        (⟨w, hw'⟩ * ⟨u, hu'⟩) = QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x))
        (⟨u, hu'⟩ * ⟨w, hw'⟩) := by
      rw [map_mul, map_mul, hπw, ← hr, ← map_mul, ← map_mul, hr'comm]
    exact congrArg Subtype.val (hπinj _ _ h1)
  have hwne : w ≠ u := by
    intro h
    have h1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w, hw'⟩ =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨u, hu'⟩ :=
      congrArg _ (Subtype.ext h)
    rw [hπw, ← hr] at h1
    exact hr'ne (hψinj h1)
  have hvuw : v = u * w := by
    have huw' : u * w ∈ locLayer Ω x := Subgroup.mul_mem _ hu' hw'
    have h1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨v, hv'⟩ =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨u * w, huw'⟩ := by
      rw [hπv]
      show D.hom i (r * r') = QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x))
        (⟨u, hu'⟩ * ⟨w, hw'⟩)
      rw [map_mul (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x))), hπw, ← hr,
        ← map_mul]
    exact congrArg Subtype.val (hπinj _ _ h1)
  refine ⟨M₁, M₂, w, ⟨hM₁m, ?_⟩, ⟨hM₂m, ?_⟩, hw, hvuw ▸ hv, hwu, hwne⟩
  · rw [hM₁R]
    exact Subgroup.map_le_range _ _
  · rw [hM₂R]
    exact Subgroup.map_le_range _ _

end Members

section Edge

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {K₁ K₂ : Subgroup G} {z₁ z₂ : G} {ι : Type}

namespace EdgeData

theorem kleinAt_of_kleinData (hR : RouteD3Setup K z) (h : EdgeData K K₁ K₂ z₁ z₂)
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁)) {i : ι}
    (hi : locImg (conjClass3 K) z₁ K₂ ≤ (D.hom i).range) (hKd : KleinData (D.kind i)) :
    KleinAt K K₁ z₂ := by
  have hΩ := hR.inClass
  have hex := hR.setup.1
  have hR₁ : RouteD3Setup K₁ z₁ := Q3TC.RouteD3Setup.of_mem_conjClass3 hR h.mem₁ h.cls₁
  have hcl : conjClass3 K₁ = conjClass3 K := Q3TC.conjClass3_eq_of_mem h.mem₁
  have hP1 : LocalOddCentral (conjClass3 K) {z₁} := hcl ▸ hR₁.setup.2
  have hO3 : LocalOddThreeFree3 (conjClass3 K) z₁ :=
    hcl ▸ Q3W.oddThreeFreeInput_proved G K₁ z₁ hR₁
  have hK₁ : K₁ ∈ centralizingMembers (conjClass3 K) {z₁} :=
    ⟨h.mem₁, isSubnormal_le h.cls₁.subnormal⟩
  have hK₂ : K₂ ∈ centralizingMembers (conjClass3 K) {z₁} := ⟨h.mem₂, h.le_centralizer₁⟩
  have hOY : classicalInvolutionOddCore ↥(locLayer (conjClass3 K) z₁) = ⊥ := by
    have h1 := oddCoreIn_centralizingLayer_le hΩ.conjInvariant z₁
    rw [Q3OF.involutionOddCore_eq_bot_of_member hR h.mem₁ h.cls₁, le_bot_iff] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (centralizingLayer (conjClass3 K) {z₁}).subtype_injective).mp h1
  obtain ⟨i₁, hi₁⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨K₁, hK₁, rfl⟩)
  have hu₁' : z₁ ∈ locLayer (conjClass3 K) z₁ := le_centralizingLayer hK₁ h.cls₁.mem
  have hA1 : D.kind i₁ = CompData.sl23 :=
    kind_eq_sl23_of_ubar_central D hK₁ h.cls₁ hu₁' (ubar_mem_center_at_self hu₁') i₁ hi₁
  have hne : i₁ ≠ i := by
    intro heq
    subst heq
    have hKK : K₁ = K₂ := eq_of_mem_compMembers_a13 hΩ hex hP1 hO3 hA1 ⟨hK₁, hi₁⟩ ⟨hK₂, hi⟩
    have hcl₂ : IsClassicalMember3 K₁ z₂ := hKK ▸ h.cls₂
    exact h.ne (involution_unique3 h.cls₁ hcl₂)
  obtain ⟨M₁, M₂, w, hM₁, hM₂, c₁, c₂, hcomm, hwne⟩ :=
    exists_klein_members hΩ hex hP1 hO3 hOY D hKd ⟨hK₂, hi⟩ h.cls₂
  have hcK₁ : ∀ {M : Subgroup G} {m : G}, M ∈ compMembers3 (conjClass3 K) z₁ D i →
      IsClassicalMember3 M m → K₁ ≤ Subgroup.centralizer ({m} : Set G) := by
    intro M m hM hm y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commutes_of_ne_comp3 hΩ hex hP1 hO3 D hne ⟨hK₁, hi₁⟩ hM y hy m hm.mem
  exact ⟨M₁, M₂, w, hM₁.1.1, hM₂.1.1, c₁, c₂, hcK₁ hM₁ c₁, hcomm, hwne⟩

end EdgeData

end Edge

end CFSG.ClassicalInvolution.Q3.Q3PP
