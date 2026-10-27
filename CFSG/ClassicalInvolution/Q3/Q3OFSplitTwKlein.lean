module

public import CFSG.ClassicalInvolution.Q3.Q3PPKleinAt
public import CFSG.ClassicalInvolution.Q3.Q3NTChain
public import CFSG.ClassicalInvolution.Q3.Q3OFShCrit
public import CFSG.ClassicalInvolution.Q3.Q3EXTwin
public import CFSG.ClassicalInvolution.Q3.Q3DBSetup
public import CFSG.ClassicalInvolution.Q3.Q3OFModelU

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OF

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3PP
open scoped MatrixGroups

section Model


structure ChainKleinData (c : CompData) : Prop where
  fund : KindFund3 c
  conj : FundConjClosed3 c
  single : ∀ R ∈ c.fund, ∀ R' ∈ c.fund, ∃ g : c.G, R' = conjSub g R
  chain : Asc77.ChainPair c.fund

theorem chainKleinData_model {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ}
    (ht : t = .PSL ∨ t = .PSU) (hn : 3 ≤ n) : ChainKleinData (CompData.model t n) := by
  have hadm := Q3NT.statedLieAdmissible_three ht hn
  have hft : IsFundTag t := by rcases ht with rfl | rfl <;> simp [IsFundTag]
  have hG2 : t ≠ .G2 := by rcases ht with rfl | rfl <;> decide
  have hD4 : t ≠ .trialityD4 := by rcases ht with rfl | rfl <;> decide
  exact ⟨kindFund3_model hft hadm hG2 hD4, fundConjClosed3_model t n,
    Q3W.EX.singleClass_of_kind rfl hft hadm hG2 hD4, Q3NT.chainPair_model_three t n ht hn⟩

end Model

section Fund

variable {c : CompData} {X : Type} [Group X]

theorem sl23_eq_of_sq_eq_one :
    ∀ s s' : SL(2, ZMod 3), s * s = 1 → s' * s' = 1 → s ≠ 1 → s' ≠ 1 → s = s' := by
  decide +kernel

theorem fund_facts (hF : KindFund3 c) (ψ : c.G →* X) (hker : ψ.ker ≤ Subgroup.center c.G)
    {R : Subgroup c.G} (hR : R ∈ c.fund) (h24 : Nat.card (R.map ψ) = 24) :
    (∀ a ∈ R, ∀ b ∈ R, a * a = 1 → b * b = 1 → a ≠ 1 → b ≠ 1 → a = b) ∧
      ∀ a ∈ R, ∀ b ∈ R, ψ a = ψ b → a = b := by
  obtain ⟨e⟩ := hF ψ hker R hR h24
  have hRc : Nat.card R = 24 := by rw [Nat.card_congr e.toEquiv, natCard_sl2Three]
  have : Finite ↥R := Nat.finite_of_card_ne_zero (by rw [hRc]; norm_num)
  have : Finite ↥(R.map ψ) := Nat.finite_of_card_ne_zero (by rw [h24]; norm_num)
  refine ⟨fun a ha b hb hab hbb ha1 hb1 => ?_,
    injOn_of_card_map_eq (φ := ψ) (R := R) (by rw [hRc, h24])⟩
  have h1 : e ⟨a, ha⟩ = e ⟨b, hb⟩ := sl23_eq_of_sq_eq_one _ _
    (by rw [← map_mul]; exact (map_eq_one_iff e e.injective).mpr (Subtype.ext hab))
    (by rw [← map_mul]; exact (map_eq_one_iff e e.injective).mpr (Subtype.ext hbb))
    (fun h => ha1 (congrArg Subtype.val (e.injective (h.trans (map_one e).symm))))
    (fun h => hb1 (congrArg Subtype.val (e.injective (h.trans (map_one e).symm))))
  exact congrArg Subtype.val (e.injective h1)

end Fund

section Members


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G} {ι : Type}

theorem mk_involution_eq_of_corr {D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)} {i : ι}
    (hF : KindFund3 (D.kind i)) {M : Subgroup G} {w : G} (hM : M ∈ centralizingMembers Ω {x})
    (hw : IsClassicalMember3 M w) {R' : Subgroup (D.kind i).G} {r' : (D.kind i).G}
    (hMR : locImg Ω x M = R'.map (D.hom i)) (hR'f : R' ∈ (D.kind i).fund) (hr'R : r' ∈ R')
    (hr'2 : r' * r' = 1) (hr'1 : r' ≠ 1) (hw' : w ∈ locLayer Ω x) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w, hw'⟩ = D.hom i r' := by
  have h24 : Nat.card (R'.map (D.hom i)) = 24 := by
    rw [← hMR]
    exact D.card_eq _ (mem_locFamily_iff.mpr ⟨M, hM, rfl⟩)
  obtain ⟨huniq, hinj⟩ := fund_facts hF (D.hom i) (D.ker_le_center i) hR'f h24
  have hcl : IsClassicalMember3 (locImg Ω x M)
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w, hw'⟩) :=
    (hw.subgroupOf (le_centralizingLayer hM)).map_oddQuotient
  have hmem : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w, hw'⟩ ∈
      R'.map (D.hom i) := by
    rw [← hMR]
    exact hcl.mem
  obtain ⟨s, hsR, hs⟩ := hmem
  have hw2 : (⟨w, hw'⟩ : ↥(locLayer Ω x)) * ⟨w, hw'⟩ = 1 :=
    Subtype.ext (Q3NT.mul_self_eq_one_of_orderOf_eq_two hw.orderOf_eq_two)
  have hs2 : s * s = 1 := hinj _ (R'.mul_mem hsR hsR) _ R'.one_mem (by
    rw [map_mul, hs, ← map_mul, hw2, map_one, map_one])
  have hs1 : s ≠ 1 := by
    intro h1
    apply hcl.ne_one
    rw [← hs, h1, map_one]
  rw [← hs, huniq s hsR r' hr'R hs2 hr'2 hs1 hr'1]

theorem exists_klein_members_chain (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (hOY : classicalInvolutionOddCore ↥(locLayer Ω x) = ⊥)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {i : ι}
    (hKd : ChainKleinData (D.kind i)) {N : Subgroup G} {u : G}
    (hN : N ∈ compMembers3 Ω x D i) (hu : IsClassicalMember3 N u) :
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
  obtain ⟨R, hNm, hRf, hNR⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hN
  have hNY : N ≤ locLayer Ω x := le_centralizingLayer hNm
  have hu' : u ∈ locLayer Ω x := hNY hu.mem
  have hclN : IsClassicalMember3 (locImg Ω x N)
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨u, hu'⟩) :=
    (hu.subgroupOf hNY).map_oddQuotient
  have h24 : Nat.card (R.map (D.hom i)) = 24 := by
    rw [← hNR]
    exact D.card_eq _ (mem_locFamily_iff.mpr ⟨N, hNm, rfl⟩)
  obtain ⟨huniqR, hinjR⟩ := fund_facts hKd.fund (D.hom i) (D.ker_le_center i) hRf h24
  have hmemN : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨u, hu'⟩ ∈
      R.map (D.hom i) := by
    rw [← hNR]
    exact hclN.mem
  obtain ⟨r, hrR, hr⟩ := hmemN
  have hu2 : (⟨u, hu'⟩ : ↥(locLayer Ω x)) * ⟨u, hu'⟩ = 1 :=
    Subtype.ext (Q3NT.mul_self_eq_one_of_orderOf_eq_two hu.orderOf_eq_two)
  have hr2 : r * r = 1 := hinjR _ (R.mul_mem hrR hrR) _ R.one_mem (by
    rw [map_mul, hr, ← map_mul, hu2, map_one, map_one])
  have hr1 : r ≠ 1 := by
    intro h1
    apply hclN.ne_one
    rw [← hr, h1, map_one]
  obtain ⟨R₁, hR₁, R₂, hR₂, τ₁, τ₂, ν₁, ν₂, hd⟩ := hKd.chain
  obtain ⟨g, hg⟩ := hKd.single R₁ hR₁ R hRf
  have hτ₁1 : τ₁ ≠ 1 := by
    intro h1
    obtain ⟨s, -, hs⟩ := hd.not_central
    exact hs (by rw [h1]; simp)
  have hτ₁R : g * τ₁ * g⁻¹ ∈ R := hg ▸ conj_mem_conjSub hd.mem₁
  have hτ₁2 : (g * τ₁ * g⁻¹) * (g * τ₁ * g⁻¹) = 1 := by
    calc (g * τ₁ * g⁻¹) * (g * τ₁ * g⁻¹) = g * (τ₁ * τ₁) * g⁻¹ := by group
      _ = 1 := by rw [hd.sq₁]; group
  have hτ₁ne : g * τ₁ * g⁻¹ ≠ 1 := by
    intro h1
    apply hτ₁1
    have : τ₁ = g⁻¹ * (g * τ₁ * g⁻¹) * g := by group
    rw [this, h1]
    group
  have hrdef : r = g * τ₁ * g⁻¹ := huniqR r hrR _ hτ₁R hr2 hτ₁2 hr1 hτ₁ne
  obtain ⟨r', hr'e⟩ : ∃ r' : (D.kind i).G, r' = g * τ₂ * g⁻¹ := ⟨_, rfl⟩
  obtain ⟨g', hg'e⟩ : ∃ g' : (D.kind i).G, g' = g * ν₁ * g⁻¹ := ⟨_, rfl⟩
  obtain ⟨g'', hg''e⟩ : ∃ g'' : (D.kind i).G, g'' = g * ν₂ * g⁻¹ := ⟨_, rfl⟩
  have hr'def : r' = g' * r * g'⁻¹ := by
    rw [hr'e, hg'e, hrdef, ← hd.swap₁]
    group
  have hrr'def : r * r' = g'' * r * g''⁻¹ := by
    have e : g * τ₁ * g⁻¹ * (g * τ₂ * g⁻¹) = g * (τ₁ * τ₂) * g⁻¹ := by group
    rw [hr'e, hg''e, hrdef, e, ← hd.swap₂]
    group
  have hr'comm : r' * r = r * r' := by
    rw [hr'e, hrdef]
    calc g * τ₂ * g⁻¹ * (g * τ₁ * g⁻¹) = g * (τ₂ * τ₁) * g⁻¹ := by group
      _ = g * (τ₁ * τ₂) * g⁻¹ := by rw [hd.comm]
      _ = g * τ₁ * g⁻¹ * (g * τ₂ * g⁻¹) := by group
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
  have hR'f : conjSub g' R ∈ (D.kind i).fund := hKd.conj R hRf g'
  have hR''f : conjSub g'' R ∈ (D.kind i).fund := hKd.conj R hRf g''
  have hr'R' : r' ∈ conjSub g' R := by
    rw [hr'def]
    exact conj_mem_conjSub hrR
  have hrr'R'' : r * r' ∈ conjSub g'' R := by
    rw [hrr'def]
    exact conj_mem_conjSub hrR
  obtain ⟨M₁, hM₁m, -, hM₁R⟩ := exists_corr_conj3 hΩ ⟨hNm, hRf, hNR⟩ g' hR'f
  obtain ⟨M₂, hM₂m, -, hM₂R⟩ := exists_corr_conj3 hΩ ⟨hNm, hRf, hNR⟩ g'' hR''f
  obtain ⟨w, hw⟩ := hΩ.classical M₁ hM₁m.1
  obtain ⟨v, hv⟩ := hΩ.classical M₂ hM₂m.1
  have hw' : w ∈ locLayer Ω x := le_centralizingLayer hM₁m hw.mem
  have hv' : v ∈ locLayer Ω x := le_centralizingLayer hM₂m hv.mem
  have hπw := mk_involution_eq_of_corr hKd.fund hM₁m hw hM₁R hR'f hr'R' hr'2 hr'1 hw'
  have hπv := mk_involution_eq_of_corr hKd.fund hM₂m hv hM₂R hR''f hrr'R'' hrr'2 hrr'1 hv'
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
    have hcen : r'⁻¹ * r ∈ Subgroup.center (D.kind i).G := D.ker_le_center i (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel])
    rw [inv_eq_of_mul_eq_one_right hr'2, hr'e, hrdef] at hcen
    have hc2 := Subgroup.Normal.conj_mem inferInstance _ hcen g⁻¹
    have e : g⁻¹ * (g * τ₂ * g⁻¹ * (g * τ₁ * g⁻¹)) * g⁻¹⁻¹ = τ₂ * τ₁ := by group
    rw [e] at hc2
    exact hd.prod_not_central (by rw [hd.comm]; exact hc2)
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

theorem kleinAt_of_chainKleinData (hR : RouteD3Setup K z) (h : EdgeData K K₁ K₂ z₁ z₂)
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁)) {i : ι}
    (hi : locImg (conjClass3 K) z₁ K₂ ≤ (D.hom i).range) (hKd : ChainKleinData (D.kind i)) :
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
  have hOY : classicalInvolutionOddCore ↥(locLayer (conjClass3 K) z₁) = ⊥ :=
    Q3DB.classicalInvolutionOddCore_locLayer_eq_bot hΩ.conjInvariant
      (involutionOddCore_eq_bot_of_member hR h.mem₁ h.cls₁)
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
    exists_klein_members_chain hΩ hex hP1 hO3 hOY D hKd ⟨hK₂, hi⟩ h.cls₂
  have hcK₁ : ∀ {M : Subgroup G} {m : G}, M ∈ compMembers3 (conjClass3 K) z₁ D i →
      IsClassicalMember3 M m → K₁ ≤ Subgroup.centralizer ({m} : Set G) := by
    intro M m hM hm y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commutes_of_ne_comp3 hΩ hex hP1 hO3 D hne ⟨hK₁, hi₁⟩ hM y hy m hm.mem
  exact ⟨M₁, M₂, w, hM₁.1.1, hM₂.1.1, c₁, c₂, hcK₁ hM₁ c₁, hcomm, hwne⟩

end Edge

end CFSG.ClassicalInvolution.Q3.Q3OF
