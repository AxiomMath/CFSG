module

public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedFamily
import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedTransport
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.Quasithin.EmptyFaithful.Gold14610LiftSL2
import CFSG.GroupTheory.InnerCentralizerProjection
import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedSemisimpleTools
import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedComponentTools
import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigFunctor
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.ComponentClassification.FooteMarked

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_orderOf_eq_two_of_isElementaryAbelian {E : Subgroup G}
    (hE : IsElementaryAbelian 2 ↥E) (hE2 : 2 ≤ Nat.card E) : ∃ a ∈ E, orderOf a = 2 := by
  haveI := hE
  have hnt : Nontrivial ↥E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨a, haE⟩, ha1⟩ := exists_ne (1 : ↥E)
  refine ⟨a, haE, ?_⟩
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have h2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a haE
  have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd h (by rw [orderOf_eq_one_iff]; exact ha1')
  · exact h

theorem sup_oddCoreIn_ambientCanonicalLift {H K : Subgroup G}
    {A : Subgroup (↥H ⧸ pPrimeCore 2 ↥H)} (hA : IsComponent A) (hKH : K ≤ H)
    (hKA : (K.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) = A)
    (hKJ : K ≤ ambientCanonicalLift H A) :
    K ⊔ FooteLit.oddCoreIn (ambientCanonicalLift H A) = ambientCanonicalLift H A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (sup_le hKJ ?_) ?_
  · show (pPrimeCore 2 ↥(ambientCanonicalLift H A)).map
      (ambientCanonicalLift H A).subtype ≤ ambientCanonicalLift H A
    exact Subgroup.map_subtype_le _
  intro j hjJ
  have hJH : ambientCanonicalLift H A ≤ H := ambientCanonicalLift_le H A
  have hjA : (QuotientGroup.mk' (pPrimeCore 2 ↥H)) ⟨j, hJH hjJ⟩ ∈ A := by
    rw [← ambientCanonicalLift_map_quotient hA]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hjJ)
  rw [← hKA] at hjA
  obtain ⟨kH, hkK, hkπ⟩ := Subgroup.mem_map.mp hjA
  have hkK' : (kH : G) ∈ K := Subgroup.mem_subgroupOf.mp hkK
  have hkH : (kH : G) ∈ H := hKH hkK'
  have hxH : (kH : G)⁻¹ * j ∈ H := H.mul_mem (H.inv_mem hkH) (hJH hjJ)
  have hxJ : (kH : G)⁻¹ * j ∈ ambientCanonicalLift H A :=
    (ambientCanonicalLift H A).mul_mem ((ambientCanonicalLift H A).inv_mem (hKJ hkK')) hjJ
  have hxker : (⟨(kH : G)⁻¹ * j, hxH⟩ : ↥H) ∈ pPrimeCore 2 ↥H := by
    refine (QuotientGroup.eq_one_iff _).mp ?_
    have hsplit : (⟨(kH : G)⁻¹ * j, hxH⟩ : ↥H) = kH⁻¹ * ⟨j, hJH hjJ⟩ := Subtype.ext rfl
    have hπ : (QuotientGroup.mk' (pPrimeCore 2 ↥H)) (kH⁻¹ * ⟨j, hJH hjJ⟩) = 1 := by
      rw [map_mul, map_inv, hkπ, inv_mul_cancel]
    rwa [hsplit]
  have hxO : (kH : G)⁻¹ * j ∈ FooteLit.oddCoreIn H :=
    Subgroup.mem_map_of_mem H.subtype hxker
  have hconjH : ∀ (g : ↥H) (y : G), y ∈ FooteLit.oddCoreIn H →
      (g : G) * y * (g : G)⁻¹ ∈ FooteLit.oddCoreIn H := by
    haveI : (pPrimeCore 2 ↥H).Normal := CFSG.pPrimeCore_normal
    intro g y hy
    obtain ⟨yH, hyH, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_map_of_mem H.subtype (Subgroup.Normal.conj_mem inferInstance yH hyH g)
  have hHnorm : H ≤ Subgroup.normalizer (FooteLit.oddCoreIn H : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hconjH ⟨h, hh⟩ y hy
    · intro hy
      have h1 := hconjH ⟨h, hh⟩⁻¹ (h * y * h⁻¹) hy
      have h2 : (↑(⟨h, hh⟩⁻¹ : ↥H) : G) * (h * y * h⁻¹) *
          (↑(⟨h, hh⟩⁻¹ : ↥H) : G)⁻¹ = y := by
        simp only [Subgroup.coe_inv, Subgroup.coe_mk, inv_inv]
        group
      rwa [h2] at h1
  have hNJodd : Odd (Nat.card ↥(ambientCanonicalLift H A ⊓ FooteLit.oddCoreIn H)) :=
    (FooteLit.odd_card_oddCoreIn H).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hxOJ : (kH : G)⁻¹ * j ∈ FooteLit.oddCoreIn (ambientCanonicalLift H A) :=
    FooteLit.le_oddCoreIn (Y := ambientCanonicalLift H A)
      (N := ambientCanonicalLift H A ⊓ FooteLit.oddCoreIn H) inf_le_left
      (by
        intro x hx
        exact Subgroup.inf_normalizer_le_normalizer_inf
          ⟨le_normalizer (H := ambientCanonicalLift H A) hx, hHnorm (hJH hx)⟩)
      hNJodd ⟨hxJ, hxO⟩
  have hsplit : j = (kH : G) * ((kH : G)⁻¹ * j) := by group
  rw [hsplit]
  exact Subgroup.mul_mem_sup hkK' hxOJ

theorem three_le_pRank_centralizer_map_fixedShadowAt {H K E : Subgroup G} (hKH : K ≤ H)
    (hEH : E ≤ H) (hEK : E ≤ UnbalancedLayer.coreActionKernel K)
    (hE : IsElementaryAbelian 2 ↥E) (hE8 : 8 ≤ Nat.card E) {a : ↥H} (haE : (a : G) ∈ E)
    (hA : CFSG.IsQuasisimple ↥(((fixedShadowAt K a).subgroupOf H).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥H)))) :
    3 ≤ CFSG.pRank 2 ↥(centralizer ((((fixedShadowAt K a).subgroupOf H).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥H)) : Subgroup (↥H ⧸ pPrimeCore 2 ↥H)) :
        Set (↥H ⧸ pPrimeCore 2 ↥H))) := by
  classical
  haveI hEinst : IsElementaryAbelian 2 ↥E := hE
  let π : ↥H →* (↥H ⧸ pPrimeCore 2 ↥H) := QuotientGroup.mk' (pPrimeCore 2 ↥H)
  let Ka : Subgroup G := fixedShadowAt K (a : G)
  let W : Subgroup ↥H := Ka.subgroupOf H
  let A : Subgroup (↥H ⧸ pPrimeCore 2 ↥H) := W.map π
  have hAq : CFSG.IsQuasisimple ↥A := hA
  have hKaK : Ka ≤ K := fixedShadowAt_le K (a : G)
  have hKaH : Ka ≤ H := hKaK.trans hKH
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥E) (⟨y, hy⟩ : ↥E))
  have hEnorm : ∀ e ∈ E, e ∈ Subgroup.normalizer (Ka : Set G) := by
    intro e he
    refine mem_normalizer_fixedShadowAt (M := K) (a := (a : G)) (b := e)
      (UnbalancedLayer.mem_coreActionKernel.mp (hEK he)).1 (hcommE (a : G) haE e he)
  have hpi_norm : ∀ e : ↥E, π ⟨(e : G), hEH e.2⟩ ∈ Subgroup.normalizer (A : Set _) := by
    intro e
    have heW : (⟨(e : G), hEH e.2⟩ : ↥H) ∈ Subgroup.normalizer (W : Set ↥H) := by
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · intro hw
        rw [Subgroup.mem_subgroupOf]
        have h := (Subgroup.mem_normalizer_iff.mp (hEnorm e e.2) (w : G)).mp hw
        simpa using h
      · intro hw
        rw [Subgroup.mem_subgroupOf] at hw
        have h := (Subgroup.mem_normalizer_iff.mp (hEnorm e e.2) (w : G)).mpr hw
        exact Subgroup.mem_subgroupOf.mpr h
    exact Subgroup.le_normalizer_map (H := W) π (Subgroup.mem_map_of_mem π heW)
  let Y : Subgroup G := Ka ⊓ FooteLit.oddCoreIn K
  have hYH : Y ≤ H := inf_le_left.trans hKaH
  let YH : Subgroup ↥H := Y.subgroupOf H
  let N : Subgroup (↥H ⧸ pPrimeCore 2 ↥H) := YH.map π
  have hYW : YH ≤ W := fun y hy => hy.1
  have hNA : N ≤ A := Subgroup.map_mono hYW
  have hYconj : ∀ (w y : ↥H), w ∈ W → y ∈ YH → w * y * w⁻¹ ∈ YH := by
    intro w y hwW hyY
    have hwK : (w : G) ∈ K := hKaK hwW
    rw [Subgroup.mem_subgroupOf]
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer hwW) y).mp hyY.1
    · exact (Subgroup.mem_normalizer_iff.mp
        (FooteLit.mem_normalizer_oddCoreIn (le_normalizer hwK)) (y : G)).mp hyY.2
  have hN_normal : (N.subgroupOf A).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨w, hwW, hπw⟩ := Subgroup.mem_map.mp g.2
    obtain ⟨y, hyY, hπy⟩ := Subgroup.mem_map.mp hn
    have hmem : w * y * w⁻¹ ∈ YH := hYconj w y hwW hyY
    have heq : (↑(g * n * g⁻¹) : ↥H ⧸ pPrimeCore 2 ↥H) = π (w * y * w⁻¹) := by
      have h1 : (↑(g * n * g⁻¹) : ↥H ⧸ pPrimeCore 2 ↥H) = ↑g * ↑n * (↑g)⁻¹ := rfl
      rw [h1, ← hπw, ← hπy, ← map_mul, ← map_inv, ← map_mul]
    rw [heq]
    exact Subgroup.mem_map_of_mem π hmem
  have hOKK : FooteLit.oddCoreIn K ≤ K := Subgroup.map_subtype_le _
  have hOKH : FooteLit.oddCoreIn K ≤ H := hOKK.trans hKH
  have hNodd : Odd (Nat.card ↥(N.subgroupOf A)) := by
    have h1 : Nat.card ↥(N.subgroupOf A) = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNA).toEquiv
    rw [h1]
    have h2 : Nat.card ↥N ∣ Nat.card ↥YH := Subgroup.card_map_dvd YH π
    have h3 : Nat.card ↥YH ∣ Nat.card (FooteLit.oddCoreIn K) := by
      have hle : YH ≤ (FooteLit.oddCoreIn K).subgroupOf H := fun y hy => hy.2
      have hdvd := Subgroup.card_dvd_of_le hle
      have heq : Nat.card ↥((FooteLit.oddCoreIn K).subgroupOf H) =
          Nat.card (FooteLit.oddCoreIn K) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOKH).toEquiv
      rwa [heq] at hdvd
    exact (FooteLit.odd_card_oddCoreIn K).of_dvd_nat (h2.trans h3)
  have hNcenter : (N.subgroupOf A) ≤ Subgroup.center ↥A :=
    CFSG.Quasithin.Gold14610.normal_le_center_of_odd hAq hN_normal hNodd
  have hcenterA : ∀ (y : ↥H) (hy : y ∈ YH),
      (⟨π y, hNA (Subgroup.mem_map_of_mem π hy)⟩ : ↥A) ∈ Subgroup.center ↥A := by
    intro y hy
    have hyN : π y ∈ N := Subgroup.mem_map_of_mem π hy
    exact hNcenter (Subgroup.mem_subgroupOf.mpr hyN)
  have hcommut : ∀ (e : ↥E) (j : ↥A),
      π ⟨(e : G), hEH e.2⟩ * (j : _) * (π ⟨(e : G), hEH e.2⟩)⁻¹ * (j : _)⁻¹ ∈
        (Subgroup.center ↥A).map A.subtype := by
    intro e j
    obtain ⟨x, hxW, hπx⟩ := Subgroup.mem_map.mp j.2
    have hxK : (x : G) ∈ K := hKaK hxW
    have heH : (e : G) ∈ H := hEH e.2
    have hOKnorm : K ≤ Subgroup.normalizer (FooteLit.oddCoreIn K : Set G) :=
      fun k hk => FooteLit.mem_normalizer_oddCoreIn (le_normalizer hk)
    have hz : (x : G)⁻¹ * (e : G)⁻¹ * (x : G) * (e : G) ∈ FooteLit.oddCoreIn K :=
      (UnbalancedLayer.mem_coreActionKernel.mp (hEK e.2)).2 (x : G) hxK
    have h1 : (x : G) * ((x : G)⁻¹ * (e : G)⁻¹ * (x : G) * (e : G)) * (x : G)⁻¹ ∈
        FooteLit.oddCoreIn K :=
      (Subgroup.mem_normalizer_iff.mp (hOKnorm hxK) _).mp hz
    have h2 : (e : G) * ((x : G) * ((x : G)⁻¹ * (e : G)⁻¹ * (x : G) * (e : G)) *
        (x : G)⁻¹) * (e : G)⁻¹ ∈ FooteLit.oddCoreIn K :=
      (Subgroup.mem_normalizer_iff.mp
        (FooteLit.mem_normalizer_oddCoreIn
          (UnbalancedLayer.mem_coreActionKernel.mp (hEK e.2)).1) _).mp h1
    have h3 : (e : G) * ((x : G) * ((x : G)⁻¹ * (e : G)⁻¹ * (x : G) * (e : G)) *
        (x : G)⁻¹) * (e : G)⁻¹ = (x : G) * (e : G) * (x : G)⁻¹ * (e : G)⁻¹ := by group
    rw [h3] at h2
    have h4 : (e : G) * (x : G) * (e : G)⁻¹ * (x : G)⁻¹ ∈ FooteLit.oddCoreIn K := by
      have h5 : (e : G) * (x : G) * (e : G)⁻¹ * (x : G)⁻¹ =
          ((x : G) * (e : G) * (x : G)⁻¹ * (e : G)⁻¹)⁻¹ := by group
      rw [h5]
      exact (FooteLit.oddCoreIn K).inv_mem h2
    have hyKa : (e : G) * (x : G) * (e : G)⁻¹ * (x : G)⁻¹ ∈ Ka :=
      Ka.mul_mem ((Subgroup.mem_normalizer_iff.mp (hEnorm (e : G) e.2) (x : G)).mp hxW)
        (Ka.inv_mem hxW)
    have hyYH : (⟨(e : G), heH⟩ : ↥H) * x * ⟨(e : G), heH⟩⁻¹ * x⁻¹ ∈ YH := by
      rw [Subgroup.mem_subgroupOf]
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] using
        (show (e : G) * (x : G) * (e : G)⁻¹ * (x : G)⁻¹ ∈ Y from ⟨hyKa, h4⟩)
    have hπx' : π x = (j : ↥H ⧸ pPrimeCore 2 ↥H) := hπx
    have heq : π ⟨(e : G), heH⟩ * (j : _) * (π ⟨(e : G), heH⟩)⁻¹ * (j : _)⁻¹ =
        π ((⟨(e : G), heH⟩ : ↥H) * x * ⟨(e : G), heH⟩⁻¹ * x⁻¹) := by
      have h1 : π ((⟨(e : G), heH⟩ : ↥H) * x * ⟨(e : G), heH⟩⁻¹ * x⁻¹)
          = π ⟨(e : G), heH⟩ * π x * (π ⟨(e : G), heH⟩)⁻¹ * (π x)⁻¹ := by
        simp only [map_mul, map_inv]
      rw [h1, hπx']
      rfl
    rw [heq]
    exact Subgroup.mem_map_of_mem A.subtype (hcenterA _ hyYH)
  have hcent : ∀ e : ↥E,
      π ⟨(e : G), hEH e.2⟩ ∈ Subgroup.centralizer (A : Set _) := by
    intro e
    exact CFSG.mem_centralizer_of_commutator_mem_center hAq.1 (hpi_norm e)
      (fun j hj => hcommut e ⟨j, hj⟩)
  let Ca : Subgroup (↥H ⧸ pPrimeCore 2 ↥H) := Subgroup.centralizer (A : Set _)
  let f : ↥E →* ↥Ca :=
    { toFun := fun e => ⟨π ⟨(e : G), hEH e.2⟩, hcent e⟩
      map_one' := by
        apply Subtype.ext
        have h1 : (⟨((1 : ↥E) : G), hEH (1 : ↥E).2⟩ : ↥H) = 1 := Subtype.ext rfl
        show π (⟨((1 : ↥E) : G), hEH (1 : ↥E).2⟩ : ↥H) = 1
        rw [h1, map_one]
      map_mul' := by
        intro e1 e2
        apply Subtype.ext
        have h1 : (⟨((e1 * e2 : ↥E) : G), hEH (e1 * e2).2⟩ : ↥H) =
            ⟨(e1 : G), hEH e1.2⟩ * ⟨(e2 : G), hEH e2.2⟩ := Subtype.ext rfl
        show π (⟨((e1 * e2 : ↥E) : G), hEH (e1 * e2).2⟩ : ↥H) =
          π ⟨(e1 : G), hEH e1.2⟩ * π ⟨(e2 : G), hEH e2.2⟩
        rw [h1, map_mul] }
  have hEdisc : E ⊓ FooteLit.oddCoreIn H = ⊥ := by
    have h2E : IsPGroup 2 E := IsElementaryAbelian.isPGroup 2 ↥E
    obtain ⟨k, hk⟩ := h2E.exists_card_eq
    have hcop : Nat.Coprime (Nat.card E) (Nat.card (FooteLit.oddCoreIn H)) := by
      rw [hk]
      exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (FooteLit.odd_card_oddCoreIn H))
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hf_inj : Function.Injective f := by
    intro e1 e2 heq
    have hπeq : π ⟨(e1 : G), hEH e1.2⟩ = π ⟨(e2 : G), hEH e2.2⟩ := congrArg Subtype.val heq
    have h1 : (⟨(e1 : G), hEH e1.2⟩ : ↥H) * ⟨(e2 : G), hEH e2.2⟩⁻¹ ∈ pPrimeCore 2 ↥H := by
      refine (QuotientGroup.eq_one_iff _).mp ?_
      change π ((⟨(e1 : G), hEH e1.2⟩ : ↥H) * ⟨(e2 : G), hEH e2.2⟩⁻¹) = 1
      rw [map_mul, map_inv, hπeq, mul_inv_cancel]
    have h2 : (e1 : G) * (e2 : G)⁻¹ ∈ FooteLit.oddCoreIn H := Subgroup.mem_map_of_mem H.subtype h1
    have h3 : (e1 : G) * (e2 : G)⁻¹ ∈ E := E.mul_mem e1.2 (E.inv_mem e2.2)
    have h4 : (e1 : G) * (e2 : G)⁻¹ = 1 := by
      have hmem : (e1 : G) * (e2 : G)⁻¹ ∈ E ⊓ FooteLit.oddCoreIn H := ⟨h3, h2⟩
      rwa [hEdisc, Subgroup.mem_bot] at hmem
    exact Subtype.ext (mul_inv_eq_one.mp h4)
  obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 2 ↥E).exists_card_eq
  have hk3 : 3 ≤ k := by
    refine (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp ?_
    rw [← hk]
    simpa using hE8
  have hpow : ∀ a : ↥E, a ^ 2 = 1 := fun a =>
    Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) (a : G) a.2)
  have hfin : 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup ↥Ca) :=
    le_trans hk3 (CFSG.SectionRank.le_pRank_of_injective (p := 2) (A := ↥E) (k := k)
      (by norm_num) (fun a b => mul_comm' a b) hpow hk f hf_inj le_top)
  show 3 ≤ CFSG.pRank 2 ↥Ca
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank (p := 2) (H := Ca),
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup (H := Ca)]
  exact hfin

private theorem marked_le_coreActionKernel_of_ne {T : Type} [Group T]
    {S : Set (Subgroup G)} {N J K : Subgroup G}
    (hJ : J ∈ markedComponents S T N) (hK : K ∈ markedComponents S T N) (hne : J ≠ K) :
    J ≤ UnbalancedLayer.coreActionKernel K :=
  CFSG.ComponentClassification.GSThmB.B5a.le_coreActionKernel_of_ne hK.1.1 hJ.1.1 hK.1.2 hJ.1.2
    hne.symm

private theorem baseKernel_le_coreActionKernel_of_marked {T : Type} [Group T]
    {S : Set (Subgroup G)} {N K : Subgroup G} (hK : K ∈ markedComponents S T N) :
    baseKernel S T N ≤ UnbalancedLayer.coreActionKernel K := by
  intro g hg
  have hgN : g ∈ Subgroup.normalizer (K : Set G) :=
    base_le_normalizer_of_isTwoComponentIn hK.1 hg.1
  have hKmD : K ≤ markedLayer S T N := le_sSup hK
  have hOK : K ≤ Subgroup.normalizer (FooteLit.oddCoreIn (markedLayer S T N) : Set G) :=
    fun k hk => FooteLit.mem_normalizer_oddCoreIn (le_normalizer (hKmD hk))
  have hKN : K ≤ Subgroup.normalizer
      ((K ⊓ FooteLit.oddCoreIn (markedLayer S T N) : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
      exact ⟨K.mul_mem (K.mul_mem hx hy1) (K.inv_mem hx),
        (Subgroup.mem_normalizer_iff.mp (hOK hx) y).mp hy2⟩
    · intro hy
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
      have hconj : x⁻¹ * (x * y * x⁻¹) * x = y := by group
      have h1 : x⁻¹ * (x * y * x⁻¹) * x ∈ K :=
        K.mul_mem (K.mul_mem (K.inv_mem hx) hy1) hx
      have h2 : x⁻¹ * (x * y * x⁻¹) * x ∈ FooteLit.oddCoreIn (markedLayer S T N) := by
        simpa only [inv_inv] using
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hOK hx)) (x * y * x⁻¹)).mp hy2
      rw [hconj] at h1 h2
      exact ⟨h1, h2⟩
  have hNK : K ⊓ FooteLit.oddCoreIn (markedLayer S T N) ≤ FooteLit.oddCoreIn K :=
    FooteLit.le_oddCoreIn (Y := K) (N := K ⊓ FooteLit.oddCoreIn (markedLayer S T N)) inf_le_left
      hKN
      ((FooteLit.odd_card_oddCoreIn (markedLayer S T N)).of_dvd_nat
        (Subgroup.card_dvd_of_le inf_le_right))
  refine ⟨hgN, fun j hj => hNK ⟨?_, ?_⟩⟩
  · have h1 : g⁻¹ * j * g ∈ K := by
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) j).mp hj
    have h2 : j⁻¹ * (g⁻¹ * j * g) ∈ K := K.mul_mem (K.inv_mem hj) h1
    simpa [mul_assoc] using h2
  · exact (UnbalancedLayer.mem_coreActionKernel.mp hg.2).2 j (hKmD hj)

private theorem marked_inf_coreActionKernel_le_oddCoreIn {T : Type} [Group T] [IsSimpleGroup T]
    {S : Set (Subgroup G)} (hFam : IsomorphicFamily S T) {N K : Subgroup G}
    (hK : K ∈ markedComponents S T N) :
    K ⊓ UnbalancedLayer.coreActionKernel K ≤ FooteLit.oddCoreIn K := by
  have hQ : CFSG.IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) := hK.2.quotient_quasisimple hFam
  have hZ : Subgroup.center (↥K ⧸ pPrimeCore 2 ↥K) = ⊥ := by
    obtain ⟨e⟩ := hK.2.2.1
    haveI hQs : IsSimpleGroup (↥K ⧸ pPrimeCore 2 ↥K) := e.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (↥K ⧸ pPrimeCore 2 ↥K)) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hQ.2.2
      refine hxy ?_
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (↥K ⧸ pPrimeCore 2 ↥K)) x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (↥K ⧸ pPrimeCore 2 ↥K)) y
      have hc : b * a = a * b := Subgroup.mem_center_iff.mp (h.symm ▸ Subgroup.mem_top a) b
      rw [← map_mul, ← map_mul, hc]
  intro x hx
  exact FooteLit.mem_oddCoreIn_of_mem_coreActionKernel hZ hx.1 hx.2

theorem exists_isElementaryAbelian_le_base {T : Type} [Group T] [IsSimpleGroup T]
    {𝓢 : Set (Subgroup G)} (hFam : IsomorphicFamily 𝓢 T) (hT4 : ∃ V : Subgroup T, IsKleinFour ↥V)
    {N : Subgroup G} (hN : Balanced 𝓢 T N) {K : Subgroup G} (hK : K ∈ markedComponents 𝓢 T N) :
    ∃ E : Subgroup G, E ≤ base N ∧ E ≤ UnbalancedLayer.coreActionKernel K ∧
      IsElementaryAbelian 2 ↥E ∧ 8 ≤ Nat.card E := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfour : ∀ J ∈ markedComponents 𝓢 T N, ∃ V : Subgroup G, V ≤ J ∧ IsKleinFour ↥V := by
    intro J hJ
    obtain ⟨e⟩ := hJ.2.2.1
    exact exists_isKleinFour_le_of_sup_oddCoreIn (K := J) (X := J) le_rfl
      (sup_eq_left.mpr (Subgroup.map_subtype_le _)) e hT4
  have hlayer : ∀ J ∈ markedComponents 𝓢 T N, J ≤ FooteLit.twoLayerIn N := by
    intro J hJ
    calc J = (J.subgroupOf N).map N.subtype := (Subgroup.map_subgroupOf_eq_of_le hJ.1.1).symm
      _ ≤ (pLayer ↥N 2).map N.subtype := Subgroup.map_mono (le_sSup hJ.1.2)
      _ = FooteLit.twoLayerIn N := rfl
  have hbase : ∀ J ∈ markedComponents 𝓢 T N, J ≤ base N := fun J hJ =>
    (hlayer J hJ).trans le_sup_right
  have key : ∀ {V : Subgroup G} {v : G}, IsKleinFour ↥V → orderOf v = 2 → v ∉ V →
      V ≤ Subgroup.centralizer ({v} : Set G) → V ≤ base N → v ∈ base N →
      V ≤ UnbalancedLayer.coreActionKernel K → v ∈ UnbalancedLayer.coreActionKernel K →
      ∃ E : Subgroup G, E ≤ base N ∧ E ≤ UnbalancedLayer.coreActionKernel K ∧
        IsElementaryAbelian 2 ↥E ∧ 8 ≤ Nat.card E := by
    intro V v hV hv2 hv_notin hVcent hVbase hvbase hVK hvK
    have hvpow : v ^ 2 = 1 := by rw [← hv2]; exact pow_orderOf_eq_one v
    haveI hVea : IsElementaryAbelian 2 ↥V :=
      (CFSG.ComponentClassification.Sol76.Sig.isElemAbelian_of_isKleinFour hV).isElementaryAbelian
    haveI hzpea : IsElementaryAbelian 2 ↥(Subgroup.zpowers v) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) (x := v) hvpow
    have hcV : V ≤ Subgroup.centralizer (Subgroup.zpowers v : Set G) := by
      rw [Subgroup.le_centralizer_iff]
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hcomm : Commute x v := Subgroup.mem_centralizer_singleton_iff.mp (hVcent hx)
      exact (hcomm.zpow_right n).eq
    have hV4 : Nat.card ↥V = 4 := hV.card_four
    have hW2 : Nat.card ↥(Subgroup.zpowers v) = 2 := by rw [Nat.card_zpowers, hv2]
    have hinf : V ⊓ Subgroup.zpowers v = ⊥ := by
      have hdv : Nat.card ↥(V ⊓ Subgroup.zpowers v) ∣ 2 := by
        rw [← hW2]; exact Subgroup.card_dvd_of_le inf_le_right
      have hne2 : Nat.card ↥(V ⊓ Subgroup.zpowers v) ≠ 2 := by
        intro h2
        have heq : V ⊓ Subgroup.zpowers v = Subgroup.zpowers v :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
        have hmem : v ∈ V ⊓ Subgroup.zpowers v := heq.symm ▸ Subgroup.mem_zpowers v
        exact hv_notin (Subgroup.mem_inf.mp hmem).1
      have h1 : Nat.card ↥(V ⊓ Subgroup.zpowers v) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hdv with h | h
        · exact h
        · exact absurd h hne2
      exact Subgroup.card_eq_one.mp h1
    have hnorm : V ≤ Subgroup.normalizer (Subgroup.zpowers v : Set G) :=
      hcV.trans (Subgroup.centralizer_le_normalizer _)
    have hcard : Nat.card ↥(V ⊔ Subgroup.zpowers v) = 8 := by
      have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
        (H := V) (K := Subgroup.zpowers v) hnorm
      rw [hinf, hV4, hW2] at h
      simpa using h
    refine ⟨Subgroup.zpowers v ⊔ V, sup_le (Subgroup.zpowers_le.mpr hvbase) hVbase,
      sup_le (Subgroup.zpowers_le.mpr hvK) hVK,
      IsElementaryAbelian.sup_of_le_centralizer hcV, ?_⟩
    rw [sup_comm]
    exact hcard.ge
  rcases hN.2 with h3 | heven
  ·
    have h3count : 3 ≤ (markedComponents 𝓢 T N).ncard := h3
    obtain ⟨K₁, hK₁, K₂, hK₂, hK₁₂⟩ :=
      (Set.one_lt_ncard (Set.toFinite _)).mp
        (by
          have hdiff : (markedComponents 𝓢 T N \ {K}).ncard =
              (markedComponents 𝓢 T N).ncard - 1 := Set.ncard_diff_singleton_of_mem hK
          omega : 1 < (markedComponents 𝓢 T N \ {K}).ncard)
    rw [Set.mem_diff, Set.mem_singleton_iff] at hK₁ hK₂
    obtain ⟨hK₁d, hK₁ne⟩ := hK₁
    obtain ⟨hK₂d, hK₂ne⟩ := hK₂
    obtain ⟨V, hVK₁, hV⟩ := hfour K₁ hK₁d
    have hK₁K₂ : K₁ ≤ UnbalancedLayer.coreActionKernel K₂ :=
      marked_le_coreActionKernel_of_ne hK₁d hK₂d hK₁₂
    have hK₁K : K₁ ≤ UnbalancedLayer.coreActionKernel K :=
      marked_le_coreActionKernel_of_ne hK₁d hK hK₁ne
    have hK₂K : K₂ ≤ UnbalancedLayer.coreActionKernel K :=
      marked_le_coreActionKernel_of_ne hK₂d hK hK₂ne
    have hVK₂ : V ≤ UnbalancedLayer.coreActionKernel K₂ := hVK₁.trans hK₁K₂
    have hqK₂ : CFSG.IsQuasisimple (↥K₂ ⧸ pPrimeCore 2 ↥K₂) := hK₂d.2.quotient_quasisimple hFam
    have hV2 : IsPGroup 2 V := isPGroup_of_isKleinFour hV
    obtain ⟨hcover, -, -⟩ := fixedShadow_cover_quotient hqK₂ hV2 hVK₂
    have hQeven : Even (Nat.card (↥K₂ ⧸ pPrimeCore 2 ↥K₂)) := by
      by_contra hodd
      have hodd' : Odd (Nat.card (↥K₂ ⧸ pPrimeCore 2 ↥K₂)) := Nat.not_even_iff_odd.mp hodd
      have hsolv : Group.IsSolvable (↥K₂ ⧸ pPrimeCore 2 ↥K₂) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd'
      haveI hperf : Group.IsPerfect (↥K₂ ⧸ pPrimeCore 2 ↥K₂) := hqK₂.1
      haveI hnt : Nontrivial (↥K₂ ⧸ pPrimeCore 2 ↥K₂) :=
        CFSG.LocalCores.isQuasisimple_nontrivial hqK₂
      exact Group.IsPerfect.not_isSolvable _ hsolv
    have hK₂even : Even (Nat.card ↥K₂) := by
      haveI : (pPrimeCore 2 ↥K₂).Normal := CFSG.pPrimeCore_normal
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K₂)]
      obtain ⟨m, hm⟩ := hQeven
      exact ⟨m * Nat.card (pPrimeCore 2 ↥K₂), by rw [hm]; ring⟩
    have hFodd_contra : ¬ Odd (Nat.card ↥(fixedShadow K₂ V)) := by
      intro hFodd
      have hFnorm : fixedShadow K₂ V ≤
          Subgroup.normalizer (FooteLit.oddCoreIn K₂ : Set G) :=
        fun x hx => FooteLit.mem_normalizer_oddCoreIn
          (le_normalizer (fixedShadow_le K₂ V hx))
      have hsup : Odd (Nat.card ↥(fixedShadow K₂ V ⊔ FooteLit.oddCoreIn K₂)) :=
        FooteLit.odd_card_sup_of_le_normalizer hFnorm hFodd (FooteLit.odd_card_oddCoreIn K₂)
      rw [hcover] at hsup
      exact (Nat.not_even_iff_odd.mpr hsup) hK₂even
    have hFeven : Even (Nat.card ↥(fixedShadow K₂ V)) := Nat.not_odd_iff_even.mp hFodd_contra
    obtain ⟨v, hvF, hv2⟩ : ∃ v ∈ fixedShadow K₂ V, orderOf v = 2 := by
      haveI : Fintype ↥(fixedShadow K₂ V) := Fintype.ofFinite _
      obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card
        (G := ↥(fixedShadow K₂ V)) 2
        (by rw [← Nat.card_eq_fintype_card]; exact even_iff_two_dvd.mp hFeven)
      exact ⟨(v : G), v.2, by rw [orderOf_coe]; exact hv⟩
    have hvcentV : v ∈ Subgroup.centralizer (V : Set G) := (fixedShadow_le_inf K₂ V hvF).2
    have hVcent : V ≤ Subgroup.centralizer ({v} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hvcentV x hx
    have hv_notin : v ∉ V := by
      intro hvV
      have hvK₂ : v ∈ K₂ := fixedShadow_le K₂ V hvF
      have hvcore : v ∈ UnbalancedLayer.coreActionKernel K₂ := hK₁K₂ (hVK₁ hvV)
      have hmem : v ∈ FooteLit.oddCoreIn K₂ :=
        marked_inf_coreActionKernel_le_oddCoreIn hFam hK₂d ⟨hvK₂, hvcore⟩
      have hdvd : orderOf v ∣ Nat.card ↥(FooteLit.oddCoreIn K₂) :=
        Subgroup.orderOf_dvd_natCard _ hmem
      exact (FooteLit.odd_card_oddCoreIn K₂).not_two_dvd_nat (hv2 ▸ hdvd)
    exact key (V := V) (v := v) hV hv2 hv_notin hVcent (hVK₁.trans (hbase K₁ hK₁d))
      ((hbase K₂ hK₂d) (fixedShadow_le K₂ V hvF)) (hVK₁.trans hK₁K)
      (hK₂K (fixedShadow_le K₂ V hvF))
  ·
    have h2count : 2 ≤ (markedComponents 𝓢 T N).ncard := hN.1
    obtain ⟨K₁, hK₁, hK₁ne⟩ :=
      Set.exists_ne_of_one_lt_ncard (by omega : 1 < (markedComponents 𝓢 T N).ncard) K
    obtain ⟨z, hzK, hz2⟩ : ∃ z ∈ baseKernel 𝓢 T N, orderOf z = 2 := by
      have h2 : 2 ∣ Nat.card ↥(baseKernel 𝓢 T N) := even_iff_two_dvd.mp heven
      haveI : Fintype ↥(baseKernel 𝓢 T N) := Fintype.ofFinite _
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card
        (G := ↥(baseKernel 𝓢 T N)) 2
        (by rw [← Nat.card_eq_fintype_card]; exact even_iff_two_dvd.mp heven)
      exact ⟨(z : G), z.2, by rw [orderOf_coe]; exact hz⟩
    have hzK₁ : z ∈ UnbalancedLayer.coreActionKernel K₁ :=
      baseKernel_le_coreActionKernel_of_marked hK₁ hzK
    have hzK_ : z ∈ UnbalancedLayer.coreActionKernel K :=
      baseKernel_le_coreActionKernel_of_marked hK hzK
    have hK₁K : K₁ ≤ UnbalancedLayer.coreActionKernel K :=
      marked_le_coreActionKernel_of_ne hK₁ hK hK₁ne
    have hqK₁ : CFSG.IsQuasisimple (↥K₁ ⧸ pPrimeCore 2 ↥K₁) := hK₁.2.quotient_quasisimple hFam
    have hz2' : IsPGroup 2 (Subgroup.zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one])
    obtain ⟨hcover, -, -⟩ := fixedShadow_cover_quotient hqK₁ hz2'
      (Subgroup.zpowers_le.mpr hzK₁)
    obtain ⟨e₁⟩ := hK₁.2.2.1
    obtain ⟨V, hVF, hV⟩ :=
      exists_isKleinFour_le_of_sup_oddCoreIn (K := K₁) (X := fixedShadow K₁ (Subgroup.zpowers z))
        (fixedShadow_le K₁ _) hcover e₁ hT4
    have hVcent : V ≤ Subgroup.centralizer ({z} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp
        ((fixedShadow_le_inf K₁ (Subgroup.zpowers z) (hVF hx)).2) z
        (Subgroup.mem_zpowers z)).symm
    have hz_notin : z ∉ V := by
      intro hzV
      have hmem : z ∈ FooteLit.oddCoreIn K₁ :=
        marked_inf_coreActionKernel_le_oddCoreIn hFam hK₁
          ⟨hVF.trans (fixedShadow_le K₁ _) hzV, hzK₁⟩
      have hdvd : orderOf z ∣ Nat.card ↥(FooteLit.oddCoreIn K₁) :=
        Subgroup.orderOf_dvd_natCard _ hmem
      exact (FooteLit.odd_card_oddCoreIn K₁).not_two_dvd_nat (hz2 ▸ hdvd)
    exact key (V := V) (v := z) hV hz2 hz_notin hVcent
      (hVF.trans ((fixedShadow_le K₁ (Subgroup.zpowers z)).trans (hbase K₁ hK₁)))
      ((inf_le_left : baseKernel 𝓢 T N ≤ base N) hzK)
      (hVF.trans ((fixedShadow_le K₁ (Subgroup.zpowers z)).trans hK₁K)) hzK_

end CFSG.ComponentClassification.FooteMarked
