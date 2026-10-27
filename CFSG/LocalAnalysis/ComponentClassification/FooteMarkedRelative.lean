module

public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedTransport
public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedHulls
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigBound
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecStd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCDiagCover
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMCrit
public import CFSG.GroupTheory.QuasiDihedralFusion.CharPowerStructure
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFCenter
public import CFSG.GroupTheory.PerfectLeSupCenter
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTwoComp
public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedDisconnectedNormality
public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedConjugacy
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
public import CFSG.Walter.Bender1970.S2.Involutions

public section

namespace CFSG.ComponentClassification.FooteMarked

open CFSG Subgroup
open CFSG.ComponentClassification.FooteLit
open CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.AssemblyBTwoComponents
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isQuasisimple_of_localB_component {Q : Type} [Group Q] [Finite Q]
    (hB : CFSG.Assembly.ComponentType.LocalBProperty Q)
    {a : Q} (ha : orderOf a = 2) {A : Subgroup Q}
    (hAC : A ≤ centralizer ({a} : Set Q))
    (hA : IsPComponent 2 (A.subgroupOf (centralizer ({a} : Set Q)))) :
    IsQuasisimple A := by
  let C : Subgroup Q := centralizer ({a} : Set Q)
  have hA2 : CFSG.Assembly.ComponentType.IsTwoPComponent (A.subgroupOf C) :=
    (isTwoPComponent_iff_twoComponent (A.subgroupOf C)).mpr
      ((CatalogueBAlternating.pComponent_two_iff (A.subgroupOf C)).mp hA)
  have hAc : CFSG.Assembly.IsComponentOf (A.subgroupOf C) ⊤ :=
    CFSG.ComponentClassification.AssemblyBLocalB.ordinary_at_involution hB a ha
      (A.subgroupOf C) hA2
  have hAcOpen : CFSG.Open.IsComponentOf (A.subgroupOf C) ⊤ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open
      (A.subgroupOf C) ⊤).mp hAc
  have hAc' : IsComponent (A.subgroupOf C) := (CFSG.isComponent_iff_open _).mpr hAcOpen
  exact LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hAC) hAc'.1

theorem isComponent_subgroupOf_of_localB_component {Q : Type} [Group Q] [Finite Q]
    (hB : CFSG.Assembly.ComponentType.LocalBProperty Q)
    {a : Q} (ha : orderOf a = 2) {A : Subgroup Q}
    (hAC : A ≤ centralizer ({a} : Set Q))
    (hA : IsPComponent 2 (A.subgroupOf (centralizer ({a} : Set Q)))) :
    IsComponent (A.subgroupOf (centralizer ({a} : Set Q))) := by
  let C : Subgroup Q := centralizer ({a} : Set Q)
  have hA2 : CFSG.Assembly.ComponentType.IsTwoPComponent (A.subgroupOf C) :=
    (isTwoPComponent_iff_twoComponent (A.subgroupOf C)).mpr
      ((CatalogueBAlternating.pComponent_two_iff (A.subgroupOf C)).mp hA)
  have hAc : CFSG.Assembly.IsComponentOf (A.subgroupOf C) ⊤ :=
    CFSG.ComponentClassification.AssemblyBLocalB.ordinary_at_involution hB a ha
      (A.subgroupOf C) hA2
  have hAcOpen : CFSG.Open.IsComponentOf (A.subgroupOf C) ⊤ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open
      (A.subgroupOf C) ⊤).mp hAc
  exact (CFSG.isComponent_iff_open _).mpr hAcOpen

theorem gsWeakCorr_source_le_centralizer {Q : Type} [Group Q] [Finite Q]
    {a b : Q} {A K : Subgroup Q} (hC : GrSLit.GSWeakCorr a A b K)
    (hAq : IsQuasisimple A) : A ≤ centralizer ({b} : Set Q) := by
  refine GrSLit.HeKMC.le_centralizer_of_gsWeakCorr hC ?_
  have hOpen : CFSG.Open.IsQuasisimple A :=
    (CatalogueBAlternating.quasisimple_iff_native).mp hAq
  have hcenter : pPrimeCore 2 A ≤ Subgroup.center A := by
    have h := CFSG.ClassicalInvolution.Balance.oddCore_le_center_of_isQuasisimple hOpen
    change CFSG.oddCore A ≤ Subgroup.center A at h
    rwa [CFSG.ComponentClassification.Sol78.oddCore_eq_pPrimeCore] at h
  rintro x ⟨y, hy, rfl⟩ m hm
  exact (congrArg (fun z : ↥A => (z : Q))
    (Subgroup.mem_center_iff.mp (hcenter hy) ⟨m, hm⟩)).symm

theorem exists_commuting_involution_lifts {H Q : Type} [Group H] [Finite H] [Group Q]
    (π : H →* Q) (hπ : Function.Surjective π) (hodd : Odd (Nat.card π.ker))
    {abar bbar : Q} (ha : orderOf abar = 2) (hb : orderOf bbar = 2)
    (hab : Commute abar bbar) :
    ∃ a b : H, orderOf a = 2 ∧ orderOf b = 2 ∧ Commute a b ∧
      π a = abar ∧ π b = bbar := by
  let A : CFSG.OrderReductions.InvolutionGraph.Involution Q := ⟨abar, ha⟩
  obtain ⟨a, haeq⟩ :=
    CFSG.OrderReductions.OddKernelInvolutions.exists_involution_lift π hπ hodd A
  let B : CFSG.OrderReductions.InvolutionGraph.Involution Q := ⟨bbar, hb⟩
  have hcomm : Commute (π a.val) B.val := by
    rw [haeq]
    exact hab
  obtain ⟨b, hbeq, hcommab⟩ :=
    CFSG.OrderReductions.OddKernelInvolutions.exists_commuting_involution_lift π hπ hodd a B hcomm
  exact ⟨a.val, b.val, a.property, b.property, hcommab, haeq, hbeq⟩

theorem le_conjClosure_sup_oddCore_of_normalClosure_map_eq_top
    {V A : Subgroup G} (hAV : A ≤ V)
    (h : Subgroup.normalClosure
      (SetLike.coe ((A.subgroupOf V).map (QuotientGroup.mk' (pPrimeCore 2 V)))) = ⊤) :
    V ≤ FooteLit.conjClosure A V ⊔ FooteLit.oddCoreIn V := by
  let π : V →* (V ⧸ pPrimeCore 2 V) := QuotientGroup.mk' (pPrimeCore 2 V)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  set N : Subgroup V := FooteLit.conjClosure (A.subgroupOf V) ⊤ with hN
  have hNclosure : N = Subgroup.normalClosure (A.subgroupOf V : Set V) := by
    rw [hN, FooteLit.conjClosure_top_eq_normalClosure]
  have hquot : N.map π = ⊤ := by
    have hmap := FooteLit.map_conjClosure π (A.subgroupOf V) (⊤ : Subgroup V)
    rw [← hN] at hmap
    have htop : (⊤ : Subgroup V).map π = ⊤ := by
      rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr hπ]
    rw [htop] at hmap
    rw [hmap]
    simpa only [FooteLit.conjClosure_top_eq_normalClosure] using h
  have hV : N ⊔ pPrimeCore 2 V = ⊤ := by
    have hc := Subgroup.comap_map_eq (f := π) (H := N)
    rw [QuotientGroup.ker_mk'] at hc
    rw [hquot, Subgroup.comap_top] at hc
    exact hc.symm
  have htopV : (⊤ : Subgroup V).map V.subtype = V := by
    simpa using Subgroup.subgroupOf_map_subtype (⊤ : Subgroup G) V
  have hNambient : N.map V.subtype = FooteLit.conjClosure A V := by
    have hmap := FooteLit.map_conjClosure V.subtype (A.subgroupOf V) (⊤ : Subgroup V)
    rw [← hN] at hmap
    rw [Subgroup.map_subgroupOf_eq_of_le hAV, htopV] at hmap
    exact hmap
  have hVambient : (N ⊔ pPrimeCore 2 V).map V.subtype = V := by
    rw [hV, htopV]
  have hVambient' : (N ⊔ pPrimeCore 2 V).map V.subtype =
      FooteLit.conjClosure A V ⊔ FooteLit.oddCoreIn V := by
    rw [Subgroup.map_sup, hNambient]
    rfl
  exact (calc
    V = (N ⊔ pPrimeCore 2 V).map V.subtype := hVambient.symm
    _ = FooteLit.conjClosure A V ⊔ FooteLit.oddCoreIn V := hVambient').le

theorem canonicalPerfectLift_map_quotient {H : Subgroup G}
    {A : Subgroup (H ⧸ pPrimeCore 2 H)} (hAperf : Group.IsPerfect A) :
    ((canonicalPerfectLift H A).subgroupOf H).map
      (QuotientGroup.mk' (pPrimeCore 2 H)) = A := by
  classical
  let π : H →* (H ⧸ pPrimeCore 2 H) := QuotientGroup.mk' (pPrimeCore 2 H)
  let V : Subgroup H := A.comap π
  let f : V →* A := (π.comp V.subtype).codRestrict A (fun v => v.2)
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 H) a
    refine ⟨⟨h, ?_⟩, Subtype.ext hh⟩
    change π h ∈ A
    rw [hh]
    exact a.2
  letI : Group.IsPerfect A := hAperf
  have hres := CFSG.ComponentClassification.SolMax.perfectResidual_map_eq_top f hf
  have htopA : (⊤ : Subgroup A).map A.subtype = A := by
    simpa using Subgroup.subgroupOf_map_subtype (⊤ : Subgroup (H ⧸ pPrimeCore 2 H)) A
  have hmap : ((CFSG.perfectResidual V).map V.subtype).map π = A := by
    have h1 : ((CFSG.perfectResidual V).map f).map A.subtype =
        (CFSG.perfectResidual V).map (π.comp V.subtype) := by
      rw [Subgroup.map_map]
      rfl
    rw [hres, htopA] at h1
    calc
      ((CFSG.perfectResidual V).map V.subtype).map π =
          (CFSG.perfectResidual V).map (π.comp V.subtype) := by
        rw [Subgroup.map_map]
      _ = A := h1.symm
  have hsub : (((CFSG.perfectResidual V).map V.subtype).map H.subtype).subgroupOf H =
      (CFSG.perfectResidual V).map V.subtype :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  change ((((CFSG.perfectResidual V).map V.subtype).map H.subtype).subgroupOf H).map π = A
  rw [hsub]
  exact hmap

theorem eq_of_relative_cover
    {Q : Type} [Group Q] [Finite Q] {abar bbar : Q}
    {A K N Wbar : Subgroup Q}
    (hK : IsComponent (K.subgroupOf (centralizer ({bbar} : Set Q))))
    (hKc : IsComponent ((conjugate K abar).subgroupOf (centralizer ({bbar} : Set Q))))
    (hKle : K ≤ centralizer ({bbar} : Set Q))
    (hKcle : conjugate K abar ≤ centralizer ({bbar} : Set Q))
    (hAq : IsQuasisimple A)
    (hAcent : A ≤ centralizer ({abar} : Set Q))
    (hWbar : Wbar = K ⊔ conjugate K abar)
    (hAK : A ≤ Wbar)
    (hWperf : Group.IsPerfect Wbar)
    (hNle : N ≤ Wbar)
    (hNnormal : (N.subgroupOf Wbar).Normal)
    (hNodd : Odd (Nat.card N))
    (hWN : Wbar = A ⊔ N) :
    K = A := by
  let C : Subgroup Q := centralizer ({bbar} : Set Q)
  have hWsub : (Wbar.subgroupOf C).IsSubnormal := by
    rw [hWbar, Subgroup.subgroupOf_sup hKle hKcle]
    exact CFSG.GroupTheory.isSubnormal_sup hK.2 hKc.2
  have hWleC : Wbar ≤ C := by
    rw [hWbar]
    exact sup_le hKle hKcle
  have hNleC : N ≤ C := hNle.trans hWleC
  have hNsub : (N.subgroupOf C).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_trans hNle hWleC
      hNnormal.isSubnormal hWsub
  have hNsolv : Group.IsSolvable (N.subgroupOf C) := by
    apply CFSG.FeitThompson.isSolvable_of_odd_natCard _
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNleC).toEquiv]
  have hcentral := CFSG.LocalCores.component_solvable_centralizer
    (G := C) hNsolv hNsub
  have hKN : ⁅K.subgroupOf C, N.subgroupOf C⁆ = ⊥ := hcentral.1 (K.subgroupOf C) hK
  have hKcN : ⁅(conjugate K abar).subgroupOf C, N.subgroupOf C⁆ = ⊥ :=
    hcentral.1 ((conjugate K abar).subgroupOf C) hKc
  have hKcomm : ∀ k ∈ K, ∀ n ∈ N, k * n = n * k := by
    intro k hk n hn
    have hkC : (⟨k, hKle hk⟩ : C) ∈ K.subgroupOf C := by
      rw [Subgroup.mem_subgroupOf]
      exact hk
    have hnC : (⟨n, hNleC hn⟩ : C) ∈ N.subgroupOf C := by
      rw [Subgroup.mem_subgroupOf]
      exact hn
    have hcent := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKN) hkC
    have h := (Subgroup.mem_centralizer_iff.mp hcent) ⟨n, hNleC hn⟩ hnC
    exact (congrArg (fun z : C => (z : Q)) h).symm
  have hKccomm : ∀ k ∈ conjugate K abar, ∀ n ∈ N, k * n = n * k := by
    intro k hk n hn
    have hkC : (⟨k, hKcle hk⟩ : C) ∈ (conjugate K abar).subgroupOf C := by
      rw [Subgroup.mem_subgroupOf]
      exact hk
    have hnC : (⟨n, hNleC hn⟩ : C) ∈ N.subgroupOf C := by
      rw [Subgroup.mem_subgroupOf]
      exact hn
    have hcent := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKcN) hkC
    have h := (Subgroup.mem_centralizer_iff.mp hcent) ⟨n, hNleC hn⟩ hnC
    exact (congrArg (fun z : C => (z : Q)) h).symm
  have hKleCent : K ≤ centralizer (N : Set Q) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact (hKcomm k hk n hn).symm
  have hKcleCent : conjugate K abar ≤ centralizer (N : Set Q) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact (hKccomm k hk n hn).symm
  have hWleCent : Wbar ≤ centralizer (N : Set Q) := by
    rw [hWbar]
    exact sup_le hKleCent hKcleCent
  have hNleCent : N ≤ centralizer (Wbar : Set Q) := by
    have hcomm : ⁅Wbar, N⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hWleCent
    rwa [commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
  have hNc : ∀ z ∈ N, ∀ h ∈ Wbar, z * h = h * z := by
    intro z hz h hh
    exact ((Subgroup.mem_centralizer_iff.mp (hNleCent hz)) h hh).symm
  have hperf : Wbar ≤ ⁅Wbar, Wbar⁆ := by
    have hmap := congrArg (Subgroup.map Wbar.subtype)
      (Group.IsPerfect.commutator_eq_top (G := Wbar))
    have htop : (⊤ : Subgroup Wbar).map Wbar.subtype = Wbar := by
      simpa using Subgroup.subgroupOf_map_subtype (⊤ : Subgroup Q) Wbar
    have hmap' : (⁅Wbar, Wbar⁆ : Subgroup Q) = Wbar := by
      rw [← Subgroup.map_subtype_commutator Wbar, hmap, htop]
    exact le_of_eq hmap'.symm
  have hWleA : Wbar ≤ A :=
    CFSG.ClassicalInvolution.Generic.le_of_perfect_of_le_sup_central
      hAK hNle hNc hperf (by rw [hWN])
  have hAeqW : A = Wbar := le_antisymm hAK hWleA
  have hKleW : K ≤ Wbar := by rw [hWbar]; exact le_sup_left
  have hKA : K ≤ A := hKleW.trans hWleA
  have hKcEqK : conjugate K abar = K :=
    CFSG.ComponentClassification.UnbalancedCorr.conjugate_eq_self_of_le_centralizer
      (hKA.trans hAcent)
  have : A = K := by
    rw [hAeqW, hWbar, hKcEqK, sup_idem]
  exact this.symm

theorem quotient_image_isComponent_of_isTwoComponentIn
    {C J : Subgroup G} (hJC : FooteLit.IsTwoComponentIn J C)
    {T : Type} [Group T] [IsSimpleGroup T]
    (eJ : J ⧸ pPrimeCore 2 J ≃* T) :
    IsComponent ((J.subgroupOf C).map (QuotientGroup.mk' (pPrimeCore 2 C))) ∧
      IsSimpleGroup ((J.subgroupOf C).map (QuotientGroup.mk' (pPrimeCore 2 C))) := by
  let πC := QuotientGroup.mk' (pPrimeCore 2 C)
  let J' := J.subgroupOf C
  let K := J'.map πC
  have hK : IsComponent K := (CatalogueBPrimeJoin.quotient_component_iff_core_quotient
    2 J' hJC.2.choose_spec.2.1).mpr
      (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 J' hJC.2)
  let eK : K ≃* T :=
    (CatalogueBHeldSmallCore.subnormalCoreQuotientEquivImage
      2 J' hJC.2.choose_spec.2.1).symm.trans
        ((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
          (subgroupOfEquivOfLe hJC.1)).trans eJ)
  exact ⟨hK, eK.isSimpleGroup⟩

theorem isQuasisimple_oddCoreQuotient_of_perfect_simple
    {P : Type} [Group P] [Finite P] {T : Type} [Group T] [IsSimpleGroup T]
    (hP : Group.IsPerfect P) (e : P ⧸ pPrimeCore 2 P ≃* T) :
    IsQuasisimple (P ⧸ pPrimeCore 2 P) := by
  let Q := P ⧸ pPrimeCore 2 P
  haveI : Group.IsPerfect Q :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (pPrimeCore 2 P))
      (QuotientGroup.mk'_surjective (pPrimeCore 2 P))
  haveI : IsSimpleGroup Q := e.isSimpleGroup
  haveI : Nontrivial Q := e.toEquiv.nontrivial
  refine (LocalCores.isQuasisimple_of_isSimpleGroup (Q := Q) ?_).1
  by_contra h
  push Not at h
  haveI : IsMulCommutative Q := ⟨⟨fun a b => h a b⟩⟩
  exact Group.IsPerfect.not_isMulCommutative (G := Q) inferInstance

theorem gsFixedLayer_eq_self_of_isQuasisimple {H : Type} [Group H] [Finite H]
    {L : Subgroup H} {y : H} (hLy : L ≤ centralizer ({y} : Set H))
    (hLq : IsQuasisimple L) : UnbalancedGS.gsFixedLayer L y = L := by
  rw [UnbalancedGS.gsFixedLayer, inf_eq_left.mpr hLy,
    CFSG.LocalAnalysis.ComponentInitial.pLayer_two_eq_top_of_isQuasisimple hLq]
  simpa using Subgroup.subgroupOf_map_subtype (⊤ : Subgroup H) L

theorem map_inf_oddCore_le_oddCore_map {H : Subgroup G} (P : Subgroup H) :
    (P ⊓ CFSG.pPrimeCore 2 H).map H.subtype ≤
      FooteLit.oddCoreIn (P.map H.subtype) := by
  let S : Subgroup H := P ⊓ CFSG.pPrimeCore 2 H
  let T : Subgroup G := S.map H.subtype
  let P' : Subgroup G := P.map H.subtype
  have hTle : T ≤ P' := Subgroup.map_mono inf_le_left
  have hSsub : S.subgroupOf P = (CFSG.pPrimeCore 2 H).subgroupOf P := by
    ext x
    simp [S]
  have hSnormal : (S.subgroupOf P).Normal := by
    rw [hSsub]
    exact (CFSG.pPrimeCore_normal (p := 2) (G := H)).subgroupOf P
  have hTnormal : (T.subgroupOf P').Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp hn
    obtain ⟨p, hp, hpe⟩ := Subgroup.mem_map.mp g.2
    let sP : P := ⟨s, hs.1⟩
    have hsSub : sP ∈ S.subgroupOf P := by
      rw [Subgroup.mem_subgroupOf]
      exact hs
    let pP : P := ⟨p, hp⟩
    let cP : P := pP * sP * pP⁻¹
    have hcSub : cP ∈ S.subgroupOf P := hSnormal.conj_mem sP hsSub pP
    rw [Subgroup.mem_subgroupOf] at hcSub
    refine Subgroup.mem_map.mpr ⟨cP.1, hcSub, ?_⟩
    show H.subtype cP.1 = (g : G) * (n : G) * (g : G)⁻¹
    rw [← hpe, ← hse]
    simp [cP, sP, pP]
  have hOodd : Odd (Nat.card (CFSG.pPrimeCore 2 H)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := H))
  have hTodd : Odd (Nat.card (T.subgroupOf P')) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv]
    exact hOodd.of_dvd_nat
      ((Subgroup.card_map_dvd S H.subtype).trans (Subgroup.card_dvd_of_le inf_le_right))
  have hle : T.subgroupOf P' ≤ CFSG.pPrimeCore 2 P' :=
    CFSG.le_pPrimeCore_of_normal_coprime hTnormal
      (Nat.coprime_two_left.mpr hTodd)
  calc
    T = (T.subgroupOf P').map P'.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hTle).symm
    _ ≤ (CFSG.pPrimeCore 2 P').map P'.subtype := Subgroup.map_mono hle
    _ = FooteLit.oddCoreIn P' := rfl

theorem canonicalPerfectLift_coreActionKernel {H : Subgroup G}
    {A : Subgroup (H ⧸ pPrimeCore 2 H)} {b : H}
    {bbar : H ⧸ pPrimeCore 2 H}
    (hbbar : QuotientGroup.mk' (pPrimeCore 2 H) b = bbar)
    (hAcent : A ≤ centralizer ({bbar} : Set (H ⧸ pPrimeCore 2 H))) :
    H.subtype b ∈ UnbalancedLayer.coreActionKernel (canonicalPerfectLift H A) := by
  classical
  let π : H →* (H ⧸ pPrimeCore 2 H) := QuotientGroup.mk' (pPrimeCore 2 H)
  let V : Subgroup H := A.comap π
  let W0 : Subgroup H := (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual V).map V.subtype
  let P : Subgroup G := W0.map H.subtype
  have hP : P = canonicalPerfectLift H A := rfl
  have hπb : π b = bbar := hbbar
  have hbbarCent : bbar ∈ Subgroup.centralizer (A : Set (H ⧸ pPrimeCore 2 H)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact mem_centralizer_singleton_iff.mp (hAcent ha)
  have hbbarN : bbar ∈ Subgroup.normalizer (A : Set (H ⧸ pPrimeCore 2 H)) :=
    Subgroup.centralizer_le_normalizer (A : Set (H ⧸ pPrimeCore 2 H)) hbbarCent
  have hbN : b ∈ Subgroup.comap π (Subgroup.normalizer (A : Set (H ⧸ pPrimeCore 2 H))) := by
    rw [Subgroup.mem_comap, hπb]
    exact hbbarN
  have hbnormW0 : b ∈ Subgroup.normalizer (W0 : Set H) := by
    have h := CFSG.RankThreeCoreUniqueness.Helpers.normalizer_preimage_le_normalizer_perfectResidualOf
      π A hbN
    simpa [W0, CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf] using h
  have hbnormP : H.subtype b ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro p
    constructor
    · intro hp
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hp
      refine Subgroup.mem_map.mpr ⟨b * w * b⁻¹, ?_, by simp⟩
      exact (Subgroup.mem_normalizer_iff.mp hbnormW0 w).mp hw
    · intro hp
      obtain ⟨w, hw, hw_eq⟩ := Subgroup.mem_map.mp hp
      have hbw : b⁻¹ * w * b ∈ W0 := by
        simpa using (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (W0 : Set H)).inv_mem hbnormW0) w).mp hw
      refine Subgroup.mem_map.mpr ⟨b⁻¹ * w * b, hbw, ?_⟩
      rw [map_mul, map_mul, map_inv, hw_eq]
      group
  refine mem_coreActionKernel.mpr ⟨by simpa [hP] using hbnormP, ?_⟩
  intro p hp
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hp
  have hwV : w ∈ V := (Subgroup.map_subtype_le (CFSG.perfectResidual V)) hw
  have hwA : π w ∈ A := Subgroup.mem_comap.mp hwV
  have hbw : b⁻¹ * w * b ∈ W0 := by
    simpa using (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (W0 : Set H)).inv_mem hbnormW0) w).mp hw
  have hcW0 : w⁻¹ * b⁻¹ * w * b ∈ W0 := by
    rw [show w⁻¹ * b⁻¹ * w * b = w⁻¹ * (b⁻¹ * w * b) by group]
    exact W0.mul_mem (W0.inv_mem hw) hbw
  have hcKer : w⁻¹ * b⁻¹ * w * b ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    have hcomm : π w * bbar = bbar * π w :=
      mem_centralizer_singleton_iff.mp (hAcent hwA)
    have hconj : bbar⁻¹ * π w * bbar = π w := by
      calc
        bbar⁻¹ * π w * bbar = bbar⁻¹ * (π w * bbar) := by group
        _ = bbar⁻¹ * (bbar * π w) := by rw [hcomm]
        _ = π w := by group
    simp only [map_mul, map_inv, hπb]
    rw [show (π w)⁻¹ * bbar⁻¹ * π w * bbar =
      (π w)⁻¹ * (bbar⁻¹ * π w * bbar) by group, hconj, inv_mul_cancel]
  have hcO : w⁻¹ * b⁻¹ * w * b ∈ CFSG.pPrimeCore 2 H := by
    simpa [π, QuotientGroup.ker_mk'] using hcKer
  have hcinf : w⁻¹ * b⁻¹ * w * b ∈ W0 ⊓ CFSG.pPrimeCore 2 H :=
    ⟨hcW0, hcO⟩
  have hmem := map_inf_oddCore_le_oddCore_map (G := G) W0
    (Subgroup.mem_map.mpr ⟨w⁻¹ * b⁻¹ * w * b, hcinf, rfl⟩)
  change H.subtype (w⁻¹ * b⁻¹ * w * b) ∈ FooteLit.oddCoreIn P
  exact hmem

theorem relative_component_sup_le_normalizer
    {Q : Type} [Group Q] [Finite Q] {abar bbar : Q} {K : Subgroup Q}
    (hK : IsComponent (K.subgroupOf (centralizer ({bbar} : Set Q))))
    (hKc : IsComponent ((conjugate K abar).subgroupOf
      (centralizer ({bbar} : Set Q))))
    (hKle : K ≤ centralizer ({bbar} : Set Q))
    (hKcle : conjugate K abar ≤ centralizer ({bbar} : Set Q)) :
    K ⊔ conjugate K abar ≤ Subgroup.normalizer (K : Set Q) := by
  let C : Subgroup Q := centralizer ({bbar} : Set Q)
  let M : Subgroup C := K.subgroupOf C
  let L : Subgroup C := (conjugate K abar).subgroupOf C
  have hM : IsComponent M := by simpa [M, C] using hK
  have hL : IsComponent L := by simpa [L, C] using hKc
  have hKL : conjugate K abar ≤ Subgroup.normalizer (K : Set Q) := by
    rcases CFSG.LocalCores.distinct_components_commute hM hL with hEq | hComm
    · have hle : conjugate K abar ≤ K := by
        intro x hx
        have hxC : x ∈ C := hKcle hx
        have hxL : (⟨x, hxC⟩ : C) ∈ L := by
          rw [Subgroup.mem_subgroupOf]
          exact hx
        have hxM : (⟨x, hxC⟩ : C) ∈ M := by
          rw [← hEq] at hxL
          exact hxL
        exact Subgroup.mem_subgroupOf.mp hxM
      exact hle.trans K.le_normalizer
    · have hcent : conjugate K abar ≤ Subgroup.centralizer (K : Set Q) := by
        intro x hx y hy
        have hxC : x ∈ C := hKcle hx
        have hyC : y ∈ C := hKle hy
        have hxL : (⟨x, hxC⟩ : C) ∈ L := by
          rw [Subgroup.mem_subgroupOf]
          exact hx
        have hyM : (⟨y, hyC⟩ : C) ∈ M := by
          rw [Subgroup.mem_subgroupOf]
          exact hy
        have hmem : ⁅(⟨y, hyC⟩ : C), (⟨x, hxC⟩ : C)⁆ ∈ ⁅M, L⁆ :=
          Subgroup.commutator_mem_commutator hyM hxL
        rw [hComm] at hmem
        have hcomm : (⟨y, hyC⟩ : C) * (⟨x, hxC⟩ : C) =
            (⟨x, hxC⟩ : C) * (⟨y, hyC⟩ : C) :=
          commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)
        exact congrArg (fun z : C => (z : Q)) hcomm
      exact hcent.trans (Subgroup.centralizer_le_normalizer (K : Set Q))
  exact sup_le K.le_normalizer hKL

theorem relative_normal_generation
    {Q : Type} [Group Q] [Finite Q] {abar bbar : Q}
    {A K : Subgroup Q} (ha : orderOf abar = 2)
    (hK : IsComponent (K.subgroupOf (centralizer ({bbar} : Set Q))))
    (hKc : IsComponent ((conjugate K abar).subgroupOf
      (centralizer ({bbar} : Set Q))))
    (hKle : K ≤ centralizer ({bbar} : Set Q))
    (hKcle : conjugate K abar ≤ centralizer ({bbar} : Set Q))
    (hAq : IsQuasisimple A)
    (hAcent : A ≤ centralizer ({abar} : Set Q))
    (hAK : A ≤ K ⊔ conjugate K abar) :
    K ⊔ conjugate K abar ≤
      FooteLit.conjClosure A (K ⊔ conjugate K abar) ⊔
        FooteLit.oddCoreIn (K ⊔ conjugate K abar) := by
  let C : Subgroup Q := centralizer ({bbar} : Set Q)
  let V : Subgroup Q := K ⊔ conjugate K abar
  have hVM : V ≤ Subgroup.normalizer (K : Set Q) :=
    relative_component_sup_le_normalizer hK hKc hKle hKcle
  have haa : abar * abar = 1 := by
    rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have haV : abar ∈ Subgroup.normalizer (V : Set Q) := by
    have hconj : conjugate V abar = V := by
      dsimp [V]
      rw [conjugate_sup, conjugate_conjugate_self_of_mul_self haa, sup_comm]
    have hainv : abar⁻¹ = abar := inv_eq_of_mul_eq_one_right haa
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa [conjugate, hainv] using hconj
  have hKpC : IsPComponent 2 (K.subgroupOf C) :=
    CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hK
  have hWperf : ⁅A, A⁆ = A := Subgroup.isPerfect_iff.mp hAq.1
  have hAne : A ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot A).mp
      (CFSG.LocalCores.isQuasisimple_nontrivial hAq)
  have hWodd : ¬ A ≤ FooteLit.oddCoreIn V := by
    intro hle
    have hOodd : Odd (Nat.card (FooteLit.oddCoreIn V)) := by
      dsimp [FooteLit.oddCoreIn]
      rw [Subgroup.card_map_of_injective V.subtype_injective]
      exact Nat.coprime_two_left.mp
        (CFSG.pPrimeCore_coprime_card (p := 2) (G := V))
    have hAodd : Odd (Nat.card A) :=
      hOodd.of_dvd_nat (Subgroup.card_dvd_of_le hle)
    haveI : Nontrivial A := CFSG.LocalCores.isQuasisimple_nontrivial hAq
    haveI : Group.IsPerfect A := hAq.1
    exact Group.IsPerfect.not_isSolvable A (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hAodd)
  have hNC := UnbalancedCorr.normalClosure_map_eq_top_of_orbit haa hKle hKpC rfl hVM haV
    hAK hAcent hWperf hWodd
  exact le_conjClosure_sup_oddCore_of_normalClosure_map_eq_top hAK hNC

theorem map_oddCoreIn_subgroupOf_eq_bot {C J : Subgroup G}
    (hJC : FooteLit.IsTwoComponentIn J C) :
    ((FooteLit.oddCoreIn J).subgroupOf C).map
      (QuotientGroup.mk' (pPrimeCore 2 C)) = ⊥ := by
  rw [Subgroup.map_eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker]
  have hxJ : (x : G) ∈ FooteLit.oddCoreIn J := Subgroup.mem_subgroupOf.mp hx
  have hxOC : (x : G) ∈ FooteLit.oddCoreIn C :=
    FooteLit.oddCoreIn_le_of_isTwoComponentIn hJC hxJ
  have hxmap : (x : G) ∈ (CFSG.pPrimeCore 2 C).map C.subtype := hxOC
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxmap
  have hyx' : y = x := C.subtype_injective hyx
  exact (QuotientGroup.eq_one_iff x).mpr (by simpa [hyx'] using hy)

theorem fixedShadowAt_canonical_lift_map_eq {H : Subgroup G}
    {A : Subgroup (H ⧸ pPrimeCore 2 H)} {b : H}
    {bbar : H ⧸ pPrimeCore 2 H}
    (hAq : IsQuasisimple A)
    (hPq : IsQuasisimple (canonicalPerfectLift H A ⧸
      pPrimeCore 2 (canonicalPerfectLift H A)))
    (hPmap : ((canonicalPerfectLift H A).subgroupOf H).map
      (QuotientGroup.mk' (pPrimeCore 2 H)) = A)
    (hbG2 : orderOf (H.subtype b) = 2)
    (hbbar : QuotientGroup.mk' (pPrimeCore 2 H) b = bbar)
    (hbCore : H.subtype b ∈ UnbalancedLayer.coreActionKernel
      (canonicalPerfectLift H A)) :
    ((fixedShadowAt (canonicalPerfectLift H A) (H.subtype b)).subgroupOf H).map
      (QuotientGroup.mk' (pPrimeCore 2 H)) = A := by
  classical
  let π : H →* (H ⧸ pPrimeCore 2 H) := QuotientGroup.mk' (pPrimeCore 2 H)
  let P : Subgroup G := canonicalPerfectLift H A
  let Pb : Subgroup G := fixedShadowAt P (H.subtype b)
  have hU : IsPGroup 2 (zpowers (H.subtype b)) :=
    isPGroup_zpowers_of_orderOf_eq_two hbG2
  have hUK : zpowers (H.subtype b) ≤ UnbalancedLayer.coreActionKernel P :=
    Subgroup.zpowers_le.mpr hbCore
  obtain ⟨hcover, -, -⟩ := fixedShadow_cover_quotient hPq hU hUK
  have hcover' : Pb ⊔ FooteLit.oddCoreIn P = P := by
    simpa [Pb, P, fixedShadow_zpowers] using hcover
  have hPH : P ≤ H := by
    dsimp [P, canonicalPerfectLift]
    exact Subgroup.map_subtype_le _
  have hPbH : Pb ≤ H := (fixedShadowAt_le P (H.subtype b)).trans hPH
  have hOH : FooteLit.oddCoreIn P ≤ H :=
    (show FooteLit.oddCoreIn P ≤ P from Subgroup.map_subtype_le _).trans hPH
  have hcoverH : (Pb.subgroupOf H) ⊔ (FooteLit.oddCoreIn P).subgroupOf H =
      P.subgroupOf H := by
    have h := congrArg (fun X : Subgroup G => X.subgroupOf H) hcover'
    rwa [Subgroup.subgroupOf_sup hPbH hOH] at h
  let B : Subgroup (H ⧸ pPrimeCore 2 H) := (Pb.subgroupOf H).map π
  let Z : Subgroup (H ⧸ pPrimeCore 2 H) := (FooteLit.oddCoreIn P).subgroupOf H |>.map π
  have hBZ : B ⊔ Z = A := by
    rw [show B ⊔ Z = ((Pb.subgroupOf H) ⊔ (FooteLit.oddCoreIn P).subgroupOf H).map π from
      (Subgroup.map_sup _ _ _).symm, hcoverH]
    exact hPmap
  have hBH : B ≤ A := hBZ ▸ le_sup_left
  have hZH : Z ≤ A := hBZ ▸ le_sup_right
  have hOPnormalP : ((FooteLit.oddCoreIn P).subgroupOf P).Normal :=
    CFSG.ComponentClassification.GSThmB.B5a.oddCoreIn_subgroupOf_normal P
  have hZnormalA : (Z.subgroupOf A).Normal := by
    refine ⟨fun z hz a => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    obtain ⟨o, ho, hzo⟩ := Subgroup.mem_map.mp hz
    have hoO : (o : G) ∈ FooteLit.oddCoreIn P := Subgroup.mem_subgroupOf.mp ho
    have haA : (a : H ⧸ pPrimeCore 2 H) ∈ (P.subgroupOf H).map π := by
      rw [hPmap]
      exact a.property
    obtain ⟨p, hp, hpa⟩ := Subgroup.mem_map.mp haA
    have hpP : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hp
    have hoP : (o : G) ∈ P := (show FooteLit.oddCoreIn P ≤ P from Subgroup.map_subtype_le _) hoO
    have hconjO : (p : G) * (o : G) * (p : G)⁻¹ ∈ FooteLit.oddCoreIn P := by
      have hconj := hOPnormalP.conj_mem ⟨(o : G), hoP⟩
        (by rw [Subgroup.mem_subgroupOf]; exact hoO) ⟨(p : G), hpP⟩
      rw [Subgroup.mem_subgroupOf] at hconj
      exact hconj
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hzo, ← hpa]
    change π (p * o * p⁻¹) ∈ Z
    refine Subgroup.mem_map.mpr ⟨p * o * p⁻¹, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    simpa using hconjO
  have hZoddA : Odd (Nat.card (Z.subgroupOf A)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv]
    have hOodd : Odd (Nat.card (FooteLit.oddCoreIn P)) := by
      dsimp [FooteLit.oddCoreIn]
      rw [Subgroup.card_map_of_injective P.subtype_injective]
      exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := P))
    have hdvd : Nat.card Z ∣ Nat.card (FooteLit.oddCoreIn P) :=
      (Subgroup.card_map_dvd _ π).trans (by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOH).toEquiv])
    exact hOodd.of_dvd_nat hdvd
  have hZcenterA : Z.subgroupOf A ≤ Subgroup.center A := by
    have hZcore : Z.subgroupOf A ≤ CFSG.pPrimeCore 2 A :=
      CFSG.le_pPrimeCore_of_normal_coprime hZnormalA
        (Nat.coprime_two_left.mpr hZoddA)
    have hOpen : CFSG.Open.IsQuasisimple A :=
      (CatalogueBAlternating.quasisimple_iff_native).mp hAq
    have h := CFSG.ClassicalInvolution.Balance.oddCore_le_center_of_isQuasisimple hOpen
    change CFSG.oddCore A ≤ Subgroup.center A at h
    rw [CFSG.ComponentClassification.Sol78.oddCore_eq_pPrimeCore] at h
    exact hZcore.trans h
  have hZc : ∀ z ∈ Z, ∀ a ∈ A, z * a = a * z := by
    intro z hz a ha
    have hzA : z ∈ A := hZH hz
    have hzZ : (⟨z, hzA⟩ : A) ∈ Z.subgroupOf A := by
      rw [Subgroup.mem_subgroupOf]
      exact hz
    have hc := hZcenterA hzZ
    have h := Subgroup.mem_center_iff.mp hc ⟨a, ha⟩
    exact (congrArg (fun x : A => (x : H ⧸ pPrimeCore 2 H)) h).symm
  have hperf : A ≤ ⁅A, A⁆ := by
    rw [Subgroup.isPerfect_iff.mp hAq.1]
  have hAeq : A = B := by
    apply le_antisymm _ hBH
    exact CFSG.ClassicalInvolution.Generic.le_of_perfect_of_le_sup_central
      hBH hZH hZc hperf (hBZ ▸ le_rfl)
  simpa [B, Pb, P, π] using hAeq.symm

theorem conjClosure_eq_of_perfect_le_sup_odd {V A : Subgroup G}
    (hAV : A ≤ V) (hV : Group.IsPerfect V)
    (hle : V ≤ FooteLit.conjClosure A V ⊔ FooteLit.oddCoreIn V) :
    FooteLit.conjClosure A V = V := by
  let N : Subgroup G := FooteLit.conjClosure A V
  have hNV : N ≤ V := by
    rw [show N = FooteLit.conjClosure A V from rfl, FooteLit.conjClosure_eq_iSup]
    refine iSup₂_le ?_
    intro e he
    rintro x ⟨a, ha, rfl⟩
    simpa [conjugate] using V.mul_mem (V.mul_mem (V.inv_mem he) (hAV ha)) he
  have hVN : V ≤ Subgroup.normalizer (N : Set G) :=
    Sol78.le_normalizer_conjClosure A V
  have hON : FooteLit.oddCoreIn V ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.map_subtype_le (pPrimeCore 2 V)).trans hVN
  have hOdd : Odd (Nat.card (FooteLit.oddCoreIn V)) := FooteLit.odd_card_oddCoreIn V
  have hVleN : V ≤ N :=
    GSThmB.CorC.le_of_perfect_of_le_sup_odd hON hOdd
      (Subgroup.isPerfect_iff.mp hV) (by simpa [N] using hle)
  exact le_antisymm (by simpa [N] using hNV) hVleN

structure RelativePerfectLiftData {G : Type} [Group G] {H : Subgroup G}
    (V : Subgroup (H ⧸ pPrimeCore 2 H)) (P : Subgroup G) (b : H) where
  D : Subgroup H
  D_map : D.map (QuotientGroup.mk' (pPrimeCore 2 H)) = V
  W0 : Subgroup H
  W0_perfect : Group.IsPerfect W0
  W0_map : W0.map (QuotientGroup.mk' (pPrimeCore 2 H)) = V
  W0_le_D : W0 ≤ D
  P0_le_W0 : P.subgroupOf H ≤ W0
  W : Subgroup G
  W_eq : W = W0.map H.subtype
  W_le_H : W ≤ H
  W_le_Cb : W ≤ Subgroup.centralizer ({H.subtype b} : Set G)
  W_perfect : Group.IsPerfect W
  P_le_W : P ≤ W
  W_map : (W.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H)) = V
  W_normal_gen : W ≤ FooteLit.conjClosure P W ⊔ (W ⊓ FooteLit.oddCoreIn H)
  R_le_W : W ⊓ FooteLit.oddCoreIn H ≤ W
  R_odd : Odd (Nat.card ↥(W ⊓ FooteLit.oddCoreIn H))

noncomputable def exists_relative_perfect_lift_normal_generation
    {H : Subgroup G} {b : H} (hb : orderOf b = 2)
    {V : Subgroup (H ⧸ pPrimeCore 2 H)} (hVperf : Group.IsPerfect V)
    (hVcent : V ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (pPrimeCore 2 H) b} : Set (H ⧸ pPrimeCore 2 H)))
    {P : Subgroup G} (hPH : P ≤ H)
    (hPb : P ≤ Subgroup.centralizer ({H.subtype b} : Set G))
    (hPperf : Group.IsPerfect P)
    (hconj : FooteLit.conjClosure ((P.subgroupOf H).map
      (QuotientGroup.mk' (pPrimeCore 2 H))) V = V) :
    RelativePerfectLiftData V P b := by
  classical
  let π : H →* (H ⧸ pPrimeCore 2 H) := QuotientGroup.mk' (pPrimeCore 2 H)
  let Cb : Subgroup H := Subgroup.centralizer ({b} : Set H)
  let D : Subgroup H := V.comap π ⊓ Cb
  let W0 : Subgroup H := (CFSG.perfectResidual D).map D.subtype
  let W : Subgroup G := W0.map H.subtype
  let A : Subgroup (H ⧸ pPrimeCore 2 H) := (P.subgroupOf H).map π
  have hAV : A ≤ V := by
    rw [← hconj]
    exact FooteLit.le_conjClosure A V
  have hbb : b * b = 1 := by
    rw [← pow_two, ← hb, pow_orderOf_eq_one]
  have hU : IsPGroup 2 (Subgroup.zpowers b) :=
    isPGroup_zpowers_of_orderOf_eq_two hb
  have hCbmap : Subgroup.centralizer ({π b} : Set (H ⧸ pPrimeCore 2 H)) =
      Cb.map π := by
    rw [← UnbalancedLayer.centralizer_zpowers_eq (π b),
      ← MonoidHom.map_zpowers π b,
      GSThmB.OddQuot.centralizer_map_eq (H := H) hU,
      UnbalancedLayer.centralizer_zpowers_eq b]
  have hDmap : D.map π = V := by
    refine le_antisymm ?_ ?_
    · intro v hv
      obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hv
      exact hd.1
    · intro v hv
      have hvC : v ∈ Subgroup.centralizer ({π b} : Set (H ⧸ pPrimeCore 2 H)) :=
        hVcent hv
      rw [hCbmap] at hvC
      obtain ⟨h, hhCb, hhpi⟩ := Subgroup.mem_map.mp hvC
      refine Subgroup.mem_map.mpr ⟨h, ?_, hhpi⟩
      refine ⟨?_, hhCb⟩
      exact Subgroup.mem_comap.mpr (by rw [hhpi]; exact hv)
  let f : D →* V :=
    { toFun := fun d => ⟨π (d : H), d.2.1⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }
  have hf : Function.Surjective f := by
    intro v
    have hv : (v : H ⧸ pPrimeCore 2 H) ∈ D.map π := by
      rw [hDmap]
      exact v.2
    obtain ⟨d, hd, hdpi⟩ := Subgroup.mem_map.mp hv
    refine ⟨⟨d, hd⟩, ?_⟩
    ext
    exact hdpi
  haveI : Group.IsPerfect V := hVperf
  have htop : (CFSG.perfectResidual D).map f = ⊤ :=
    SolMax.perfectResidual_map_eq_top f hf
  have hW0map : W0.map π = V := by
    have h := congrArg (Subgroup.map V.subtype) htop
    have hcomp : V.subtype.comp f = π.comp D.subtype := by
      ext d
      rfl
    rw [Subgroup.map_top, Subgroup.range_subtype] at h
    simpa [W0, Subgroup.map_map, hcomp] using h
  have hW0perf : Group.IsPerfect W0 := by
    change Group.IsPerfect
      ((CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual D).map D.subtype)
    exact CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidualOf_isPerfect D
  have hW0leD : W0 ≤ D := Subgroup.map_subtype_le _
  have hP0perf : Group.IsPerfect (P.subgroupOf H) := by
    haveI : Group.IsPerfect P := hPperf
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hPH).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPH).symm.surjective
  have hP0D : P.subgroupOf H ≤ D := by
    intro p hp
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_comap]
      exact hAV (Subgroup.mem_map.mpr ⟨p, hp, rfl⟩)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hpP : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hp
      have hG := Subgroup.mem_centralizer_singleton_iff.mp (hPb hpP)
      apply H.subtype_injective
      simpa using hG
  have hP0W0 : P.subgroupOf H ≤ W0 := by
    change P.subgroupOf H ≤
      (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual D).map D.subtype
    exact CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf
      (P.subgroupOf H) D hP0perf hP0D
  have hP_W : P ≤ W := by
    have h := Subgroup.map_mono (f := H.subtype) hP0W0
    rwa [Subgroup.map_subgroupOf_eq_of_le hPH] at h
  have hWH : W ≤ H := Subgroup.map_subtype_le _
  have hWleCb : W ≤ Subgroup.centralizer ({H.subtype b} : Set G) := by
    rintro w ⟨w0, hw0, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hw0D : w0 ∈ D := hW0leD hw0
    have hw0C : w0 ∈ Cb := (Subgroup.mem_inf.mp hw0D).2
    have hh := Subgroup.mem_centralizer_singleton_iff.mp hw0C
    simpa using congrArg (fun z : H => (z : G)) hh
  have hWperf : Group.IsPerfect W := by
    haveI : Group.IsPerfect W0 := hW0perf
    simpa [W] using Group.IsPerfect.map (H := W0) (f := H.subtype)
  let N : Subgroup G := FooteLit.conjClosure P W
  have hNW : N ≤ W := by
    rw [show N = FooteLit.conjClosure P W from rfl, FooteLit.conjClosure_eq_iSup]
    refine iSup₂_le ?_
    intro e he
    rintro x ⟨p, hp, rfl⟩
    simpa [conjugate] using W.mul_mem (W.mul_mem (W.inv_mem he) (hP_W hp)) he
  have hNH : N ≤ H := hNW.trans hWH
  have hWsub : W.subgroupOf H = W0 := by
    ext h
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨w0, hw0, hEq⟩
      exact H.subtype_injective hEq ▸ hw0
    · intro hh
      exact Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
  have hWmap : (W.subgroupOf H).map π = V := by
    rw [hWsub]
    exact hW0map
  let C : Subgroup H := FooteLit.conjClosure (P.subgroupOf H) (W.subgroupOf H)
  have hNmapH : C.map H.subtype = N := by
    dsimp [C, N]
    rw [FooteLit.map_conjClosure, Subgroup.map_subgroupOf_eq_of_le hPH,
      Subgroup.map_subgroupOf_eq_of_le hWH]
  have hNsub : N.subgroupOf H = C := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hNH, hNmapH]
  have hNmap : (N.subgroupOf H).map π = V := by
    rw [hNsub]
    dsimp [C]
    rw [FooteLit.map_conjClosure, show (P.subgroupOf H).map π = A from rfl, hWmap, hconj]
  have hWnormal : W ≤ N ⊔ (W ⊓ FooteLit.oddCoreIn H) := by
    intro w hw
    have hwH : w ∈ H := hWH hw
    let wH : H := ⟨w, hwH⟩
    have hwV : π wH ∈ V := by
      rw [← hWmap]
      exact Subgroup.mem_map.mpr ⟨wH, Subgroup.mem_subgroupOf.mpr hw, rfl⟩
    have hwN : π wH ∈ (N.subgroupOf H).map π := by
      rwa [hNmap]
    obtain ⟨nH, hnHN, hnpi⟩ := Subgroup.mem_map.mp hwN
    have hnN : H.subtype nH ∈ N := Subgroup.mem_subgroupOf.mp hnHN
    have hnW : H.subtype nH ∈ W := hNW hnN
    have hwnW : w * (H.subtype nH)⁻¹ ∈ W :=
      W.mul_mem hw (W.inv_mem hnW)
    have hkerH : π (wH * nH⁻¹) = 1 := by
      rw [map_mul, map_inv, hnpi, mul_inv_cancel]
    let rH : H := wH * nH⁻¹
    have hrHker : rH ∈ (QuotientGroup.mk' (pPrimeCore 2 H)).ker := by
      rw [MonoidHom.mem_ker]
      exact hkerH
    have hO : w * (H.subtype nH)⁻¹ ∈ FooteLit.oddCoreIn H := by
      have hrO : rH ∈ pPrimeCore 2 H := by
        rw [← QuotientGroup.ker_mk' (pPrimeCore 2 H)]
        exact hrHker
      have hmem : H.subtype rH ∈ FooteLit.oddCoreIn H :=
        Subgroup.mem_map.mpr ⟨rH, hrO, rfl⟩
      simpa [rH, wH] using hmem
    have hR : w * (H.subtype nH)⁻¹ ∈ W ⊓ FooteLit.oddCoreIn H :=
      ⟨hwnW, hO⟩
    have hw_eq : w = (w * (H.subtype nH)⁻¹) * H.subtype nH := by group
    rw [hw_eq, sup_comm]
    exact Subgroup.mul_mem_sup hR hnN
  have hRodd : Odd (Nat.card ↥(W ⊓ FooteLit.oddCoreIn H)) :=
    (FooteLit.odd_card_oddCoreIn H).of_dvd_nat
      (Subgroup.card_dvd_of_le (show W ⊓ FooteLit.oddCoreIn H ≤ FooteLit.oddCoreIn H from
        inf_le_right))
  exact
    { D := D
      D_map := hDmap
      W0 := W0
      W0_perfect := hW0perf
      W0_map := hW0map
      W0_le_D := hW0leD
      P0_le_W0 := hP0W0
      W := W
      W_eq := rfl
      W_le_H := hWH
      W_le_Cb := hWleCb
      W_perfect := hWperf
      P_le_W := hP_W
      W_map := hWmap
      W_normal_gen := hWnormal
      R_le_W := inf_le_left
      R_odd := hRodd }

noncomputable def relative_W_for_gs_orbit
    {H : Subgroup G} {b : H} (hb : orderOf b = 2)
    {abar bbar : H ⧸ pPrimeCore 2 H} (ha : orderOf abar = 2)
    (hbbar : QuotientGroup.mk' (pPrimeCore 2 H) b = bbar)
    {A K : Subgroup (H ⧸ pPrimeCore 2 H)}
    {T : Type} [Group T] [IsSimpleGroup T] {S : Set (Subgroup G)}
    (hPmarked : Marked S T (canonicalPerfectLift H A))
    (hK : IsComponent (K.subgroupOf
      (Subgroup.centralizer ({bbar} : Set (H ⧸ pPrimeCore 2 H)))))
    (hKc : IsComponent ((conjugate K abar).subgroupOf
      (Subgroup.centralizer ({bbar} : Set (H ⧸ pPrimeCore 2 H)))))
    (hKle : K ≤ Subgroup.centralizer ({bbar} : Set (H ⧸ pPrimeCore 2 H)))
    (hKcle : conjugate K abar ≤
      Subgroup.centralizer ({bbar} : Set (H ⧸ pPrimeCore 2 H)))
    (hAq : IsQuasisimple A)
    (hAcent : A ≤ Subgroup.centralizer ({abar} : Set (H ⧸ pPrimeCore 2 H)))
    (hAK : A ≤ K ⊔ conjugate K abar)
    (hVperf : Group.IsPerfect ↥(K ⊔ conjugate K abar)) :
    RelativePerfectLiftData (K ⊔ conjugate K abar)
      (fixedShadowAt (canonicalPerfectLift H A) (H.subtype b)) b := by
  classical
  let π : H →* (H ⧸ pPrimeCore 2 H) := QuotientGroup.mk' (pPrimeCore 2 H)
  let V : Subgroup (H ⧸ pPrimeCore 2 H) := K ⊔ conjugate K abar
  let P : Subgroup G := fixedShadowAt (canonicalPerfectLift H A) (H.subtype b)
  have hbG2 : orderOf (H.subtype b) = 2 := by
    simpa [Subgroup.orderOf_coe] using hb
  have hPq : IsQuasisimple (canonicalPerfectLift H A ⧸
      pPrimeCore 2 (canonicalPerfectLift H A)) := by
    obtain ⟨eP⟩ := hPmarked.2.1
    exact isQuasisimple_oddCoreQuotient_of_perfect_simple hPmarked.1 eP
  have hPmapCanon : ((canonicalPerfectLift H A).subgroupOf H).map
      (QuotientGroup.mk' (pPrimeCore 2 H)) = A :=
    canonicalPerfectLift_map_quotient hAq.1
  have hbCore : H.subtype b ∈ UnbalancedLayer.coreActionKernel
      (canonicalPerfectLift H A) :=
    canonicalPerfectLift_coreActionKernel hbbar (hAK.trans (sup_le hKle hKcle))
  have hPmap : ((P.subgroupOf H).map
      (QuotientGroup.mk' (pPrimeCore 2 H))) = A :=
    fixedShadowAt_canonical_lift_map_eq hAq hPq hPmapCanon hbG2 hbbar hbCore
  have hPHcanon : canonicalPerfectLift H A ≤ H := by
    dsimp [canonicalPerfectLift]
    exact Subgroup.map_subtype_le _
  have hPH : P ≤ H :=
    (fixedShadowAt_le (canonicalPerfectLift H A) (H.subtype b)).trans hPHcanon
  have hz : ({H.subtype b} : Set G) ⊆ (Subgroup.zpowers (H.subtype b) : Set G) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact Subgroup.mem_zpowers (H.subtype b)
  have hcent_le : Subgroup.centralizer (Subgroup.zpowers (H.subtype b) : Set G) ≤
      Subgroup.centralizer ({H.subtype b} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact hx _ (Subgroup.mem_zpowers (H.subtype b))
  have hPb : P ≤ Subgroup.centralizer ({H.subtype b} : Set G) := by
    rw [show P = fixedShadow (canonicalPerfectLift H A) (Subgroup.zpowers (H.subtype b)) from
      (fixedShadow_zpowers (canonicalPerfectLift H A) (H.subtype b)).symm]
    exact ((fixedShadow_le_inf (canonicalPerfectLift H A)
      (Subgroup.zpowers (H.subtype b))).trans inf_le_right).trans hcent_le
  have hPperf : Group.IsPerfect P := fixedShadowAt_perfect (canonicalPerfectLift H A) (H.subtype b)
  have hVcent : V ≤ Subgroup.centralizer ({π b} : Set (H ⧸ pPrimeCore 2 H)) := by
    dsimp [V]
    rw [show π b = bbar from hbbar]
    exact sup_le hKle hKcle
  have hconjA : FooteLit.conjClosure A V = V := by
    apply conjClosure_eq_of_perfect_le_sup_odd hAK hVperf
    exact relative_normal_generation ha hK hKc hKle hKcle hAq hAcent hAK
  rw [← hPmap] at hconjA
  have hconj : FooteLit.conjClosure ((P.subgroupOf H).map
      (QuotientGroup.mk' (pPrimeCore 2 H))) V = V := hconjA
  exact exists_relative_perfect_lift_normal_generation hb hVperf hVcent hPH hPb hPperf hconj

theorem relative_identity_of_localB
    {H : Subgroup G} {S : Set (Subgroup G)} {T : Type} [Group T] [IsSimpleGroup T]
    (hFam : IsomorphicFamily S T)
    (hB : CFSG.Assembly.ComponentType.LocalBProperty (H ⧸ pPrimeCore 2 H))
    {abar bbar : H ⧸ pPrimeCore 2 H}
    {A K : Subgroup (H ⧸ pPrimeCore 2 H)}
    (hCorr : GrSLit.GSWeakCorr abar A bbar K)
    (hMarked : Marked S T (canonicalPerfectLift H A)) :
    K = A ∧ conjugate K abar = A := by
  classical
  have hCorr' : GrSLit.GSWeakCorr abar A bbar K := hCorr
  obtain ⟨ha, hb, hab, hAa, hApc, hKb, hKpc, hbNA, hcommA, hshadow⟩ := hCorr
  let π : H →* (H ⧸ pPrimeCore 2 H) := QuotientGroup.mk' (pPrimeCore 2 H)
  let Ca : Subgroup (H ⧸ pPrimeCore 2 H) := Subgroup.centralizer ({abar} : Set _)
  let Cb : Subgroup (H ⧸ pPrimeCore 2 H) := Subgroup.centralizer ({bbar} : Set _)
  let V : Subgroup (H ⧸ pPrimeCore 2 H) := K ⊔ conjugate K abar
  have hAq : IsQuasisimple A :=
    isQuasisimple_of_localB_component hB ha hAa hApc
  have hAcomp : IsComponent (A.subgroupOf Ca) :=
    isComponent_subgroupOf_of_localB_component hB ha hAa hApc
  have hKcomp : IsComponent (K.subgroupOf Cb) :=
    isComponent_subgroupOf_of_localB_component hB hb hKb hKpc
  have hAb : A ≤ Cb := gsWeakCorr_source_le_centralizer hCorr' hAq
  have hfix : UnbalancedGS.gsFixedLayer A bbar = A :=
    gsFixedLayer_eq_self_of_isQuasisimple hAb hAq
  have hAK : A ≤ V := by
    dsimp [V]
    rw [← hfix]
    exact hshadow
  have habarCb : abar ∈ Cb := by
    dsimp [Cb]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hab
  let u : Cb := ⟨abar, habarCb⟩
  have hKccomp : IsComponent ((conjugate K abar).subgroupOf Cb) := by
    have h := isComponent_conjugate hKcomp u
    rw [CFSG.GroupTheory.conjugate_subgroupOf] at h
    simpa [u] using h
  have hKcle : conjugate K abar ≤ Cb :=
    CFSG.GroupTheory.conjugate_le_of_mem hKb habarCb
  haveI : Group.IsPerfect (K.subgroupOf Cb) := hKcomp.1.1
  haveI : Group.IsPerfect ((conjugate K abar).subgroupOf Cb) := hKccomp.1.1
  have hKperf : Group.IsPerfect K :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hKb).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKb).surjective
  have hKcperf : Group.IsPerfect (conjugate K abar) :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hKcle).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKcle).surjective
  haveI : Group.IsPerfect K := hKperf
  haveI : Group.IsPerfect (conjugate K abar) := hKcperf
  have hVperf : Group.IsPerfect V := by
    dsimp [V]
    exact CFSG.ComponentClassification.GSThmB.B5a.isPerfect_sup
  have hleV : V ≤ FooteLit.conjClosure A V ⊔ FooteLit.oddCoreIn V := by
    simpa [V] using
      (relative_normal_generation ha hKcomp hKccomp hKb hKcle hAq hAa hAK)
  have hconjV : FooteLit.conjClosure A V = V :=
    conjClosure_eq_of_perfect_le_sup_odd hAK hVperf hleV
  have hπsurj : Function.Surjective π := by
    dsimp [π]
    exact QuotientGroup.mk'_surjective (pPrimeCore 2 H)
  have hker : π.ker = CFSG.pPrimeCore 2 H := by
    simpa [π] using QuotientGroup.ker_mk' (CFSG.pPrimeCore 2 H)
  have hoddker : Odd (Nat.card π.ker) := by
    rw [hker]
    exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := H))
  obtain ⟨a, b, ha2, hb2, hcommab, haeq, hbeq⟩ :=
    exists_commuting_involution_lifts π hπsurj hoddker ha hb hab
  let P : Subgroup G := canonicalPerfectLift H A
  let Pb : Subgroup G := fixedShadowAt P (H.subtype b)
  have hPq : IsQuasisimple (P ⧸ pPrimeCore 2 P) := by
    simpa [P] using hMarked.quotient_quasisimple hFam
  have hPmap : ((P.subgroupOf H).map π) = A := by
    simpa [P, π] using canonicalPerfectLift_map_quotient (H := H) hAq.1
  have hbCore : H.subtype b ∈ UnbalancedLayer.coreActionKernel P :=
    canonicalPerfectLift_coreActionKernel hbeq hAb
  have hbG2 : orderOf (H.subtype b) = 2 := by
    simpa [Subgroup.orderOf_coe] using hb2
  have hPbmap : ((Pb.subgroupOf H).map π) = A :=
    fixedShadowAt_canonical_lift_map_eq hAq hPq hPmap hbG2 hbeq hbCore
  have hPH : P ≤ H := by
    dsimp [P, canonicalPerfectLift]
    exact Subgroup.map_subtype_le _
  have hPbH : Pb ≤ H := (fixedShadowAt_le P (H.subtype b)).trans hPH
  have hPbC : Pb ≤ Subgroup.centralizer ({H.subtype b} : Set G) := by
    have hz : ({H.subtype b} : Set G) ⊆ (Subgroup.zpowers (H.subtype b) : Set G) := by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact Subgroup.mem_zpowers (H.subtype b)
    have hcent : Subgroup.centralizer (Subgroup.zpowers (H.subtype b) : Set G) ≤
        Subgroup.centralizer ({H.subtype b} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact hx _ (Subgroup.mem_zpowers (H.subtype b))
    have h := ((fixedShadow_le_inf P (Subgroup.zpowers (H.subtype b))).trans inf_le_right).trans hcent
    simpa [Pb, fixedShadow_zpowers] using h
  have hPbperf : Group.IsPerfect Pb := fixedShadowAt_perfect P (H.subtype b)
  obtain ⟨D, hDmap, W0, hW0perf, hW0map, hW0leD, hP0W0,
    W, hWeq, hWH, hWCb, hWperf, hPbW, hWmap, hWnormal, hRleW, hRodd⟩ :=
    relative_W_for_gs_orbit hb2 ha hbeq hMarked hKcomp hKccomp hKb hKcle
      hAq hAa hAK hVperf
  let U : Subgroup G := Subgroup.zpowers (H.subtype b)
  have hU : IsPGroup 2 U := isPGroup_zpowers_of_orderOf_eq_two hbG2
  have hUK : U ≤ UnbalancedLayer.coreActionKernel P :=
    Subgroup.zpowers_le.mpr hbCore
  have hU0 : U ≠ ⊥ := by
    intro hbot
    have hb1 : H.subtype b = 1 := (Subgroup.zpowers_eq_bot).mp hbot
    have htwo : (2 : ℕ) = 1 := by
      rw [← hbG2, hb1, orderOf_one]
    omega
  have hST : MarkedST S T := markedST_of_isomorphicFamily hFam
  obtain ⟨J, hJC, hJmarked, hconjJ, hcoverJ⟩ := hST P hMarked U hU hUK hU0
  let C : Subgroup G := Subgroup.centralizer ({H.subtype b} : Set G)
  have hCeq : Subgroup.centralizer (U : Set G) = C := by
    dsimp [U, C]
    exact UnbalancedLayer.centralizer_zpowers_eq (H.subtype b)
  have hJCb : FooteLit.IsTwoComponentIn J C := by
    simpa [C, hCeq] using hJC
  have hcoverJb : Pb ⊔ FooteLit.oddCoreIn J = J := by
    simpa [Pb, P, U, fixedShadow_zpowers] using hcoverJ
  have hOJleC : FooteLit.oddCoreIn J ≤ C :=
    (show FooteLit.oddCoreIn J ≤ J from Subgroup.map_subtype_le _).trans hJCb.1
  have hOJmapBot : ((FooteLit.oddCoreIn J).subgroupOf C).map
      (QuotientGroup.mk' (pPrimeCore 2 C)) = ⊥ :=
    map_oddCoreIn_subgroupOf_eq_bot hJCb
  let πC : C →* (C ⧸ pPrimeCore 2 C) := QuotientGroup.mk' (pPrimeCore 2 C)
  have hcoverSub : J.subgroupOf C =
      (Pb.subgroupOf C) ⊔ ((FooteLit.oddCoreIn J).subgroupOf C) := by
    calc
      J.subgroupOf C = (Pb ⊔ FooteLit.oddCoreIn J).subgroupOf C :=
        congrArg (fun X : Subgroup G => X.subgroupOf C) hcoverJb.symm
      _ = (Pb.subgroupOf C) ⊔ ((FooteLit.oddCoreIn J).subgroupOf C) :=
        Subgroup.subgroupOf_sup hPbC hOJleC
  have hImgEq : (Pb.subgroupOf C).map πC = (J.subgroupOf C).map πC := by
    have hJmap : (J.subgroupOf C).map πC = (Pb.subgroupOf C).map πC := by
      rw [hcoverSub, Subgroup.map_sup, hOJmapBot, sup_bot_eq]
    exact hJmap.symm
  obtain ⟨eJ⟩ := hJmarked.2.1
  have hJimg := quotient_image_isComponent_of_isTwoComponentIn hJCb eJ
  have hX : IsComponent ((Pb.subgroupOf C).map πC) := by
    rw [hImgEq]
    exact hJimg.1
  have hXsimple : IsSimpleGroup ((Pb.subgroupOf C).map πC) := by
    rw [hImgEq]
    exact hJimg.2
  obtain ⟨hWcover, hWoddC, hWsupC⟩ :=
    eq_sup_oddCoreIn_of_simple_oddCoreImage hPbC hWCb hPbW hWperf hRleW hRodd
      hWnormal hX hXsimple
  let N : Subgroup (H ⧸ pPrimeCore 2 H) :=
    ((FooteLit.oddCoreIn W).subgroupOf H).map π
  have hOWleH : FooteLit.oddCoreIn W ≤ H :=
    (show FooteLit.oddCoreIn W ≤ W from Subgroup.map_subtype_le _).trans hWH
  have hWsubEq : W.subgroupOf H =
      (Pb.subgroupOf H) ⊔ (FooteLit.oddCoreIn W).subgroupOf H := by
    calc
      W.subgroupOf H = (Pb ⊔ FooteLit.oddCoreIn W).subgroupOf H :=
        congrArg (fun X : Subgroup G => X.subgroupOf H) hWcover
      _ = (Pb.subgroupOf H) ⊔ (FooteLit.oddCoreIn W).subgroupOf H :=
        Subgroup.subgroupOf_sup hPbH hOWleH
  have hWN : V = A ⊔ N := by
    change K ⊔ conjugate K abar = A ⊔ N
    rw [← hWmap, hWsubEq, Subgroup.map_sup, hPbmap]
  have hNleV : N ≤ V := by
    rw [hWN]
    exact le_sup_right
  have hNodd : Odd (Nat.card N) := by
    have hOodd : Odd (Nat.card (FooteLit.oddCoreIn W)) := FooteLit.odd_card_oddCoreIn W
    refine hOodd.of_dvd_nat ?_
    refine (Subgroup.card_map_dvd _ π).trans ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOWleH).toEquiv]
  let πH : W →* H := Subgroup.inclusion hWH
  let πW : W →* V := (π.comp πH).codRestrict V (fun w => by
    dsimp [πH, V]
    change π ((inclusion hWH) w) ∈ K ⊔ conjugate K abar
    rw [← hWmap]
    exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hWH w, by
      rw [Subgroup.mem_subgroupOf]
      exact w.property, rfl⟩)
  have hπWsurj : Function.Surjective πW := by
    intro v
    have hv : (v : H ⧸ pPrimeCore 2 H) ∈ (W.subgroupOf H).map π := by
      rw [hWmap]
      exact v.property
    obtain ⟨wH, hwH, hwpi⟩ := Subgroup.mem_map.mp hv
    refine ⟨⟨H.subtype wH, ?_⟩, ?_⟩
    · exact Subgroup.mem_subgroupOf.mp hwH
    · ext
      simpa [πW, πH, Subgroup.inclusion] using hwpi
  have hOWnormalW : ((FooteLit.oddCoreIn W).subgroupOf W).Normal :=
    CFSG.ComponentClassification.GSThmB.B5a.oddCoreIn_subgroupOf_normal W
  have hImgNormalV : (((FooteLit.oddCoreIn W).subgroupOf W).map πW).Normal :=
    hOWnormalW.map πW hπWsurj
  have hImgEqN : (((FooteLit.oddCoreIn W).subgroupOf W).map πW) = N.subgroupOf V := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      have hwO : (w : G) ∈ FooteLit.oddCoreIn W := Subgroup.mem_subgroupOf.mp hw
      exact Subgroup.mem_map.mpr ⟨⟨w, hWH w.property⟩, by
        rw [Subgroup.mem_subgroupOf]
        exact hwO, rfl⟩
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨oH, hoH, hoHpi⟩ := Subgroup.mem_map.mp hx
      have hoOW : H.subtype oH ∈ FooteLit.oddCoreIn W := Subgroup.mem_subgroupOf.mp hoH
      have hoW : H.subtype oH ∈ W :=
        (show FooteLit.oddCoreIn W ≤ W from Subgroup.map_subtype_le _) hoOW
      refine ⟨⟨H.subtype oH, hoW⟩, ?_, ?_⟩
      · change (H.subtype oH) ∈ FooteLit.oddCoreIn W
        exact hoOW
      · ext
        simpa [πW, πH, Subgroup.inclusion] using hoHpi
  have hNnormal : (N.subgroupOf V).Normal := by
    rw [← hImgEqN]
    exact hImgNormalV
  have hKA : K = A :=
    eq_of_relative_cover (Wbar := V) hKcomp hKccomp hKb hKcle hAq hAa rfl
      hAK hVperf hNleV hNnormal hNodd hWN
  refine ⟨hKA, ?_⟩
  rw [hKA]
  exact UnbalancedCorr.conjugate_eq_self_of_le_centralizer hAa

theorem proper_section_isKGroupCat_and_B
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Blueprint.Catalog)
    (hU : CFSG.ComponentClassification.CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hheld : CFSG.ComponentClassification.KProperRelativeB.HeldInput)
    {G : Type} [Group G] [Finite G]
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {H : Subgroup G} (hH : H ≠ ⊤) :
    SectionRank.IsKGroupCat (H ⧸ pPrimeCore 2 H) ∧
      CFSG.ComponentClassification.ProperSectionB.KGroupBConclusion (H ⧸ pPrimeCore 2 H) :=
  CFSG.ComponentClassification.ProperSectionB.kProper_section_B_conclusion_of_inputs
    hS hU hheld hK hH (pPrimeCore 2 H) (MulEquiv.refl (H ⧸ pPrimeCore 2 H))

theorem relative_localB_of_proper_H
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Blueprint.Catalog)
    (hU : CFSG.ComponentClassification.CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hheld : CFSG.ComponentClassification.KProperRelativeB.HeldInput)
    {G : Type} [Group G] [Finite G]
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {H : Subgroup G} (hH : H ≠ ⊤) :
    SectionRank.IsKGroupCat (H ⧸ pPrimeCore 2 H) ∧
      CFSG.ComponentClassification.ProperSectionB.KGroupBConclusion (H ⧸ pPrimeCore 2 H) ∧
      CFSG.Assembly.ComponentType.LocalBProperty (H ⧸ pPrimeCore 2 H) := by
  obtain ⟨hYK, hconcl⟩ :=
    proper_section_isKGroupCat_and_B hS hU hheld hK hH
  have hcore : CFSG.Assembly.oddCore (H ⧸ pPrimeCore 2 H) = ⊥ := by
    have hO : CFSG.Open.componentClassificationOddCore H = CFSG.pPrimeCore 2 H := by
      rw [show CFSG.Open.componentClassificationOddCore H = CFSG.Assembly.oddCore H from rfl,
        CFSG.Assembly.Dichotomy.oddCore_eq_pPrimeCore]
    let e : (H ⧸ CFSG.Open.componentClassificationOddCore H) ≃*
        (H ⧸ CFSG.pPrimeCore 2 H) :=
      QuotientGroup.quotientMulEquivOfEq hO
    have hq : CFSG.oddCore (H ⧸ CFSG.Open.componentClassificationOddCore H) = ⊥ :=
      CFSG.ComponentClassification.OddCore.quotient_corefree H
    have hq' : CFSG.oddCore (H ⧸ CFSG.pPrimeCore 2 H) = ⊥ :=
      CFSG.QuasiDihedralFusion.oddCore_eq_bot_of_mulEquiv e hq
    exact hq'
  exact ⟨hYK, hconcl, (hconcl.2.1 hcore).2⟩

theorem relative_identity_of_localB_proper_H
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Blueprint.Catalog)
    (hU : CFSG.ComponentClassification.CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hheld : CFSG.ComponentClassification.KProperRelativeB.HeldInput)
    {G : Type} [Group G] [Finite G]
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {H : Subgroup G} (hH : H ≠ ⊤)
    {S : Set (Subgroup G)} {T : Type} [Group T] [IsSimpleGroup T]
    (hFam : IsomorphicFamily S T)
    {abar bbar : H ⧸ pPrimeCore 2 H}
    {A K : Subgroup (H ⧸ pPrimeCore 2 H)}
    (hCorr : GrSLit.GSWeakCorr abar A bbar K)
    (hMarked : Marked S T (canonicalPerfectLift H A)) :
    K = A ∧ conjugate K abar = A := by
  obtain ⟨-, -, hB⟩ := relative_localB_of_proper_H hS hU hheld hK hH
  exact relative_identity_of_localB hFam hB hCorr hMarked

private noncomputable def relativeLiftA (M H : Subgroup G) (a : G) :
    Subgroup (H ⧸ pPrimeCore 2 H) :=
  ((fixedShadowAt M a).subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H))

private theorem relativeLiftA_le_centralizer
    {S : Set (Subgroup G)} {T : Type} [Group T] [IsSimpleGroup T]
    {M H : Subgroup G} {a : G} (_hM : Marked S T M) (hMH : M ≤ H)
    (ha : orderOf a = 2) (haH : a ∈ H) :
    relativeLiftA M H a ≤
      centralizer ({QuotientGroup.mk' (pPrimeCore 2 H) ⟨a, haH⟩} :
        Set (H ⧸ pPrimeCore 2 H)) := by
  let pi : H →* (H ⧸ pPrimeCore 2 H) := QuotientGroup.mk' (pPrimeCore 2 H)
  let aH : H := ⟨a, haH⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hyMa : ((y : H) : G) ∈ fixedShadow M (Subgroup.zpowers a) := by
    change ((y : H) : G) ∈ fixedShadowAt M a at hy
    rwa [← fixedShadow_zpowers] at hy
  have hyC : ((y : H) : G) ∈ centralizer ({a} : Set G) := by
    have h := (fixedShadow_le_inf M (Subgroup.zpowers a)) hyMa
    simpa [UnbalancedLayer.centralizer_zpowers_eq] using h.2
  have hycomm : (y : H) * aH = aH * y := by
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp hyC
  calc
    pi y * pi aH = pi (y * aH) := by rw [map_mul]
    _ = pi (aH * y) := by rw [hycomm]
    _ = pi aH * pi y := by rw [map_mul]

private theorem relativeLift_abar_order
    {H : Subgroup G} {a : G} (ha : orderOf a = 2) (haH : a ∈ H) :
    orderOf (QuotientGroup.mk' (pPrimeCore 2 H) ⟨a, haH⟩) = 2 := by
  have haH2 : orderOf (⟨a, haH⟩ : H) = 2 :=
    (Subgroup.orderOf_coe _).symm.trans ha
  have hodd : Odd (Nat.card (QuotientGroup.mk' (pPrimeCore 2 H)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact Nat.coprime_two_left.mp
      (CFSG.pPrimeCore_coprime_card (p := 2) (G := H))
  simpa using
    CFSG.OrderReductions.OddKernelInvolutions.involution_image_order
      (QuotientGroup.mk' (pPrimeCore 2 H)) hodd ⟨⟨a, haH⟩, haH2⟩

private noncomputable def relC (a : G) : Subgroup G :=
  centralizer ({a} : Set G)

private noncomputable def relCH (H : Subgroup G) (a : G) (haH : a ∈ H) : Subgroup H :=
  centralizer ({⟨a, haH⟩} : Set H)

private noncomputable def relIncl (H : Subgroup G) (a : G) (haH : a ∈ H) :
    relCH H a haH →* relC a :=
  (H.subtype.comp (relCH H a haH).subtype).codRestrict (relC a) (fun x => by
    change (H.subtype ((relCH H a haH).subtype x)) ∈ centralizer ({a} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx : (x : H) * ⟨a, haH⟩ = ⟨a, haH⟩ * x :=
      Subgroup.mem_centralizer_singleton_iff.mp x.property
    exact congrArg H.subtype hx)

private noncomputable def relF (H : Subgroup G) (a : G) (haH : a ∈ H) :
    relCH H a haH →* (relC a ⧸ pPrimeCore 2 (relC a)) :=
  (QuotientGroup.mk' (pPrimeCore 2 (relC a))).comp (relIncl H a haH)

private noncomputable def relK (a : G) (Sa : Subgroup G) :
    Subgroup (relC a ⧸ pPrimeCore 2 (relC a)) :=
  (Sa.subgroupOf (relC a)).map (QuotientGroup.mk' (pPrimeCore 2 (relC a)))

private noncomputable def relI (H : Subgroup G) (a : G) (haH : a ∈ H)
    (Sa : Subgroup G) : Subgroup (relCH H a haH) :=
  (relK a Sa).comap (relF H a haH)

private noncomputable def relJ0 (H : Subgroup G) (a : G) (haH : a ∈ H)
    (Sa : Subgroup G) : Subgroup (relCH H a haH) :=
  (CFSG.perfectResidual (relI H a haH Sa)).map (relI H a haH Sa).subtype

private noncomputable def relMaH (M H : Subgroup G) (a : G) : Subgroup H :=
  (fixedShadowAt M a).subgroupOf H

private noncomputable def relMaCH (M H : Subgroup G) (a : G) (haH : a ∈ H) :
    Subgroup (relCH H a haH) :=
  (relMaH M H a).subgroupOf (relCH H a haH)

private lemma relMaCH_map_relF_eq_relK
    {S : Set (Subgroup G)} {T : Type} [Group T] [IsSimpleGroup T]
    {M H : Subgroup G} (hMH : M ≤ H) {a : G} (haH : a ∈ H)
    {Sa : Subgroup G} (hSaAt : IsTwoComponentAt a Sa)
    (himage : fixedShadowAt M a ⊔ FooteLit.oddCoreOfCentralizer a =
      Sa ⊔ FooteLit.oddCoreOfCentralizer a) :
    (relMaCH M H a haH).map (relF H a haH) = relK a Sa := by
  let C : Subgroup G := relC a
  let MaC : Subgroup C := (fixedShadowAt M a).subgroupOf C
  let SaC : Subgroup C := Sa.subgroupOf C
  have hMaC : fixedShadowAt M a ≤ C := by
    intro x hx
    have hx' : x ∈ fixedShadow M (Subgroup.zpowers a) := by
      rwa [← fixedShadow_zpowers] at hx
    have hxcent := ((fixedShadow_le_inf M (Subgroup.zpowers a)) hx').2
    simpa [C, relC, UnbalancedLayer.centralizer_zpowers_eq] using hxcent
  have hSaC : Sa ≤ C := hSaAt.2.1
  have himageC : MaC ⊔ pPrimeCore 2 C = SaC ⊔ pPrimeCore 2 C := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hMaC,
      Subgroup.map_subgroupOf_eq_of_le hSaC]
    change fixedShadowAt M a ⊔ FooteLit.oddCoreOfCentralizer a =
      Sa ⊔ FooteLit.oddCoreOfCentralizer a
    exact himage
  have hmapEq : MaC.map (QuotientGroup.mk' (pPrimeCore 2 C)) =
      SaC.map (QuotientGroup.mk' (pPrimeCore 2 C)) := by
    have h := congrArg (fun X : Subgroup C =>
      X.map (QuotientGroup.mk' (pPrimeCore 2 C))) himageC
    have hcore : (pPrimeCore 2 C).map (QuotientGroup.mk' (pPrimeCore 2 C)) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    simpa [Subgroup.map_sup, hcore] using h
  have hmapMaC : (relMaCH M H a haH).map (relIncl H a haH) = MaC := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      simpa [relIncl, relMaCH, relMaH, MaC, Subgroup.mem_subgroupOf] using hy
    · intro x hx
      have hxMa : ((x : C) : G) ∈ fixedShadowAt M a := by
        simpa [MaC, Subgroup.mem_subgroupOf] using hx
      have hxH : ((x : C) : G) ∈ H := (fixedShadowAt_le M a).trans hMH hxMa
      let hH : H := ⟨((x : C) : G), hxH⟩
      have hhHMa : hH ∈ relMaH M H a := by
        change (hH : G) ∈ fixedShadowAt M a
        exact hxMa
      have hhHCH : hH ∈ relCH H a haH := by
        change hH ∈ centralizer ({⟨a, haH⟩} : Set H)
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        exact Subgroup.mem_centralizer_singleton_iff.mp x.property
      let y : relCH H a haH := ⟨hH, hhHCH⟩
      have hyMaCH : y ∈ relMaCH M H a haH := by
        rw [relMaCH, Subgroup.mem_subgroupOf]
        exact hhHMa
      refine Subgroup.mem_map.mpr ⟨y, hyMaCH, ?_⟩
      apply Subtype.ext
      rfl
  calc
    (relMaCH M H a haH).map (relF H a haH)
        = ((relMaCH M H a haH).map (relIncl H a haH)).map
            (QuotientGroup.mk' (pPrimeCore 2 C)) := by
          rw [relF, Subgroup.map_map]
    _ = MaC.map (QuotientGroup.mk' (pPrimeCore 2 C)) := by rw [hmapMaC]
    _ = relK a Sa := hmapEq.trans rfl

private lemma relMaH_le_relCH {M H : Subgroup G} (hMH : M ≤ H) {a : G} (haH : a ∈ H) :
    relMaH M H a ≤ relCH H a haH := by
  intro x hx
  change x ∈ centralizer ({⟨a, haH⟩} : Set H)
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  change (x : G) * a = a * x
  have hx' : (x : G) ∈ fixedShadow M (Subgroup.zpowers a) := by
    change (x : G) ∈ fixedShadowAt M a at hx
    rwa [← fixedShadow_zpowers] at hx
  have hxcent := ((fixedShadow_le_inf M (Subgroup.zpowers a)) hx').2
  have hxcent' : (x : G) ∈ centralizer ({a} : Set G) := by
    simpa [UnbalancedLayer.centralizer_zpowers_eq] using hxcent
  exact Subgroup.mem_centralizer_singleton_iff.mp hxcent'

private noncomputable def relMaCH_equiv_shadow {M H : Subgroup G} (hMH : M ≤ H)
    {a : G} (haH : a ∈ H) :
    relMaCH M H a haH ≃* fixedShadowAt M a :=
  (Subgroup.subgroupOfEquivOfLe (relMaH_le_relCH hMH haH)).trans
    (Subgroup.subgroupOfEquivOfLe (show fixedShadowAt M a ≤ H from
      (fixedShadowAt_le M a).trans hMH))

private lemma relMaCH_perfect {M H : Subgroup G} (hMH : M ≤ H) {a : G} (haH : a ∈ H) :
    Group.IsPerfect (relMaCH M H a haH) := by
  let eMaCH := relMaCH_equiv_shadow hMH haH
  haveI : Group.IsPerfect (fixedShadowAt M a) := fixedShadowAt_perfect M a
  refine Group.IsPerfect.ofSurjective (f := eMaCH.symm.toMonoidHom) ?_
  intro y
  exact ⟨eMaCH y, eMaCH.symm_apply_apply y⟩

private lemma relMaCH_le_relI {M H : Subgroup G} {a : G} (haH : a ∈ H)
    {Sa : Subgroup G}
    (hMa_image : (relMaCH M H a haH).map (relF H a haH) = relK a Sa) :
    relMaCH M H a haH ≤ relI H a haH Sa := by
  intro x hx
  rw [relI, Subgroup.mem_comap]
  rw [← hMa_image]
  exact Subgroup.mem_map_of_mem (relF H a haH) hx

private lemma relI_subnormal {H : Subgroup G} {a : G} (haH : a ∈ H)
    {Sa : Subgroup G} (hKcomp : IsComponent (relK a Sa)) :
    (relI H a haH Sa).IsSubnormal := by
  have h := Subgroup.IsSubnormal.comap (relF H a haH) hKcomp.2
  simpa [relI] using h

private lemma relJ0_perfect {H : Subgroup G} {a : G} (haH : a ∈ H)
    {Sa : Subgroup G} : Group.IsPerfect (relJ0 H a haH Sa) := by
  let I : Subgroup (relCH H a haH) := relI H a haH Sa
  let R := CFSG.perfectResidual I
  let e : R ≃* relJ0 H a haH Sa :=
    R.equivMapOfInjective I.subtype I.subtype_injective
  haveI : Group.IsPerfect R :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_isPerfect
  refine Group.IsPerfect.ofSurjective (f := e.toMonoidHom) ?_
  intro y
  exact ⟨e.symm y, e.apply_symm_apply y⟩

private lemma relJ0_subnormal {H : Subgroup G} {a : G} (haH : a ∈ H)
    {Sa : Subgroup G} (hKcomp : IsComponent (relK a Sa)) :
    (relJ0 H a haH Sa).IsSubnormal := by
  let I : Subgroup (relCH H a haH) := relI H a haH Sa
  have hRsub : (CFSG.perfectResidual I).IsSubnormal :=
    Subgroup.Normal.isSubnormal (inferInstance : (CFSG.perfectResidual I).Normal)
  have hIsub : I.IsSubnormal := relI_subnormal haH hKcomp
  exact Subgroup.IsSubnormal.trans' hRsub hIsub

private lemma relMaCH_le_relJ0 {M H : Subgroup G} (hMH : M ≤ H) {a : G} (haH : a ∈ H)
    {Sa : Subgroup G}
    (hMa_image : (relMaCH M H a haH).map (relF H a haH) = relK a Sa) :
    relMaCH M H a haH ≤ relJ0 H a haH Sa :=
  CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf
    (relMaCH M H a haH) (relI H a haH Sa)
    (relMaCH_perfect hMH haH) (relMaCH_le_relI haH hMa_image)

private lemma relI_map_relF_eq_relK {H : Subgroup G} {a : G} (haH : a ∈ H)
    {M : Subgroup G} (hMH : M ≤ H) {Sa : Subgroup G}
    (hMa_image : (relMaCH M H a haH).map (relF H a haH) = relK a Sa) :
    (relI H a haH Sa).map (relF H a haH) = relK a Sa := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact Subgroup.mem_comap.mp hy
  · rw [← hMa_image]
    exact Subgroup.map_mono (relMaCH_le_relI haH hMa_image)

private lemma relJ0_map_relF_eq_relK {H : Subgroup G} {a : G} (haH : a ∈ H)
    {M : Subgroup G} (hMH : M ≤ H) {Sa : Subgroup G}
    (hMa_image : (relMaCH M H a haH).map (relF H a haH) = relK a Sa) :
    (relJ0 H a haH Sa).map (relF H a haH) = relK a Sa := by
  apply le_antisymm
  · calc
      (relJ0 H a haH Sa).map (relF H a haH)
          ≤ (relI H a haH Sa).map (relF H a haH) := by
            refine Subgroup.map_mono ?_
            rw [relJ0]
            exact Subgroup.map_subtype_le _
      _ = relK a Sa := relI_map_relF_eq_relK haH hMH hMa_image
  · rw [← hMa_image]
    exact Subgroup.map_mono (relMaCH_le_relJ0 hMH haH hMa_image)

private lemma relIncl_injective (H : Subgroup G) (a : G) (haH : a ∈ H) :
    Function.Injective (relIncl H a haH) := by
  intro x y hxy
  apply (relCH H a haH).subtype_injective
  apply H.subtype_injective
  simpa [relIncl] using congrArg Subtype.val hxy

private lemma relF_ker_odd (H : Subgroup G) (a : G) (haH : a ∈ H) :
    Odd (Nat.card (relF H a haH).ker) := by
  let e := (relF H a haH).ker.equivMapOfInjective (relIncl H a haH)
    (relIncl_injective H a haH)
  have hcard : Nat.card (relF H a haH).ker =
      Nat.card ((relF H a haH).ker.map (relIncl H a haH)) :=
    Nat.card_congr e.toEquiv
  have hle : (relF H a haH).ker.map (relIncl H a haH) ≤ pPrimeCore 2 (relC a) := by
    rintro _ ⟨x, hx, rfl⟩
    change (QuotientGroup.mk' (pPrimeCore 2 (relC a))) (relIncl H a haH x) = 1 at hx
    exact (QuotientGroup.eq_one_iff _).mp hx
  have hoddO : Odd (Nat.card (pPrimeCore 2 (relC a))) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := relC a))
  rw [hcard]
  exact hoddO.of_dvd_nat (Subgroup.card_dvd_of_le hle)

private noncomputable def relJ0_quotient_equiv_target {T : Type} [Group T]
    {H : Subgroup G} {a : G} (haH : a ∈ H)
    {Sa : Subgroup G} (hKcomp : IsComponent (relK a Sa))
    (hKsimple : IsSimpleGroup (relK a Sa))
    (eK : relK a Sa ≃* T)
    (hJ0map : (relJ0 H a haH Sa).map (relF H a haH) = relK a Sa) :
    (relJ0 H a haH Sa) ⧸ pPrimeCore 2 (relJ0 H a haH Sa) ≃* T := by
  let f := relF H a haH
  let J0 := relJ0 H a haH Sa
  have hoddF : Odd (Nat.card f.ker) := relF_ker_odd H a haH
  have hkerF : ¬ 2 ∣ Nat.card f.ker := by
    intro h2
    exact (Nat.not_even_iff_odd.mpr hoddF) (even_iff_two_dvd.mpr h2)
  have hker : ¬ 2 ∣ Nat.card (f.domRestrict J0).ker :=
    CFSG.ComponentClassification.GSThmB.OddQuot.not_two_dvd_card_ker_domRestrict
      f hkerF J0
  let e1 := Classical.choose
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.exists_restrict_core_quotient_equiv
      f J0 hker)
  haveI : IsSimpleGroup (relK a Sa) := hKsimple
  haveI : Group.IsPerfect (relK a Sa) := hKcomp.1.1
  have hKnonab : ∃ x y : relK a Sa, x * y ≠ y * x := by
    by_contra h
    push Not at h
    haveI : IsMulCommutative (relK a Sa) := ⟨⟨fun x y => h x y⟩⟩
    exact Group.IsPerfect.not_isMulCommutative (G := relK a Sa) inferInstance
  have hOK : pPrimeCore 2 (relK a Sa) = ⊥ :=
    CFSG.Walter.pPrimeCore_eq_bot_of_isSimpleGroup hKnonab
  let eSub : (J0.map f) ≃* relK a Sa := MulEquiv.subgroupCongr hJ0map
  have hcoreSub : (pPrimeCore 2 (relK a Sa)).map eSub.symm =
      pPrimeCore 2 (J0.map f) :=
    CFSG.pPrimeCore_map_iso 2 eSub.symm
  let e2 : (J0.map f ⧸ pPrimeCore 2 (J0.map f)) ≃*
      (relK a Sa ⧸ pPrimeCore 2 (relK a Sa)) :=
    (QuotientGroup.congr (pPrimeCore 2 (relK a Sa))
      (pPrimeCore 2 (J0.map f)) eSub.symm hcoreSub).symm
  let eKq : (relK a Sa ⧸ pPrimeCore 2 (relK a Sa)) ≃* T :=
    (QuotientGroup.quotientMulEquivOfEq hOK).trans
      ((QuotientGroup.quotientBot (G := relK a Sa)).trans eK)
  exact (e1.trans e2).trans eKq

private lemma relJ0_isPComponent {T : Type} [Group T] [IsSimpleGroup T]
    {H : Subgroup G} {a : G} (haH : a ∈ H)
    {Sa : Subgroup G} (hKcomp : IsComponent (relK a Sa))
    (hKsimple : IsSimpleGroup (relK a Sa))
    (eK : relK a Sa ≃* T)
    (hJ0map : (relJ0 H a haH Sa).map (relF H a haH) = relK a Sa) :
    IsPComponent 2 (relJ0 H a haH Sa) := by
  have eJ0T := relJ0_quotient_equiv_target (T := T) haH hKcomp hKsimple eK hJ0map
  have hq : IsQuasisimple
      ((relJ0 H a haH Sa) ⧸ pPrimeCore 2 (relJ0 H a haH Sa)) :=
    isQuasisimple_oddCoreQuotient_of_perfect_simple
      (relJ0_perfect haH) eJ0T
  have htwo : CFSG.ComponentClassification.HarrisLit.IsTwoComponent
      (relJ0 H a haH Sa) :=
    ⟨relJ0_subnormal haH hKcomp, relJ0_perfect haH, hq⟩
  exact (CFSG.ComponentClassification.HarrisLit.isTwoComponent_iff_isPComponent
    (relJ0 H a haH Sa)).mp htwo

private noncomputable def relMa_quot_equiv_target {S : Set (Subgroup G)} {T : Type} [Group T] [IsSimpleGroup T]
    {M : Subgroup G} {a : G} (hM : Marked S T M)
    (ha : orderOf a = 2) (haQ : a ∈ UnbalancedLayer.coreActionKernel M) :
    fixedShadowAt M a ⧸ pPrimeCore 2 (fixedShadowAt M a) ≃* T := by
  let eM := Classical.choice hM.2.1
  have hMq : IsQuasisimple (M ⧸ pPrimeCore 2 M) :=
    isQuasisimple_oddCoreQuotient_of_perfect_simple hM.1 eM
  let U : Subgroup G := Subgroup.zpowers a
  have hU : IsPGroup 2 U :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  have hUK : U ≤ UnbalancedLayer.coreActionKernel M := zpowers_le.mpr haQ
  have hcover :=
    CFSG.ComponentClassification.FooteMarked.fixedShadow_cover_quotient
      (M := M) (U := U) hMq hU hUK
  let e := Classical.choose hcover.2.2
  let eShadow : fixedShadowAt M a ≃* fixedShadow M U :=
    MulEquiv.subgroupCongr (fixedShadow_zpowers M a).symm
  let eShadowQ : fixedShadowAt M a ⧸ pPrimeCore 2 (fixedShadowAt M a) ≃*
      fixedShadow M U ⧸ pPrimeCore 2 (fixedShadow M U) :=
    QuotientGroup.congr (pPrimeCore 2 (fixedShadowAt M a))
      (pPrimeCore 2 (fixedShadow M U)) eShadow
      (CFSG.pPrimeCore_map_iso 2 eShadow)
  exact eShadowQ.trans (e.trans eM)

private noncomputable def relMaCH_quot_equiv_target {S : Set (Subgroup G)} {T : Type} [Group T] [IsSimpleGroup T]
    {M H : Subgroup G} (hMH : M ≤ H) {a : G} (haH : a ∈ H)
    (hM : Marked S T M) (ha : orderOf a = 2)
    (haQ : a ∈ UnbalancedLayer.coreActionKernel M) :
    relMaCH M H a haH ⧸ pPrimeCore 2 (relMaCH M H a haH) ≃* T := by
  let e := relMaCH_equiv_shadow hMH haH
  let eQ : relMaCH M H a haH ⧸ pPrimeCore 2 (relMaCH M H a haH) ≃*
      fixedShadowAt M a ⧸ pPrimeCore 2 (fixedShadowAt M a) :=
    QuotientGroup.congr (pPrimeCore 2 (relMaCH M H a haH))
      (pPrimeCore 2 (fixedShadowAt M a)) e (CFSG.pPrimeCore_map_iso 2 e)
  exact eQ.trans (relMa_quot_equiv_target hM ha haQ)

private abbrev relQ (H : Subgroup G) : Type :=
  H ⧸ pPrimeCore 2 H

private noncomputable def relAbar (H : Subgroup G) (a : G) (haH : a ∈ H) :
    relQ H :=
  QuotientGroup.mk' (pPrimeCore 2 H) ⟨a, haH⟩

private noncomputable def relCbar (H : Subgroup G) (a : G) (haH : a ∈ H) :
    Subgroup (relQ H) :=
  centralizer ({relAbar H a haH} : Set (relQ H))

private noncomputable def relPiCH (H : Subgroup G) (a : G) (haH : a ∈ H) :
    relCH H a haH →* relCbar H a haH :=
  ((QuotientGroup.mk' (pPrimeCore 2 H)).domRestrict (relCH H a haH)).codRestrict
    (relCbar H a haH) (fun x => by
      change QuotientGroup.mk' (pPrimeCore 2 H) (x : H) ∈
        centralizer ({relAbar H a haH} : Set (relQ H))
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hx : (x : H) * ⟨a, haH⟩ = ⟨a, haH⟩ * x :=
        Subgroup.mem_centralizer_singleton_iff.mp x.property
      change QuotientGroup.mk' (pPrimeCore 2 H) (x : H) *
          QuotientGroup.mk' (pPrimeCore 2 H) ⟨a, haH⟩ =
        QuotientGroup.mk' (pPrimeCore 2 H) ⟨a, haH⟩ *
          QuotientGroup.mk' (pPrimeCore 2 H) (x : H)
      rw [← map_mul, ← map_mul, hx])

private noncomputable def relA0 (H : Subgroup G) (a : G) (haH : a ∈ H)
    (Sa : Subgroup G) : Subgroup (relCbar H a haH) :=
  (relJ0 H a haH Sa).map (relPiCH H a haH)

private lemma relPiCH_surjective (H : Subgroup G) (a : G) (haH : a ∈ H)
    (ha : orderOf a = 2) : Function.Surjective (relPiCH H a haH) := by
  intro q
  have haH2 : orderOf (⟨a, haH⟩ : H) = 2 :=
    (Subgroup.orderOf_coe _).symm.trans ha
  have hE : IsPGroup 2 (Subgroup.zpowers (⟨a, haH⟩ : H)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, haH2, pow_one])
  have hmap := CFSG.ComponentClassification.GSThmB.OddQuot.centralizer_map_eq
    (H := H) (E := Subgroup.zpowers (⟨a, haH⟩ : H)) hE
  have hz : (Subgroup.zpowers (⟨a, haH⟩ : H)).map (QuotientGroup.mk' (pPrimeCore 2 H)) =
      Subgroup.zpowers (relAbar H a haH) := by
    rw [relAbar]
    exact MonoidHom.map_zpowers (QuotientGroup.mk' (pPrimeCore 2 H)) ⟨a, haH⟩
  have hcent : Subgroup.centralizer (Subgroup.zpowers (⟨a, haH⟩ : H) : Set H) =
      relCH H a haH := by
    rw [UnbalancedLayer.centralizer_zpowers_eq]
    rfl
  rw [hz, hcent, UnbalancedLayer.centralizer_zpowers_eq] at hmap
  have hCbar : relCbar H a haH = (relCH H a haH).map
      (QuotientGroup.mk' (pPrimeCore 2 H)) := by
    change Subgroup.centralizer ({relAbar H a haH} : Set (relQ H)) = _
    exact hmap
  have hq' : (q : relQ H) ∈ (relCH H a haH).map
      (QuotientGroup.mk' (pPrimeCore 2 H)) := by
    rw [← hCbar]
    exact q.property
  obtain ⟨c, hc, hcq⟩ := Subgroup.mem_map.mp hq'
  refine ⟨⟨c, hc⟩, ?_⟩
  apply Subtype.ext
  exact hcq

private lemma relPiCH_ker_not_two_dvd (H : Subgroup G) (a : G) (haH : a ∈ H) :
    ¬ 2 ∣ Nat.card (relPiCH H a haH).ker := by
  have hπ : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 H)).ker := by
    rw [QuotientGroup.ker_mk']
    have hodd : Odd (Nat.card (pPrimeCore 2 H)) :=
      Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := H))
    intro h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have h := CFSG.ComponentClassification.GSThmB.OddQuot.not_two_dvd_card_ker_domRestrict
    (QuotientGroup.mk' (pPrimeCore 2 H)) hπ (relCH H a haH)
  simpa [relPiCH] using h

private lemma relA0_isPComponent (H : Subgroup G) (a : G) (haH : a ∈ H)
    (ha : orderOf a = 2) {Sa : Subgroup G}
    (hJ0p : IsPComponent 2 (relJ0 H a haH Sa)) :
    IsPComponent 2 (relA0 H a haH Sa) := by
  have hbij := (CFSG.ComponentClassification.CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
      (relPiCH H a haH) (relPiCH_surjective H a haH ha)
      (relPiCH_ker_not_two_dvd H a haH)).1
  exact hbij.1 hJ0p

private noncomputable def relAq (H : Subgroup G) (a : G) (haH : a ∈ H)
    (Sa : Subgroup G) : Subgroup (relQ H) :=
  (relA0 H a haH Sa).map (relCbar H a haH).subtype

private lemma relAq_le_centralizer (H : Subgroup G) (a : G) (haH : a ∈ H)
    (Sa : Subgroup G) :
    relAq H a haH Sa ≤ centralizer ({relAbar H a haH} : Set (relQ H)) := by
  rintro _ ⟨x, hx, rfl⟩
  exact x.property

private lemma relAq_isPComponent (H : Subgroup G) (a : G) (haH : a ∈ H)
    (Sa : Subgroup G) (hA0p : IsPComponent 2 (relA0 H a haH Sa)) :
    IsPComponent 2 ((relAq H a haH Sa).subgroupOf (relCbar H a haH)) := by
  have hsub : (relAq H a haH Sa).subgroupOf (relCbar H a haH) =
      relA0 H a haH Sa := by
    rw [relAq, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (relCbar H a haH).subtype_injective]
  rw [hsub]
  exact hA0p

private lemma relAq_quasisimple {S : Set (Subgroup G)} {T : Type} [Group T]
    [IsSimpleGroup T] {H : Subgroup G} {a : G} (haH : a ∈ H)
    (hB : CFSG.Assembly.ComponentType.LocalBProperty (relQ H))
    (ha : orderOf (relAbar H a haH) = 2) {Sa : Subgroup G}
    (hA0p : IsPComponent 2 (relA0 H a haH Sa)) :
    IsQuasisimple (relAq H a haH Sa) := by
  have hA : IsPComponent 2
      ((relAq H a haH Sa).subgroupOf
        (centralizer ({relAbar H a haH} : Set (relQ H)))) := by
    change IsPComponent 2
      ((relAq H a haH Sa).subgroupOf (relCbar H a haH))
    exact relAq_isPComponent H a haH Sa hA0p
  exact isQuasisimple_of_localB_component hB ha
    (relAq_le_centralizer H a haH Sa) hA

private noncomputable def relA0_quot_equiv_target {T : Type} [Group T]
    [IsSimpleGroup T] {H : Subgroup G} {a : G} (haH : a ∈ H)
    (ha : orderOf a = 2) {Sa : Subgroup G}
    (hJ0p : IsPComponent 2 (relJ0 H a haH Sa))
    (eJ0T : (relJ0 H a haH Sa) ⧸ pPrimeCore 2 (relJ0 H a haH Sa) ≃* T) :
    (relA0 H a haH Sa) ⧸ pPrimeCore 2 (relA0 H a haH Sa) ≃* T := by
  have hThird := (CFSG.ComponentClassification.CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
      (relPiCH H a haH) (relPiCH_surjective H a haH ha)
      (relPiCH_ker_not_two_dvd H a haH)).2.2
  let e0 := Classical.choose (hThird (relJ0 H a haH Sa) hJ0p)
  exact e0.symm.trans eJ0T

private noncomputable def relAq_equiv_A0 (H : Subgroup G) (a : G) (haH : a ∈ H)
    (Sa : Subgroup G) : relAq H a haH Sa ≃* relA0 H a haH Sa :=
  ((relA0 H a haH Sa).equivMapOfInjective (relCbar H a haH).subtype
    (relCbar H a haH).subtype_injective).symm

private noncomputable def relAq_quot_equiv_target {T : Type} [Group T]
    [IsSimpleGroup T] {H : Subgroup G} {a : G} (haH : a ∈ H)
    (ha : orderOf a = 2) {Sa : Subgroup G}
    (hJ0p : IsPComponent 2 (relJ0 H a haH Sa))
    (eJ0T : (relJ0 H a haH Sa) ⧸ pPrimeCore 2 (relJ0 H a haH Sa) ≃* T) :
    (relAq H a haH Sa) ⧸ pPrimeCore 2 (relAq H a haH Sa) ≃* T := by
  let e := relAq_equiv_A0 H a haH Sa
  let eQ : (relAq H a haH Sa) ⧸ pPrimeCore 2 (relAq H a haH Sa) ≃*
      (relA0 H a haH Sa) ⧸ pPrimeCore 2 (relA0 H a haH Sa) :=
    QuotientGroup.congr (pPrimeCore 2 (relAq H a haH Sa))
      (pPrimeCore 2 (relA0 H a haH Sa)) e (CFSG.pPrimeCore_map_iso 2 e)
  exact eQ.trans (relA0_quot_equiv_target haH ha hJ0p eJ0T)

private lemma relJ0_eq_maCH_sup_oddCore {S : Set (Subgroup G)} {T : Type} [Group T]
    [IsSimpleGroup T] {M H : Subgroup G} (hMH : M ≤ H) {a : G} (haH : a ∈ H)
    (ha : orderOf a = 2) (haQ : a ∈ UnbalancedLayer.coreActionKernel M)
    (hM : Marked S T M) {Sa : Subgroup G}
    (hMa_image : (relMaCH M H a haH).map (relF H a haH) = relK a Sa)
    (hKcomp : IsComponent (relK a Sa)) (hKsimple : IsSimpleGroup (relK a Sa))
    (eK : relK a Sa ≃* T)
    (hJ0map : (relJ0 H a haH Sa).map (relF H a haH) = relK a Sa) :
    relMaCH M H a haH ⊔ FooteLit.oddCoreIn (relJ0 H a haH Sa) =
      relJ0 H a haH Sa :=
  CFSG.ComponentClassification.FooteMarked.sup_oddCoreIn_eq_of_full_oddQuotient
    (relMaCH_le_relJ0 hMH haH hMa_image)
    ⟨relMaCH_quot_equiv_target hMH haH hM ha haQ⟩
    ⟨relJ0_quotient_equiv_target haH hKcomp hKsimple eK hJ0map⟩

private lemma relA0_eq_maCH_sup_oddCore {M H : Subgroup G} {a : G} (haH : a ∈ H)
    {Sa : Subgroup G}
    (hcover : relMaCH M H a haH ⊔ FooteLit.oddCoreIn (relJ0 H a haH Sa) =
      relJ0 H a haH Sa) :
    relA0 H a haH Sa =
      (relMaCH M H a haH).map (relPiCH H a haH) ⊔
        (FooteLit.oddCoreIn (relJ0 H a haH Sa)).map (relPiCH H a haH) := by
  calc
    relA0 H a haH Sa = (relJ0 H a haH Sa).map (relPiCH H a haH) := rfl
    _ = ((relMaCH M H a haH ⊔ FooteLit.oddCoreIn (relJ0 H a haH Sa)).map
          (relPiCH H a haH)) := (congrArg (fun X => X.map (relPiCH H a haH)) hcover).symm
    _ = (relMaCH M H a haH).map (relPiCH H a haH) ⊔
        (FooteLit.oddCoreIn (relJ0 H a haH Sa)).map (relPiCH H a haH) :=
      Subgroup.map_sup _ _ _

private lemma relMaCH_map_pi_eq_literalA {M H : Subgroup G} (hMH : M ≤ H)
    {a : G} (haH : a ∈ H) {Sa : Subgroup G} :
    ((relMaCH M H a haH).map (relPiCH H a haH)).map
        (relCbar H a haH).subtype =
      ((fixedShadowAt M a).subgroupOf H).map
        (QuotientGroup.mk' (pPrimeCore 2 H)) := by
  calc
    ((relMaCH M H a haH).map (relPiCH H a haH)).map
        (relCbar H a haH).subtype
        = (relMaCH M H a haH).map
            ((relCbar H a haH).subtype.comp (relPiCH H a haH)) := by
          rw [Subgroup.map_map]
    _ = (relMaCH M H a haH).map
          ((QuotientGroup.mk' (pPrimeCore 2 H)).comp (relCH H a haH).subtype) := rfl
    _ = ((relMaCH M H a haH).map (relCH H a haH).subtype).map
          (QuotientGroup.mk' (pPrimeCore 2 H)) := by
          rw [Subgroup.map_map]
    _ = (relMaH M H a).map (QuotientGroup.mk' (pPrimeCore 2 H)) := by
          congr 1
          rw [relMaCH, Subgroup.map_subgroupOf_eq_of_le (relMaH_le_relCH hMH haH)]
    _ = ((fixedShadowAt M a).subgroupOf H).map
          (QuotientGroup.mk' (pPrimeCore 2 H)) := rfl

private lemma relA0_quasisimple (H : Subgroup G) (a : G) (haH : a ∈ H)
    (Sa : Subgroup G) (hAq : IsQuasisimple (relAq H a haH Sa)) :
    IsQuasisimple (relA0 H a haH Sa) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (relAq_equiv_A0 H a haH Sa) hAq

private lemma relA0_eq_imageMaCH {S : Set (Subgroup G)} {T : Type} [Group T]
    [IsSimpleGroup T] {M H : Subgroup G} (hMH : M ≤ H) {a : G} (haH : a ∈ H)
    (ha : orderOf a = 2) (haQ : a ∈ UnbalancedLayer.coreActionKernel M)
    (hM : Marked S T M) {Sa : Subgroup G}
    (hMa_image : (relMaCH M H a haH).map (relF H a haH) = relK a Sa)
    (hKcomp : IsComponent (relK a Sa)) (hKsimple : IsSimpleGroup (relK a Sa))
    (eK : relK a Sa ≃* T)
    (hJ0map : (relJ0 H a haH Sa).map (relF H a haH) = relK a Sa)
    (hAq : IsQuasisimple (relAq H a haH Sa)) :
    relA0 H a haH Sa = (relMaCH M H a haH).map (relPiCH H a haH) := by
  let J0 := relJ0 H a haH Sa
  let A0 := relA0 H a haH Sa
  let Ima := (relMaCH M H a haH).map (relPiCH H a haH)
  have hcoreImage : (FooteLit.oddCoreIn J0).map (relPiCH H a haH) =
      FooteLit.oddCoreIn A0 := by
    have h := CFSG.ComponentClassification.GSThmB.OddQuot.map_oddCoreIn
      (φ := relPiCH H a haH) (relPiCH_ker_not_two_dvd H a haH) J0
    calc
      (FooteLit.oddCoreIn J0).map (relPiCH H a haH)
          = (CFSG.ComponentClassification.GSThmB.oddCoreIn J0).map
              (relPiCH H a haH) := rfl
      _ = CFSG.ComponentClassification.GSThmB.oddCoreIn
            (J0.map (relPiCH H a haH)) := h
      _ = FooteLit.oddCoreIn (J0.map (relPiCH H a haH)) := rfl
      _ = FooteLit.oddCoreIn A0 := rfl
  have hcoverJ0 := relJ0_eq_maCH_sup_oddCore hMH haH ha haQ hM hMa_image
    hKcomp hKsimple eK hJ0map
  have hA0cover : A0 = Ima ⊔ FooteLit.oddCoreIn A0 := by
    calc
      A0 = Ima ⊔ (FooteLit.oddCoreIn J0).map (relPiCH H a haH) :=
        relA0_eq_maCH_sup_oddCore haH hcoverJ0
      _ = Ima ⊔ FooteLit.oddCoreIn A0 := by rw [hcoreImage]
  have hImage_le_A0 : Ima ≤ A0 := by
    rw [hA0cover]
    exact le_sup_left
  have hoddCore_le_A0 : FooteLit.oddCoreIn A0 ≤ A0 := by
    rw [FooteLit.oddCoreIn]
    exact Subgroup.map_subtype_le _
  let J : Subgroup A0 := Ima.subgroupOf A0
  let P : Subgroup A0 := (FooteLit.oddCoreIn A0).subgroupOf A0
  have hP_eq : P = CFSG.pPrimeCore 2 A0 := by
    show (FooteLit.oddCoreIn A0).subgroupOf A0 = CFSG.pPrimeCore 2 A0
    rw [FooteLit.oddCoreIn, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective A0.subtype_injective]
  have hA0q : IsQuasisimple A0 := relA0_quasisimple H a haH Sa hAq
  have hA0open : CFSG.Open.IsQuasisimple A0 :=
    ⟨hA0q.1.commutator_eq_top, hA0q.2.1⟩
  have hcoreEq : CFSG.Open.componentClassificationOddCore A0 =
      CFSG.pPrimeCore 2 A0 := by
    unfold CFSG.Open.componentClassificationOddCore CFSG.pPrimeCore
    congr 1
    ext N
    simp [Nat.coprime_two_left]
  have hOcenter : CFSG.Open.componentClassificationOddCore A0 ≤
      Subgroup.center A0 :=
    CFSG.ClassicalInvolution.Balance.oddCore_le_center_of_isQuasisimple hA0open
  have hPcenter : P ≤ Subgroup.center A0 := by
    rw [hP_eq, ← hcoreEq]
    exact hOcenter
  have hcoverA0 : J ⊔ P = ⊤ := by
    have h := congrArg (fun X : Subgroup (relCbar H a haH) => X.subgroupOf A0) hA0cover
    rw [Subgroup.subgroupOf_sup hImage_le_A0 hoddCore_le_A0] at h
    simpa [J, P, Subgroup.subgroupOf_self] using h.symm
  have hImaPerf : Group.IsPerfect Ima := by
    haveI : Group.IsPerfect (relMaCH M H a haH) := relMaCH_perfect hMH haH
    exact Group.IsPerfect.map (H := relMaCH M H a haH) (f := relPiCH H a haH)
  have hJperf : Group.IsPerfect J := by
    let e := Subgroup.subgroupOfEquivOfLe hImage_le_A0
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hPcomm : ⁅(⊤ : Subgroup A0), (⊤ : Subgroup A0)⁆ = (⊤ : Subgroup A0) := by
    haveI : Group.IsPerfect (⊤ : Subgroup A0) :=
      Group.IsPerfect.top_iff.mpr hA0q.1
    exact Subgroup.commutator_eq_self (H := (⊤ : Subgroup A0))
  have hle : (⊤ : Subgroup A0) ≤ J ⊔ Subgroup.center A0 := by
    rw [← hcoverA0]
    exact sup_le le_sup_left (hPcenter.trans le_sup_right)
  have hJcomm : ⁅J, J⁆ = J := by
    haveI : Group.IsPerfect J := hJperf
    exact Subgroup.commutator_eq_self
  have htop_le_J : (⊤ : Subgroup A0) ≤ J :=
    CFSG.le_of_perfect_of_le_sup_center hJcomm hPcomm hle
  have hJtop : J = ⊤ := le_antisymm le_top htop_le_J
  have hA0_le_Ima : A0 ≤ Ima := Subgroup.subgroupOf_eq_top.mp hJtop
  exact le_antisymm hA0_le_Ima hImage_le_A0

private lemma relAq_eq_literalA {M H : Subgroup G} (hMH : M ≤ H)
    {a : G} (haH : a ∈ H) {Sa : Subgroup G}
    (hA0eq : relA0 H a haH Sa =
      (relMaCH M H a haH).map (relPiCH H a haH)) :
    relAq H a haH Sa =
      ((fixedShadowAt M a).subgroupOf H).map
        (QuotientGroup.mk' (pPrimeCore 2 H)) := by
  calc
    relAq H a haH Sa = (relA0 H a haH Sa).map
        (relCbar H a haH).subtype := rfl
    _ = ((relMaCH M H a haH).map (relPiCH H a haH)).map
        (relCbar H a haH).subtype := by rw [hA0eq]
    _ = ((fixedShadowAt M a).subgroupOf H).map
        (QuotientGroup.mk' (pPrimeCore 2 H)) :=
      relMaCH_map_pi_eq_literalA (Sa := Sa) hMH haH

private noncomputable def relLiteralA (M H : Subgroup G) (a : G) (haH : a ∈ H) :
    Subgroup (relQ H) :=
  ((fixedShadowAt M a).subgroupOf H).map
    (QuotientGroup.mk' (pPrimeCore 2 H))

private noncomputable def relLiteralA_quot_equiv_target {T : Type} [Group T]
    [IsSimpleGroup T] {M H : Subgroup G} {a : G} (haH : a ∈ H)
    (ha : orderOf a = 2) {Sa : Subgroup G}
    (hAqeq : relAq H a haH Sa = relLiteralA M H a haH)
    (hJ0p : IsPComponent 2 (relJ0 H a haH Sa))
    (eJ0T : (relJ0 H a haH Sa) ⧸ pPrimeCore 2 (relJ0 H a haH Sa) ≃* T) :
    (relLiteralA M H a haH) ⧸ pPrimeCore 2 (relLiteralA M H a haH) ≃* T := by
  let e := relAq_quot_equiv_target (T := T) haH ha hJ0p eJ0T
  let eSub : relAq H a haH Sa ≃* relLiteralA M H a haH :=
    MulEquiv.subgroupCongr hAqeq
  let eQ : (relAq H a haH Sa) ⧸ pPrimeCore 2 (relAq H a haH Sa) ≃*
      (relLiteralA M H a haH) ⧸ pPrimeCore 2 (relLiteralA M H a haH) :=
    QuotientGroup.congr (pPrimeCore 2 (relAq H a haH Sa))
      (pPrimeCore 2 (relLiteralA M H a haH)) eSub
      (CFSG.pPrimeCore_map_iso 2 eSub)
  exact eQ.symm.trans e

private noncomputable def relP_quot_equiv_target {T : Type} [Group T]
    [IsSimpleGroup T] {M H : Subgroup G} {a : G} (haH : a ∈ H)
    (hAperf : Group.IsPerfect (relLiteralA M H a haH))
    (eA_T : (relLiteralA M H a haH) ⧸
      pPrimeCore 2 (relLiteralA M H a haH) ≃* T) :
    (canonicalPerfectLift H (relLiteralA M H a haH)) ⧸
        pPrimeCore 2 (canonicalPerfectLift H (relLiteralA M H a haH)) ≃* T := by
  let A := relLiteralA M H a haH
  let P : Subgroup G := canonicalPerfectLift H A
  let π : H →* (H ⧸ pPrimeCore 2 H) :=
    QuotientGroup.mk' (pPrimeCore 2 H)
  let PH : Subgroup H := P.subgroupOf H
  have hPHle : P ≤ H := by
    dsimp [P, canonicalPerfectLift]
    exact Subgroup.map_subtype_le _
  have hmapA : PH.map π = A := by
    change ((canonicalPerfectLift H A).subgroupOf H).map
      (QuotientGroup.mk' (pPrimeCore 2 H)) = A
    exact canonicalPerfectLift_map_quotient hAperf
  have hπ : ¬ 2 ∣ Nat.card π.ker := by
    rw [show π.ker = pPrimeCore 2 H by
      simpa [π] using QuotientGroup.ker_mk' (pPrimeCore 2 H)]
    exact Nat.prime_two.coprime_iff_not_dvd.mp
      (CFSG.pPrimeCore_coprime_card (p := 2) (G := H))
  have hker : ¬ 2 ∣ Nat.card (π.domRestrict PH).ker :=
    CFSG.ComponentClassification.GSThmB.OddQuot.not_two_dvd_card_ker_domRestrict
      π hπ PH
  let eRestr := Classical.choose
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.exists_restrict_core_quotient_equiv
      π PH hker)
  let eMapSub : (PH.map π) ≃* A := MulEquiv.subgroupCongr hmapA
  let eMapQ : (PH.map π) ⧸ pPrimeCore 2 (PH.map π) ≃*
      A ⧸ pPrimeCore 2 A :=
    QuotientGroup.congr (pPrimeCore 2 (PH.map π)) (pPrimeCore 2 A)
      eMapSub (CFSG.pPrimeCore_map_iso 2 eMapSub)
  let ePH_A : PH ⧸ pPrimeCore 2 PH ≃* A ⧸ pPrimeCore 2 A :=
    eRestr.trans eMapQ
  let eP_PH : P ≃* PH := (Subgroup.subgroupOfEquivOfLe hPHle).symm
  let eQP : P ⧸ pPrimeCore 2 P ≃* PH ⧸ pPrimeCore 2 PH :=
    QuotientGroup.congr (pPrimeCore 2 P) (pPrimeCore 2 PH) eP_PH
      (CFSG.pPrimeCore_map_iso 2 eP_PH)
  exact eQP.trans (ePH_A.trans eA_T)

private lemma relP_marked {S : Set (Subgroup G)} {T : Type} [Group T]
    [IsSimpleGroup T] (hFam : IsomorphicFamily S T) {M H : Subgroup G}
    (hMH : M ≤ H) {a : G} (ha : orderOf a = 2) (haH : a ∈ H)
    (haQ : a ∈ UnbalancedLayer.coreActionKernel M) (hM : Marked S T M)
    {Sa : Subgroup G} (hSaS : Sa ∈ S) (hSaAt : FooteLit.IsTwoComponentAt a Sa)
    (hmareq : fixedShadowAt M a ⊔ FooteLit.oddCoreOfCentralizer a =
      Sa ⊔ FooteLit.oddCoreOfCentralizer a)
    (hJ0p : IsPComponent 2 (relJ0 H a haH Sa))
    (eJ0T : (relJ0 H a haH Sa) ⧸ pPrimeCore 2 (relJ0 H a haH Sa) ≃* T)
    (hAq : IsQuasisimple (relAq H a haH Sa))
    (hAqeq : relAq H a haH Sa = relLiteralA M H a haH) :
    Marked S T (canonicalPerfectLift H (relLiteralA M H a haH)) := by
  classical
  let A : Subgroup (H ⧸ pPrimeCore 2 H) := relLiteralA M H a haH
  let P : Subgroup G := canonicalPerfectLift H A
  change Marked S T P
  have hAqeqA : relAq H a haH Sa = A := by simpa [A] using hAqeq
  have hAperf : Group.IsPerfect A := by
    rw [← hAqeqA]
    exact hAq.1
  have hPperfect : Group.IsPerfect P := by
    let π : H →* (H ⧸ pPrimeCore 2 H) := QuotientGroup.mk' (pPrimeCore 2 H)
    let V : Subgroup H := A.comap π
    have hV : Group.IsPerfect ((CFSG.perfectResidual V).map V.subtype) :=
      CFSG.SignalizerFunctorTheorem.Nonsolvable.isPerfect_perfectResidual_map V
    haveI : Group.IsPerfect ((CFSG.perfectResidual V).map V.subtype) := hV
    exact Group.IsPerfect.map (H := (CFSG.perfectResidual V).map V.subtype)
      (f := H.subtype)
  have eA_T : A ⧸ pPrimeCore 2 A ≃* T := by
    simpa [A] using relLiteralA_quot_equiv_target (T := T) haH ha hAqeq hJ0p eJ0T
  have eP_T : P ⧸ pPrimeCore 2 P ≃* T := by
    simpa [P, A] using relP_quot_equiv_target (T := T) (M := M) (H := H) (a := a)
      haH hAperf eA_T
  have hPq : IsQuasisimple (P ⧸ pPrimeCore 2 P) :=
    isQuasisimple_oddCoreQuotient_of_perfect_simple hPperfect eP_T
  have hSa2 : orderOf (⟨a, haH⟩ : H) = 2 :=
    (Subgroup.orderOf_coe _).symm.trans ha
  have hU : IsPGroup 2 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  have hAcent : A ≤ Subgroup.centralizer ({relAbar H a haH} :
      Set (H ⧸ pPrimeCore 2 H)) := by
    simpa [A, relLiteralA, relativeLiftA, relAbar] using
      relativeLiftA_le_centralizer (S := S) (T := T) hM hMH ha haH
  have haPcore : a ∈ UnbalancedLayer.coreActionKernel P := by
    have h := canonicalPerfectLift_coreActionKernel (H := H) (A := A)
      (b := (⟨a, haH⟩ : H)) (bbar := relAbar H a haH) rfl hAcent
    simpa [P] using h
  have hUK : Subgroup.zpowers a ≤ UnbalancedLayer.coreActionKernel P :=
    zpowers_le.mpr haPcore
  obtain ⟨-, -, eF0, -⟩ :=
    fixedShadow_cover_quotient (M := P) (U := Subgroup.zpowers a) hPq hU hUK
  have eF : fixedShadowAt P a ⧸ pPrimeCore 2 (fixedShadowAt P a) ≃* T := by
    let eSh : fixedShadow P (Subgroup.zpowers a) ≃* fixedShadowAt P a :=
      MulEquiv.subgroupCongr (fixedShadow_zpowers P a)
    let eQ : (fixedShadow P (Subgroup.zpowers a)) ⧸
          pPrimeCore 2 (fixedShadow P (Subgroup.zpowers a)) ≃*
        (fixedShadowAt P a) ⧸ pPrimeCore 2 (fixedShadowAt P a) :=
      QuotientGroup.congr (pPrimeCore 2 (fixedShadow P (Subgroup.zpowers a)))
        (pPrimeCore 2 (fixedShadowAt P a)) eSh
        (CFSG.pPrimeCore_map_iso 2 eSh)
    exact eQ.symm.trans (eF0.trans eP_T)
  let eA : Sa ⧸ pPrimeCore 2 Sa ≃* T := Classical.choice (hFam.2.1 Sa hSaS)
  have hA2 : FooteLit.IsTwoComponentIn Sa (Subgroup.centralizer ({a} : Set G)) :=
    ⟨hSaAt.2.1, hSaAt.2.2⟩
  have hFX : fixedShadowAt P a ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [show fixedShadowAt P a = fixedShadow P (Subgroup.zpowers a) from
      (fixedShadow_zpowers P a).symm]
    have h := (fixedShadow_le_inf P (Subgroup.zpowers a)).trans inf_le_right
    simpa [UnbalancedLayer.centralizer_zpowers_eq] using h
  have hF : Group.IsPerfect (fixedShadowAt P a) := fixedShadowAt_perfect P a
  have hMaH : fixedShadowAt M a ≤ H := (fixedShadowAt_le M a).trans hMH
  have hAeqMa : A = ((fixedShadowAt M a).subgroupOf H).map
      (QuotientGroup.mk' (pPrimeCore 2 H)) := by
    dsimp [A, relLiteralA]
  have hMaP : fixedShadowAt M a ≤ P :=
    K1_le_canonicalPerfectLift hMaH hAeqMa (fixedShadowAt_perfect M a)
  have hMaC : fixedShadowAt M a ≤
      Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
    rw [show fixedShadowAt M a = fixedShadow M (Subgroup.zpowers a) from
      (fixedShadow_zpowers M a).symm]
    exact (fixedShadow_le_inf M (Subgroup.zpowers a)).trans inf_le_right
  have hMaPa : fixedShadowAt M a ≤ fixedShadowAt P a := by
    have h := CFSG.ComponentClassification.FooteMarked.le_fixedShadow_of_perfect
      (M := P) (U := Subgroup.zpowers a) (fixedShadowAt_perfect M a)
      (le_inf hMaP hMaC)
    simpa [fixedShadow_zpowers] using h
  have hSa_le : Sa ≤ fixedShadowAt M a ⊔ FooteLit.oddCoreOfCentralizer a := by
    rw [hmareq]
    exact le_sup_left
  have hAF : Sa ≤ fixedShadowAt P a ⊔ FooteLit.oddCoreOfCentralizer a :=
    hSa_le.trans (sup_le_sup_right hMaPa _)
  have hmarkP : fixedShadowAt P a ⊔ FooteLit.oddCoreOfCentralizer a =
      Sa ⊔ FooteLit.oddCoreOfCentralizer a :=
    oddCoreImage_eq_of_contains_component (T := T) hA2 hFX hF eA eF hAF
  refine ⟨hPperfect, ⟨eP_T⟩, a, ha, haPcore, Sa, hSaS, ?_⟩
  simpa [FooteLit.oddCoreOfCentralizer] using hmarkP

private lemma relLiteralA_quasisimple {M H : Subgroup G} {a : G} (haH : a ∈ H)
    {Sa : Subgroup G} (hAq : IsQuasisimple (relAq H a haH Sa))
    (hAqeq : relAq H a haH Sa = relLiteralA M H a haH) :
    IsQuasisimple (relLiteralA M H a haH) := by
  rw [← hAqeq]
  exact hAq

private lemma relLiteralA_center_equiv_target {T : Type} [Group T] [IsSimpleGroup T]
    {M H : Subgroup G} {a : G} (haH : a ∈ H) {Sa : Subgroup G}
    (hAq : IsQuasisimple (relAq H a haH Sa))
    (hAqeq : relAq H a haH Sa = relLiteralA M H a haH)
    (eA_T : (relLiteralA M H a haH) ⧸
      pPrimeCore 2 (relLiteralA M H a haH) ≃* T) :
    Nonempty ((relLiteralA M H a haH) ⧸
      Subgroup.center (relLiteralA M H a haH) ≃* T) := by
  let A := relLiteralA M H a haH
  have hAqA : IsQuasisimple A := relLiteralA_quasisimple haH hAq hAqeq
  haveI : IsSimpleGroup (A ⧸ pPrimeCore 2 A) := eA_T.isSimpleGroup
  have hAQs : IsSimpleGroup (A ⧸ CFSG.oddCore A) := by
    let eOdd : A ⧸ CFSG.oddCore A ≃* A ⧸ pPrimeCore 2 A :=
      QuotientGroup.quotientMulEquivOfEq
        (CFSG.Assembly.Dichotomy.oddCore_eq_pPrimeCore A)
    exact eOdd.isSimpleGroup
  have hcenter : Subgroup.center A = CFSG.oddCore A :=
    CFSG.OddStandard.SmallF3.Omega.ff_center_eq_oddCore_of_simple hAqA hAQs
  let eCP : A ⧸ Subgroup.center A ≃* A ⧸ pPrimeCore 2 A :=
    QuotientGroup.quotientMulEquivOfEq
      (hcenter.trans (CFSG.Assembly.Dichotomy.oddCore_eq_pPrimeCore A))
  exact ⟨eCP.trans eA_T⟩

private lemma relLiteralA_center_odd {T : Type} [Group T] [IsSimpleGroup T]
    {M H : Subgroup G} {a : G} (haH : a ∈ H) {Sa : Subgroup G}
    (hAq : IsQuasisimple (relAq H a haH Sa))
    (hAqeq : relAq H a haH Sa = relLiteralA M H a haH)
    (eA_T : (relLiteralA M H a haH) ⧸
      pPrimeCore 2 (relLiteralA M H a haH) ≃* T) :
    Odd (Nat.card (Subgroup.center (relLiteralA M H a haH))) := by
  let A := relLiteralA M H a haH
  have hAqA : IsQuasisimple A := relLiteralA_quasisimple haH hAq hAqeq
  haveI : IsSimpleGroup (A ⧸ pPrimeCore 2 A) := eA_T.isSimpleGroup
  have hAQs : IsSimpleGroup (A ⧸ CFSG.oddCore A) := by
    let eOdd : A ⧸ CFSG.oddCore A ≃* A ⧸ pPrimeCore 2 A :=
      QuotientGroup.quotientMulEquivOfEq
        (CFSG.Assembly.Dichotomy.oddCore_eq_pPrimeCore A)
    exact eOdd.isSimpleGroup
  have hcenter : Subgroup.center A = CFSG.oddCore A :=
    CFSG.OddStandard.SmallF3.Omega.ff_center_eq_oddCore_of_simple hAqA hAQs
  rw [hcenter]
  exact CFSG.OddStandard.SmallF3.Omega.ff_odd_card_oddCore A

private noncomputable def relK_equiv_target {T : Type} [Group T] [IsSimpleGroup T]
    {J C : Subgroup G} (hJC : FooteLit.IsTwoComponentIn J C)
    (eJ : J ⧸ pPrimeCore 2 J ≃* T) :
    (J.subgroupOf C).map (QuotientGroup.mk' (pPrimeCore 2 C)) ≃* T := by
  let J' := J.subgroupOf C
  exact (CatalogueBHeldSmallCore.subnormalCoreQuotientEquivImage
      2 J' hJC.2.choose_spec.2.1).symm.trans
    ((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (Subgroup.subgroupOfEquivOfLe hJC.1)).trans eJ)

theorem relative_lift_of_localB {S : Set (Subgroup G)} {T : Type} [Group T]
    [IsSimpleGroup T] (hFam : IsomorphicFamily S T) {M H : Subgroup G}
    (hM : Marked S T M) (hMH : M ≤ H) {a : G} (ha : orderOf a = 2)
    (haH : a ∈ H) (haQ : a ∈ UnbalancedLayer.coreActionKernel M)
    (hB : CFSG.Assembly.ComponentType.LocalBProperty (H ⧸ pPrimeCore 2 H)) :
    let A : Subgroup (H ⧸ pPrimeCore 2 H) :=
      ((fixedShadowAt M a).subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H))
    let abar : H ⧸ pPrimeCore 2 H :=
      QuotientGroup.mk' (pPrimeCore 2 H) ⟨a, haH⟩
    orderOf abar = 2 ∧
      A ≤ Subgroup.centralizer ({abar} : Set (H ⧸ pPrimeCore 2 H)) ∧
      IsComponent (A.subgroupOf
        (Subgroup.centralizer ({abar} : Set (H ⧸ pPrimeCore 2 H)))) ∧
      Marked S T (canonicalPerfectLift H A) ∧
      Nonempty (A ⧸ Subgroup.center A ≃* T) ∧
      Odd (Nat.card (Subgroup.center A)) := by
  classical
  obtain ⟨Sa, hSaS, hSaAt, hmareq⟩ :=
    Marked.witness_at_every_involution (T := T) hFam hM ha haQ
  have hJC : FooteLit.IsTwoComponentIn Sa (relC a) := ⟨hSaAt.2.1, hSaAt.2.2⟩
  let eSa : Sa ⧸ pPrimeCore 2 Sa ≃* T := Classical.choice (hFam.2.1 Sa hSaS)
  have hKpair := quotient_image_isComponent_of_isTwoComponentIn (T := T) hJC eSa
  have hKcomp : IsComponent (relK a Sa) := hKpair.1
  have hKsimple : IsSimpleGroup (relK a Sa) := hKpair.2
  let eK : relK a Sa ≃* T := relK_equiv_target hJC eSa
  have hMa_image : (relMaCH M H a haH).map (relF H a haH) = relK a Sa :=
    relMaCH_map_relF_eq_relK (S := S) (T := T) hMH haH hSaAt hmareq
  have hJ0map : (relJ0 H a haH Sa).map (relF H a haH) = relK a Sa :=
    relJ0_map_relF_eq_relK haH hMH hMa_image
  have hJ0p : IsPComponent 2 (relJ0 H a haH Sa) :=
    relJ0_isPComponent haH hKcomp hKsimple eK hJ0map
  have eJ0T : (relJ0 H a haH Sa) ⧸ pPrimeCore 2 (relJ0 H a haH Sa) ≃* T :=
    relJ0_quotient_equiv_target haH hKcomp hKsimple eK hJ0map
  have hA0p : IsPComponent 2 (relA0 H a haH Sa) :=
    relA0_isPComponent H a haH ha hJ0p
  have hAbar2 : orderOf (relAbar H a haH) = 2 := by
    simpa [relAbar] using relativeLift_abar_order (H := H) ha haH
  have hAq : IsQuasisimple (relAq H a haH Sa) :=
    relAq_quasisimple (S := S) (T := T) haH hB hAbar2 hA0p
  have hA0eq : relA0 H a haH Sa =
      (relMaCH M H a haH).map (relPiCH H a haH) :=
    relA0_eq_imageMaCH hMH haH ha haQ hM hMa_image hKcomp hKsimple eK
      hJ0map hAq
  have hAqeq : relAq H a haH Sa = relLiteralA M H a haH :=
    relAq_eq_literalA hMH haH hA0eq
  have eA_T : (relLiteralA M H a haH) ⧸
      pPrimeCore 2 (relLiteralA M H a haH) ≃* T :=
    relLiteralA_quot_equiv_target (T := T) haH ha hAqeq hJ0p eJ0T
  have hAqSub : IsQuasisimple
      ((relAq H a haH Sa).subgroupOf (relCbar H a haH)) := by
    let eSub := Subgroup.subgroupOfEquivOfLe
      (relAq_le_centralizer H a haH Sa)
    exact IsQuasisimple.of_mulEquiv eSub hAq
  obtain ⟨K, hK0, hKsub, hKmap, hKmin⟩ :=
    relAq_isPComponent H a haH Sa hA0p
  have hcompAq : IsComponent
      ((relAq H a haH Sa).subgroupOf (relCbar H a haH)) :=
    ⟨hAqSub, hKsub⟩
  have hsubEq : ((relAq H a haH Sa).subgroupOf (relCbar H a haH)) =
      (((fixedShadowAt M a).subgroupOf H).map
        (QuotientGroup.mk' (pPrimeCore 2 H))).subgroupOf
        (Subgroup.centralizer
          ({QuotientGroup.mk' (pPrimeCore 2 H) ⟨a, haH⟩} :
            Set (H ⧸ pPrimeCore 2 H))) := by
    rw [hAqeq]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [relAbar] using hAbar2
  · simpa [relLiteralA, relativeLiftA, relAbar] using
      relativeLiftA_le_centralizer (S := S) (T := T) hM hMH ha haH
  · rw [← hsubEq]
    exact hcompAq
  · simpa [relLiteralA] using
      relP_marked (T := T) hFam hMH ha haH haQ hM hSaS hSaAt hmareq
        hJ0p eJ0T hAq hAqeq
  · exact relLiteralA_center_equiv_target (T := T) haH hAq hAqeq eA_T
  · exact relLiteralA_center_odd (T := T) haH hAq hAqeq eA_T
theorem relative_lift_of_localB_proper_H
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Blueprint.Catalog)
    (hU : CFSG.ComponentClassification.CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hheld : CFSG.ComponentClassification.KProperRelativeB.HeldInput)
    {G : Type} [Group G] [Finite G]
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {H : Subgroup G} (hH : H ≠ ⊤)
    {S : Set (Subgroup G)} {T : Type} [Group T] [IsSimpleGroup T]
    (hFam : IsomorphicFamily S T) {M : Subgroup G} (hM : Marked S T M)
    (hMH : M ≤ H) {a : G} (ha : orderOf a = 2) (haH : a ∈ H)
    (haQ : a ∈ UnbalancedLayer.coreActionKernel M) :
    let A : Subgroup (H ⧸ pPrimeCore 2 H) :=
      ((fixedShadowAt M a).subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H))
    let abar : H ⧸ pPrimeCore 2 H :=
      QuotientGroup.mk' (pPrimeCore 2 H) ⟨a, haH⟩
    orderOf abar = 2 ∧
      A ≤ Subgroup.centralizer ({abar} : Set (H ⧸ pPrimeCore 2 H)) ∧
      IsComponent (A.subgroupOf
        (Subgroup.centralizer ({abar} : Set (H ⧸ pPrimeCore 2 H)))) ∧
      Marked S T (canonicalPerfectLift H A) ∧
      Nonempty (A ⧸ Subgroup.center A ≃* T) ∧
      Odd (Nat.card (Subgroup.center A)) := by
  obtain ⟨-, -, hB⟩ := relative_localB_of_proper_H hS hU hheld hK hH
  exact relative_lift_of_localB (S := S) (T := T) hFam hM hMH ha haH haQ hB

end CFSG.ComponentClassification.FooteMarked
