module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWHull
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWRestrict
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

open scoped commutatorElement

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section HullPf


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {w : G}

private theorem hullpf_inf_le_coreAt {J : Subgroup G}
    (hJ : w ∈ Balance.Bootstrap.trivialOnQuot J) {S' : Sylow 2 G}
    (hwS : w ∈ (S' : Subgroup G)) : J ⊓ (S' : Subgroup G) ≤ TwinADescent.coreAt w J := by
  have hcomm : ∀ a ∈ J ⊓ (S' : Subgroup G), a ∈ Subgroup.centralizer ({w} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : ⁅w, a⁆ ∈ Balance.oddCoreIn J :=
      (Balance.Bootstrap.mem_trivialOnQuot_iff.mp hJ).2 a ha.1
    have h2 : ⁅w, a⁆ ∈ (S' : Subgroup G) := by
      rw [commutatorElement_def]
      exact (S' : Subgroup G).mul_mem ((S' : Subgroup G).mul_mem
        ((S' : Subgroup G).mul_mem hwS ha.2) ((S' : Subgroup G).inv_mem hwS))
        ((S' : Subgroup G).inv_mem ha.2)
    have h3 : IsPGroup 2 (Subgroup.zpowers ⁅w, a⁆) :=
      S'.isPGroup'.to_le (Subgroup.zpowers_le.mpr h2)
    have h4 := eq_one_of_isPGroup_of_mem_odd (Balance.odd_card_oddCoreIn J) h1 h3
    exact (commutatorElement_eq_one_iff_mul_comm.mp h4).symm
  exact le_tightCore_of_isPGroup (fun a ha => ⟨ha.1, hcomm a ha⟩)
    (S'.isPGroup'.to_le inf_le_right)

private theorem hullpf_mem_sylow_of_mem {S' : Sylow 2 G} {S₁ : Sylow 2 ↥(coreHull Ω w)}
    (hS₁ : (S₁ : Subgroup ↥(coreHull Ω w)).map (secEmb Ω w) ≤ (S' : Subgroup G))
    {x : ↥(coreHull Ω w)} (hx : secEmb Ω w x ∈ (S' : Subgroup G)) :
    x ∈ (S₁ : Subgroup ↥(coreHull Ω w)) := by
  have h2 : IsPGroup 2 ↥((S' : Subgroup G).comap (secEmb Ω w)) :=
    S'.isPGroup'.comap_of_injective _ secEmb_injective
  have hle : (S₁ : Subgroup ↥(coreHull Ω w)) ≤ (S' : Subgroup G).comap (secEmb Ω w) :=
    fun y hy => hS₁ ⟨y, hy, rfl⟩
  have heq := S₁.is_maximal' h2 hle
  have hx' : x ∈ (S' : Subgroup G).comap (secEmb Ω w) := hx
  rw [heq] at hx'
  exact hx'

private theorem hullpf_map_mem_USet (hc2 : IsPGroup 2 (Subgroup.zpowers w))
    {V : Subgroup ↥(coreHull Ω w)} (hV : V ∈ USet (hullFam Ω w)) :
    V.map (secEmb Ω w) ∈ USet Ω := by
  have h1 := map_mem_USet_restrict hV
  have h2 := map_mem_USet_restrict h1
  have e : V.map (secEmb Ω w) =
      (V.map (coreHull Ω w).subtype).map (Subgroup.centralizer ({w} : Set G)).subtype := by
    rw [Subgroup.map_map]
    rfl
  rw [e]
  exact TwinADescent.mem_USet_of_core hc2 h2

private theorem hullpf_map_mem_RSet (hc2 : IsPGroup 2 (Subgroup.zpowers w))
    {P : Subgroup ↥(coreHull Ω w)} (hP : P ∈ RSet (hullFam Ω w)) :
    P.map (secEmb Ω w) ∈ RSet Ω := by
  have h1 := map_mem_RSet_restrict hP
  have h2 := map_mem_RSet_restrict h1
  have e : P.map (secEmb Ω w) =
      (P.map (coreHull Ω w).subtype).map (Subgroup.centralizer ({w} : Set G)).subtype := by
    rw [Subgroup.map_map]
    rfl
  rw [e]
  obtain ⟨L, hL, hPL⟩ := exists_isSylow2In_of_mem_RSet h2
  obtain ⟨K, hK, rfl⟩ := hL
  exact mem_RSet_of_isSylow2In hK.1 (((TwinADescent.isSylow2In_coreAt_iff hc2 hK.2).mp hPL).1)

private theorem hullpf_mem_USet_hullFam (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers w))
    {J P U : Subgroup G} (hJ : J ∈ tqMembers3 Ω w) (hP : IsSylow2In P (TwinADescent.coreAt w J))
    (hUP : U ≤ P) (hcyc : IsCyclic ↥U) (hidx : U.relIndex P = 2) :
    ((U.subgroupOf (Subgroup.centralizer ({w} : Set G))).subgroupOf (coreHull Ω w)) ∈
      USet (hullFam Ω w) := by
  have hcore : TwinADescent.coreAt w J ∈ TwinADescent.coreFamily Ω w :=
    TwinADescent.coreAt_mem_coreFamily hJ
  have hU1 : U.subgroupOf (Subgroup.centralizer ({w} : Set G)) ∈
      USet (restrictFamily (TwinADescent.coreFamily Ω w) (Subgroup.centralizer ({w} : Set G))) :=
    CFSG.ClassicalInvolution.Asc77.AscAET.mem_USet_restrict_of_sylow hcore
      (TwinADescent.coreAt_le_centralizer w J) hP hUP hcyc hidx
  exact mem_USet_restrict_of_le (TwinADescent.hypOmegaGen_coreFamily hΩ hc2) hU1
    (subgroupOf_mem_restrictFamily hcore (TwinADescent.coreAt_le_centralizer w J))
    (le_coreHull hJ) (Subgroup.subgroupOf_mono _ (hUP.trans hP.1))

private theorem hullpf_map_lift {J A : Subgroup G} (hJ : J ∈ tqMembers3 Ω w)
    (hA : A ≤ TwinADescent.coreAt w J) :
    ((A.subgroupOf (Subgroup.centralizer ({w} : Set G))).subgroupOf (coreHull Ω w)).map
      (secEmb Ω w) = A := by
  have hAC : A ≤ Subgroup.centralizer ({w} : Set G) :=
    hA.trans (TwinADescent.coreAt_le_centralizer w J)
  have hAX : A.subgroupOf (Subgroup.centralizer ({w} : Set G)) ≤ coreHull Ω w :=
    (Subgroup.subgroupOf_mono _ hA).trans (le_coreHull hJ)
  unfold secEmb
  rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hAX,
    Subgroup.map_subgroupOf_eq_of_le hAC]

private theorem hullpf_map_le {M : Subgroup G} (hM : M ∈ tqMembers3 Ω w)
    {V : Subgroup ↥(coreHull Ω w)} (hV : V ≤ secOf Ω w M) :
    V.map (secEmb Ω w) ≤ TwinADescent.coreAt w M := by
  have := Subgroup.map_mono (f := secEmb Ω w) hV
  rwa [map_secOf hM] at this

private theorem hullpf_key (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers w))
    {S' : Sylow 2 G} {W' : Subgroup G} (hW' : W' ∈ WSet Ω) (hW'S : W' ≤ (S' : Subgroup G))
    (hwS : w ∈ (S' : Subgroup G)) {S₁ : Sylow 2 ↥(coreHull Ω w)}
    (hS₁ : (S₁ : Subgroup ↥(coreHull Ω w)).map (secEmb Ω w) ≤ (S' : Subgroup G))
    {J : Subgroup G} (hJ : J ∈ tqMembers3 Ω w) {V : Subgroup ↥(coreHull Ω w)}
    (hV : V ∈ USet (hullFam Ω w)) (hVS₁ : V ≤ (S₁ : Subgroup ↥(coreHull Ω w)))
    (hVJ : V ≤ secOf Ω w J) :
    J ⊓ W' ∈ USet Ω ∧ J ⊓ W' ≤ TwinADescent.coreAt w J ∧
      ((J ⊓ W').subgroupOf (Subgroup.centralizer ({w} : Set G))).subgroupOf (coreHull Ω w) ∈
        USet (hullFam Ω w) := by
  have hVU : V.map (secEmb Ω w) ∈ USet Ω := hullpf_map_mem_USet hc2 hV
  have hVmapJ : V.map (secEmb Ω w) ≤ TwinADescent.coreAt w J := hullpf_map_le hJ hVJ
  have hVS' : V.map (secEmb Ω w) ≤ (S' : Subgroup G) := (Subgroup.map_mono hVS₁).trans hS₁
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hVU
  have hcard : 2 < Nat.card ↥(J ⊓ (S' : Subgroup G)) := by
    have := Subgroup.card_le_of_le (le_inf (hVmapJ.trans (TwinADescent.coreAt_le_left w J)) hVS')
    omega
  have hUinf : J ⊓ W' ∈ USet Ω := inf_W_mem_USet_of_card hΩ hW' hW'S hJ.1 hcard
  have hUcore : J ⊓ (S' : Subgroup G) ≤ TwinADescent.coreAt w J :=
    hullpf_inf_le_coreAt hJ.2 hwS
  have hUle : J ⊓ W' ≤ TwinADescent.coreAt w J := (inf_le_inf_left J hW'S).trans hUcore
  obtain ⟨R', -, J', hJ'Ω, hR'J', hUR', hUcyc, hR'card, hU4⟩ :=
    Sec6Gen.exists_data_of_mem_USet hΩ hUinf
  have hU2 : IsPGroup 2 ↥(J ⊓ W') := Sec6Gen.isPGroup_of_mem_USet hΩ hUinf
  have hJJ' : J' = J :=
    Sec6Gen.eq_of_le_of_le hΩ hJ'Ω hJ.1 hU2 hU4 (hUR'.trans hR'J'.1) inf_le_left
  have hR'J : IsSylow2In R' J := hJJ' ▸ hR'J'
  obtain ⟨P, hP, hUP⟩ := IsSylow2In.exists_ge hU2 hUle
  have hPJ : IsSylow2In P J := ((TwinADescent.isSylow2In_coreAt_iff hc2 hJ.2).mp hP).1
  have hPcard : Nat.card ↥P = 2 * Nat.card ↥(J ⊓ W') := by
    rw [hPJ.natCard_eq hR'J, hR'card]
  have hidx : (J ⊓ W').relIndex P = 2 :=
    CFSG.ClassicalInvolution.Asc77.AscAET.relIndex_eq_two_of_card hUP hPcard
  exact ⟨hUinf, hUle, hullpf_mem_USet_hullFam hΩ hc2 hJ hP hUP hUcyc hidx⟩

theorem printedHull_proved : PrintedHull where
  exists_W := by
    intro G _ _ Ω K S R W H w c hw1 hw2 S₁ hRS₁
    classical
    have hΩ : HypOmegaGen Ω := c.stand.hyp
    have hK : K ∈ Ω := c.stand.mem
    obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
    have hc2 : IsPGroup 2 (Subgroup.zpowers w) :=
      IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1]
        norm_num)
    have hι : Function.Injective (secEmb Ω w) := secEmb_injective
    have hΛ : HypOmegaGen (hullFam Ω w) :=
      hypOmegaGen_restrict (TwinADescent.hypOmegaGen_coreFamily hΩ hc2) (coreHull Ω w)
    have hT₁2 : IsPGroup 2 ((S₁ : Subgroup ↥(coreHull Ω w)).map (secEmb Ω w)) :=
      S₁.isPGroup'.map (secEmb Ω w)
    have hcomm : Commutes (Subgroup.zpowers w) ((S₁ : Subgroup ↥(coreHull Ω w)).map (secEmb Ω w)) := by
      rintro x hx _ ⟨y, -, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp
        ((y : ↥(Subgroup.centralizer ({w} : Set G))).2)) k).symm.eq
    have hP : IsPGroup 2 ↥(((S₁ : Subgroup ↥(coreHull Ω w)).map (secEmb Ω w)) ⊔ Subgroup.zpowers w) :=
      hT₁2.to_sup_of_normal_left' hc2 fun y hy =>
        mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_of_mem_of_commutes hy hcomm)
    obtain ⟨S', hS'⟩ := hP.exists_le_sylow
    have hT₁S' : ∀ y : ↥(coreHull Ω w), y ∈ (S₁ : Subgroup ↥(coreHull Ω w)) →
        secEmb Ω w y ∈ (S' : Subgroup G) := fun y hy =>
      (le_sup_left.trans hS') ⟨y, hy, rfl⟩
    have hS₁S' : (S₁ : Subgroup ↥(coreHull Ω w)).map (secEmb Ω w) ≤ (S' : Subgroup G) :=
      le_sup_left.trans hS'
    have hwS' : w ∈ (S' : Subgroup G) := hS' (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
    have hRS' : R ≤ (S' : Subgroup G) := hRS₁.trans hS₁S'
    obtain ⟨z, hz, hcz⟩ := c.exists_centralizer_le
    obtain ⟨x, -, -, hW'mem, hW'S, hW'n, hCW⟩ :=
      exists_W_of_sylow hΩ hK c.hyp.trans hz hcz hRR hRK hRS c.stand.hW.1 c.stand.hW.2.1
        c.stand.hW.2.2 c.hyp.cent hRR hRK hRS'
    set η₁ : Set (Subgroup ↥(coreHull Ω w)) :=
      {V | V ∈ USet (hullFam Ω w) ∧ V ≤ (S₁ : Subgroup ↥(coreHull Ω w)) ∧
        V.map (secEmb Ω w) ≤ conjSub x W} with hη₁def
    have hdist := inDistinct_canonical hΩ hW'mem
    have hη₁dist : InDistinctMembers (hullFam Ω w) η₁ := by
      intro V hV V' hV' hne L hL hVV'
      obtain ⟨M, hM, rfl⟩ := exists_of_mem_hullFam hL
      exact hdist (V.map (secEmb Ω w)) ⟨hullpf_map_mem_USet hc2 hV.1, hV.2.2⟩
        (V'.map (secEmb Ω w)) ⟨hullpf_map_mem_USet hc2 hV'.1, hV'.2.2⟩
        (fun h => hne (Subgroup.map_injective hι h)) M hM.1
        ⟨(hullpf_map_le hM hVV'.1).trans (TwinADescent.coreAt_le_left w M),
          (hullpf_map_le hM hVV'.2).trans (TwinADescent.coreAt_le_left w M)⟩
    have hmax : ∀ η₂ : Set (Subgroup ↥(coreHull Ω w)),
        η₂ ⊆ {V | V ∈ USet (hullFam Ω w) ∧ V ≤ (S₁ : Subgroup ↥(coreHull Ω w))} →
        InDistinctMembers (hullFam Ω w) η₂ → η₂.ncard ≤ η₁.ncard := by
      intro η₂ hsub hd2
      have hmem : ∀ V ∈ η₂, ∃ J ∈ tqMembers3 Ω w, V ≤ secOf Ω w J := by
        intro V hV
        obtain ⟨L, hL, hVL⟩ := Sec6Gen.exists_member_of_mem_USet hΛ (hsub hV).1
        obtain ⟨J, hJ, rfl⟩ := exists_of_mem_hullFam hL
        exact ⟨J, hJ, hVL⟩
      choose! J₀ hJ₀ hVJ₀ using hmem
      have hkey : ∀ V ∈ η₂, J₀ V ⊓ conjSub x W ∈ USet Ω ∧
          J₀ V ⊓ conjSub x W ≤ TwinADescent.coreAt w (J₀ V) ∧
          ((J₀ V ⊓ conjSub x W).subgroupOf (Subgroup.centralizer ({w} : Set G))).subgroupOf
            (coreHull Ω w) ∈ USet (hullFam Ω w) := fun V hV =>
        hullpf_key hΩ hc2 hW'mem hW'S hwS' hS₁S' (hJ₀ V hV) (hsub hV).1 (hsub hV).2 (hVJ₀ V hV)
      have hmaps : Set.MapsTo (fun V => ((J₀ V ⊓ conjSub x W).subgroupOf
          (Subgroup.centralizer ({w} : Set G))).subgroupOf (coreHull Ω w)) η₂ η₁ := by
        intro V hV
        obtain ⟨-, hUle, hUΛ⟩ := hkey V hV
        refine ⟨hUΛ, ?_, ?_⟩
        · intro y hy
          exact hullpf_mem_sylow_of_mem hS₁S'
            (hW'S (Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hy)).2)
        · rw [hullpf_map_lift (hJ₀ V hV) hUle]
          exact inf_le_right
      have hinj : Set.InjOn (fun V => ((J₀ V ⊓ conjSub x W).subgroupOf
          (Subgroup.centralizer ({w} : Set G))).subgroupOf (coreHull Ω w)) η₂ := by
        intro V₁ hV₁ V₂ hV₂ h
        by_contra hne
        have h' : J₀ V₁ ⊓ conjSub x W = J₀ V₂ ⊓ conjSub x W := by
          have := congrArg (Subgroup.map (secEmb Ω w)) h
          rwa [hullpf_map_lift (hJ₀ V₁ hV₁) (hkey V₁ hV₁).2.1,
            hullpf_map_lift (hJ₀ V₂ hV₂) (hkey V₂ hV₂).2.1] at this
        obtain ⟨hU, -, -⟩ := hkey V₁ hV₁
        obtain ⟨-, -, -, -, -, -, -, -, h4U⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
        have hM : J₀ V₁ = J₀ V₂ := Sec6Gen.eq_of_le_of_le hΩ (hJ₀ V₁ hV₁).1 (hJ₀ V₂ hV₂).1
          (Sec6Gen.isPGroup_of_mem_USet hΩ hU) h4U inf_le_left (h' ▸ inf_le_left)
        have hVV₂ : V₂ ≤ secOf Ω w (J₀ V₁) := hM ▸ hVJ₀ V₂ hV₂
        exact hd2 V₁ hV₁ V₂ hV₂ hne (secOf Ω w (J₀ V₁)) (secOf_mem_hullFam (hJ₀ V₁ hV₁))
          ⟨hVJ₀ V₁ hV₁, hVV₂⟩
      exact Set.ncard_le_ncard_of_injOn _ hmaps hinj (Set.toFinite _)
    have hη₁S : η₁ ∈ etaSet (hullFam Ω w) (S₁ : Subgroup ↥(coreHull Ω w)) :=
      ⟨fun V hV => ⟨hV.1, hV.2.1⟩, hη₁dist, hmax⟩
    have hinv : ∀ s ∈ (S₁ : Subgroup ↥(coreHull Ω w)), ∀ V ∈ η₁, conjSub s V ∈ η₁ := by
      intro s hs V hV
      refine ⟨USet.conj hΛ.conjInvariant hV.1 s, ?_, ?_⟩
      · have := conjSub_mono (n := s) hV.2.1
        rwa [conjSub_eq_self_of_mem hs] at this
      · have e := conjSub_map (secEmb Ω w) s V
        rw [← e]
        have := conjSub_mono (n := secEmb Ω w s) hV.2.2
        rwa [hW'n (secEmb Ω w s) (hT₁S' s hs)] at this
    have hW₁mem : (⨆ V ∈ η₁, V) ∈ WSet (hullFam Ω w) := ⟨η₁, ⟨S₁, hη₁S, hinv⟩, rfl⟩
    have hW₁S : (⨆ V ∈ η₁, V) ≤ (S₁ : Subgroup ↥(coreHull Ω w)) := iSup₂_le fun V hV => hV.2.1
    have hW₁le : (⨆ V ∈ η₁, V) ≤ (conjSub x W).comap (secEmb Ω w) := iSup₂_le fun V hV =>
      (Subgroup.map_le_iff_le_comap).mp hV.2.2
    refine ⟨_, hW₁mem, hW₁S, ?_, ?_⟩
    · intro s hs
      rw [conjSub_iSup₂]
      apply le_antisymm
      · exact iSup₂_le fun U hU => le_iSup₂_of_le _ (hinv s hs U hU) le_rfl
      · refine iSup₂_le fun U hU => ?_
        have hU' : conjSub s⁻¹ U ∈ η₁ :=
          hinv s⁻¹ ((S₁ : Subgroup ↥(coreHull Ω w)).inv_mem hs) U hU
        have : U = conjSub s (conjSub s⁻¹ U) := (conjSub_conjSub_inv s U).symm
        rw [this]
        exact le_iSup₂_of_le (conjSub s⁻¹ U) hU' le_rfl
    · intro M₁ hM₁ hMW
      obtain ⟨M, hM, rfl⟩ := exists_of_mem_hullFam hM₁
      have hmapU : (secOf Ω w M ⊓ (⨆ V ∈ η₁, V)).map (secEmb Ω w) ∈ USet Ω :=
        hullpf_map_mem_USet hc2 hMW
      obtain ⟨-, -, -, -, -, -, -, -, h4V⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hmapU
      have hVS' : (secOf Ω w M ⊓ (⨆ V ∈ η₁, V)).map (secEmb Ω w) ≤ (S' : Subgroup G) :=
        (Subgroup.map_mono (inf_le_right.trans hW₁S)).trans hS₁S'
      have hVM : (secOf Ω w M ⊓ (⨆ V ∈ η₁, V)).map (secEmb Ω w) ≤ M :=
        (hullpf_map_le hM inf_le_left).trans (TwinADescent.coreAt_le_left w M)
      have hc := Subgroup.card_le_of_le (le_inf hVM hVS')
      have hMW' : M ⊓ conjSub x W ∈ USet Ω :=
        inf_W_mem_USet_of_card hΩ hW'mem hW'S hM.1 (by omega)
      have hC := hCW M hM.1 hMW'
      intro J₁ hJ₁ R₁ R₂ hR₁ hR₁M hR₁S hR₂ hR₂J hR₂S hcomm a haR haW ha1 ha2
      obtain ⟨J₀, hJ₀, rfl, hJ₀K⟩ := exists_lift_kPerp hΩ hc2 hM hJ₁
      have hcomm' : Commutes (R₁.map (secEmb Ω w)) (R₂.map (secEmb Ω w)) ∨
          R₂.map (secEmb Ω w) = R₁.map (secEmb Ω w) := by
        rcases hcomm with h | h
        · refine Or.inl ?_
          rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
          rw [← map_mul, ← map_mul, h x hx y hy]
        · exact Or.inr (by rw [h])
      have haG : secEmb Ω w a ∈ R₁.map (secEmb Ω w) ⊔ R₂.map (secEmb Ω w) := by
        have h1 : secEmb Ω w a ∈ (R₁ ⊔ R₂).map (secEmb Ω w) := ⟨a, haR, rfl⟩
        rwa [Subgroup.map_sup] at h1
      have hC' := hC J₀ hJ₀K _ _ (hullpf_map_mem_RSet hc2 hR₁)
        ((hullpf_map_le hM hR₁M).trans (TwinADescent.coreAt_le_left w M))
        ((Subgroup.map_mono hR₁S).trans hS₁S') (hullpf_map_mem_RSet hc2 hR₂)
        ((hullpf_map_le hJ₀ hR₂J).trans (TwinADescent.coreAt_le_left w J₀))
        ((Subgroup.map_mono hR₂S).trans hS₁S') hcomm' (secEmb Ω w a) haG (hW₁le haW)
        (fun h => ha1 (hι (h.trans (map_one (secEmb Ω w)).symm)))
        (by rw [← map_mul, ha2, map_one])
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      have hy' : secEmb Ω w y ∈ Subgroup.centralizer ({secEmb Ω w a} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hy]
      exact Subgroup.mem_comap.mpr (hC' hy')

end HullPf

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
