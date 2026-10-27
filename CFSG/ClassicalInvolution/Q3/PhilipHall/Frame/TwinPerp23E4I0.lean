module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEHullKey
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Transport217
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent3Fam

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.E4I

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
open CFSG.CGT.PushingUpLit.SolKNA.R4.ThmE CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement


section Hull

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {w : G}

theorem exists_sylow_hull (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers w))
    {S' : Sylow 2 G} (hS'w : (S' : Subgroup G) ≤ Subgroup.centralizer ({w} : Set G)) :
    ∃ S₁ : Sylow 2 ↥(coreHull Ω w),
      (S₁ : Subgroup ↥(coreHull Ω w)).map (secEmb Ω w) ≤ (S' : Subgroup G) := by
  set X := Subgroup.centralizer ({w} : Set G) with hX
  set L : Subgroup G := (coreHull Ω w).map X.subtype with hL
  have hLX : L ≤ X := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hXn : X ≤ Subgroup.normalizer (L : Set G) := by
    intro x hx
    apply mem_normalizer_of_conjSub_eq
    have h := conjSub_map X.subtype (⟨x, hx⟩ : ↥X) (coreHull Ω w)
    rw [conjSub_coreHull hΩ hc2] at h
    exact h
  have hV : IsSylow2In (S' : Subgroup G) X :=
    ⟨hS'w, S'.isPGroup', fun V _ hV2 hle => S'.is_maximal' hV2 hle⟩
  have hsyl : IsSylow2In ((S' : Subgroup G) ⊓ L) L :=
    isSylow2In_inf_of_le_normalizer hV hLX hXn
  set P₁ : Subgroup ↥(coreHull Ω w) := (S' : Subgroup G).comap (secEmb Ω w) with hP₁
  have hP₁2 : IsPGroup 2 ↥P₁ := S'.isPGroup'.comap_of_injective _ secEmb_injective
  have hmap : P₁.map (secEmb Ω w) = (S' : Subgroup G) ⊓ L := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, x.1, x.2, rfl⟩
    · rintro ⟨hyS, z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, hyS, rfl⟩
  refine ⟨⟨P₁, hP₁2, fun {Q} hQ hle => ?_⟩, ?_⟩
  · refine le_antisymm (fun x hx => ?_) hle
    have hQL : Q.map (secEmb Ω w) ≤ L := by
      rintro _ ⟨q, -, rfl⟩
      exact ⟨q, q.2, rfl⟩
    have hsub : (S' : Subgroup G) ⊓ L ≤ Q.map (secEmb Ω w) := by
      rw [← hmap]
      exact Subgroup.map_mono hle
    have heq := hsyl.2.2 _ hQL (hQ.map _) hsub
    have hx' : secEmb Ω w x ∈ Q.map (secEmb Ω w) := ⟨x, hx, rfl⟩
    rw [heq] at hx'
    exact hx'.1
  · show P₁.map (secEmb Ω w) ≤ (S' : Subgroup G)
    rw [hmap]
    exact inf_le_left

theorem hull_cover (hΩ : HypOmegaGen Ω)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hc2 : IsPGroup 2 (Subgroup.zpowers w)) {S' : Sylow 2 G} {W' : Subgroup G}
    (hW' : W' ∈ WSet Ω) (hW'S : W' ≤ (S' : Subgroup G))
    (hNw : Subgroup.normalizer (W' : Set G) ≤ Subgroup.centralizer ({w} : Set G))
    {U : Subgroup G} (hU : U ∈ USet Ω) (hUW : U ≤ W') :
    ∃ J ∈ tqMembers3 Ω w, ∃ T : Subgroup G, IsSylow2In T J ∧
      T ≤ Subgroup.centralizer ({w} : Set G) ∧ T ∈ RSet Ω ∧ U ≤ T ∧
      U ≤ TwinADescent.coreAt w J ∧
      (U.subgroupOf (Subgroup.centralizer ({w} : Set G))).subgroupOf (coreHull Ω w) ∈
        USet (hullFam Ω w) := by
  obtain ⟨J, hJ, hUJ⟩ := Sec6Gen.exists_member_of_mem_USet hΩ hU
  have hUS : U ≤ (S' : Subgroup G) := hUW.trans hW'S
  obtain ⟨T, hTD, hTJ⟩ := Q3CL.Thompson.exists_sylow_mem_DSet hΩ hW' hW'S hJ hU hUJ hUS
  have hTc : T ≤ Subgroup.centralizer ({w} : Set G) := hTD.2.trans hNw
  have hJtq : J ∈ tqMembers3 Ω w :=
    ⟨hJ, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ ⟨T, hTJ, hTc⟩⟩
  have hW2 : IsPGroup 2 ↥W' := isPGroup_of_mem_WSet hW'
  have hTn : T ≤ Subgroup.normalizer ((J ⊓ W' : Subgroup G) : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hTJ.1 ht), hTD.2 ht⟩
  have hJW2 : IsPGroup 2 ↥(J ⊓ W') := hW2.to_inf_right
  have hsup : IsPGroup 2 ↥(T ⊔ (J ⊓ W')) := hTJ.2.1.to_sup_of_normal_right' hJW2 hTn
  have hTeq : T ⊔ (J ⊓ W') = T := hTJ.2.2 _ (sup_le hTJ.1 inf_le_left) hsup le_sup_left
  have hUT : U ≤ T := (le_inf hUJ hUW).trans (hTeq ▸ le_sup_right)
  have hP : IsSylow2In T (TwinADescent.coreAt w J) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hJtq.2).mpr ⟨hTJ, hTc⟩
  obtain ⟨R', -, J', hJ', hR'J', hUR', hcyc, hcard, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  have hU2 : IsPGroup 2 ↥U := Sec6Gen.isPGroup_of_mem_USet hΩ hU
  have hJJ' : J' = J := Sec6Gen.eq_of_le_of_le hΩ hJ' hJ hU2 h4 (hUR'.trans hR'J'.1) hUJ
  have hR'J : IsSylow2In R' J := hJJ' ▸ hR'J'
  have hTcard : Nat.card ↥T = 2 * Nat.card ↥U := by rw [hTJ.natCard_eq hR'J, hcard]
  have hidx : U.relIndex T = 2 := AscAET.relIndex_eq_two_of_card hUT hTcard
  exact ⟨J, hJtq, T, hTJ, hTc, mem_RSet_of_isSylow2In hJ hTJ, hUT, hUT.trans hP.1,
    hullpf_mem_USet_hullFam hΩ hc2 hJtq hP hUT hcyc hidx⟩

theorem le_rLayer_of_mem_WSet (hΩ : HypOmegaGen Ω)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hc2 : IsPGroup 2 (Subgroup.zpowers w)) {S' : Sylow 2 G} {W' : Subgroup G}
    (hW' : W' ∈ WSet Ω) (hW'S : W' ≤ (S' : Subgroup G))
    (hNw : Subgroup.normalizer (W' : Set G) ≤ Subgroup.centralizer ({w} : Set G)) :
    W' ≤ rLayer Ω w := by
  obtain ⟨η, ⟨S₀, hη, -⟩, hWη⟩ := id hW'
  rw [hWη]
  refine iSup₂_le fun U hU => ?_
  have hUW : U ≤ W' := by rw [hWη]; exact le_iSup₂_of_le U hU le_rfl
  obtain ⟨J, -, T, -, hTc, hTR, hUT, -⟩ := hull_cover hΩ h2 hc2 hW' hW'S hNw (hη.1 hU).1 hUW
  exact hUT.trans (le_iSup₂_of_le T hTR (le_iSup (fun _ : T ≤ Subgroup.centralizer ({w} : Set G) => T) hTc))

theorem wHull_mem (hΩ : HypOmegaGen Ω)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hc2 : IsPGroup 2 (Subgroup.zpowers w)) {S' : Sylow 2 G} {W' : Subgroup G}
    (hW' : W' ∈ WSet Ω) (hW'S : W' ≤ (S' : Subgroup G))
    (hW'n : ∀ s ∈ (S' : Subgroup G), conjSub s W' = W') (hwW : w ∈ W')
    (hNw : Subgroup.normalizer (W' : Set G) ≤ Subgroup.centralizer ({w} : Set G))
    {S₁ : Sylow 2 ↥(coreHull Ω w)}
    (hS₁S' : (S₁ : Subgroup ↥(coreHull Ω w)).map (secEmb Ω w) ≤ (S' : Subgroup G)) :
    W'.comap (secEmb Ω w) ∈ WSet (hullFam Ω w) := by
  classical
  have hwS : w ∈ (S' : Subgroup G) := hW'S hwW
  have hι : Function.Injective (secEmb Ω w) := secEmb_injective
  have hΛ : HypOmegaGen (hullFam Ω w) :=
    hypOmegaGen_restrict (TwinADescent.hypOmegaGen_coreFamily hΩ hc2) (coreHull Ω w)
  have hdist := TwinThmEW.inDistinct_canonical hΩ hW'
  have hT₁S' : ∀ y : ↥(coreHull Ω w), y ∈ (S₁ : Subgroup ↥(coreHull Ω w)) →
      secEmb Ω w y ∈ (S' : Subgroup G) := fun y hy => hS₁S' ⟨y, hy, rfl⟩
  set η₁ : Set (Subgroup ↥(coreHull Ω w)) :=
    {V | V ∈ USet (hullFam Ω w) ∧ V ≤ (S₁ : Subgroup ↥(coreHull Ω w)) ∧
      V.map (secEmb Ω w) ≤ W'} with hη₁def
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
    have hkey : ∀ V ∈ η₂, J₀ V ⊓ W' ∈ USet Ω ∧
        J₀ V ⊓ W' ≤ TwinADescent.coreAt w (J₀ V) ∧
        ((J₀ V ⊓ W').subgroupOf (Subgroup.centralizer ({w} : Set G))).subgroupOf
          (coreHull Ω w) ∈ USet (hullFam Ω w) := fun V hV =>
      hullpf_key hΩ hc2 hW' hW'S hwS hS₁S' (hJ₀ V hV) (hsub hV).1 (hsub hV).2 (hVJ₀ V hV)
    have hmaps : Set.MapsTo (fun V => ((J₀ V ⊓ W').subgroupOf
        (Subgroup.centralizer ({w} : Set G))).subgroupOf (coreHull Ω w)) η₂ η₁ := by
      intro V hV
      obtain ⟨-, hUle, hUΛ⟩ := hkey V hV
      refine ⟨hUΛ, ?_, ?_⟩
      · intro y hy
        exact hullpf_mem_sylow_of_mem hS₁S'
          (hW'S (Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hy)).2)
      · rw [hullpf_map_lift (hJ₀ V hV) hUle]
        exact inf_le_right
    have hinj : Set.InjOn (fun V => ((J₀ V ⊓ W').subgroupOf
        (Subgroup.centralizer ({w} : Set G))).subgroupOf (coreHull Ω w)) η₂ := by
      intro V₁ hV₁ V₂ hV₂ h
      by_contra hne
      have h' : J₀ V₁ ⊓ W' = J₀ V₂ ⊓ W' := by
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
  have hW₁le : (⨆ V ∈ η₁, V) ≤ W'.comap (secEmb Ω w) :=
    iSup₂_le fun V hV => (Subgroup.map_le_iff_le_comap).mp hV.2.2
  have hcov : ∀ U : Subgroup G, U ∈ USet Ω → U ≤ W' →
      U ≤ (⨆ V ∈ η₁, V).map (secEmb Ω w) := by
    intro U hU hUW
    obtain ⟨J, hJ, T, hTJ, hTc, hTR, hUT, hUcore, hsec⟩ :=
      hull_cover hΩ h2 hc2 hW' hW'S hNw hU hUW
    have hmem : (U.subgroupOf (Subgroup.centralizer ({w} : Set G))).subgroupOf
        (coreHull Ω w) ∈ η₁ := by
      refine ⟨hsec, ?_, ?_⟩
      · intro y hy
        exact hullpf_mem_sylow_of_mem hS₁S'
          (hW'S (hUW (Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hy))))
      · rw [hullpf_map_lift hJ hUcore]
        exact hUW
    calc U = ((U.subgroupOf (Subgroup.centralizer ({w} : Set G))).subgroupOf
          (coreHull Ω w)).map (secEmb Ω w) := (hullpf_map_lift hJ hUcore).symm
      _ ≤ _ := Subgroup.map_mono (le_iSup₂_of_le _ hmem le_rfl)
  have hWle : W' ≤ (⨆ V ∈ η₁, V).map (secEmb Ω w) := by
    obtain ⟨η, ⟨S₀, hη, -⟩, hWη⟩ := id hW'
    rw [hWη]
    refine iSup₂_le fun U hU => hcov U (hη.1 hU).1 ?_
    rw [hWη]
    exact le_iSup₂_of_le U hU le_rfl
  have hge : W'.comap (secEmb Ω w) ≤ ⨆ V ∈ η₁, V := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := hWle (Subgroup.mem_comap.mp hx)
    rwa [← hι hax]
  rwa [le_antisymm hge hW₁le |>.symm] at hW₁mem

end Hull

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.E4I
