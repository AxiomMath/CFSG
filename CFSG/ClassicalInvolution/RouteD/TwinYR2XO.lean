module

public import CFSG.ClassicalInvolution.RouteD.TwinYR2Trans
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTwAll
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairFinal

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

section Gen

variable {p : ℕ} [Fact p.Prime]

theorem range_le_iSup_fund_of_commuting {t : StatedLieTag} {n e : ℕ}
    (hCF : CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalGeneration p t n e)
    (hne : (fundamentalSubgroups t (modelUniv t n p e Fact.out).D).Nonempty) {X : Type}
    [Group X] (ψ : (modelUniv t n p e Fact.out).K →* X) :
    ψ.range ≤ ⨆ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, R.map ψ := by
  obtain ⟨R₀, hR₀⟩ := hne
  have h := hCF R₀ hR₀ R₀ hR₀ 1 (one_mem _) 1 (one_mem _) (fun r _ => by simp)
    (fun r _ => by simp) (fun r _ => by simp) (fun r _ => by simp)
  have h1 : ∀ R : Subgroup (modelUniv t n p e Fact.out).K,
      R ≤ Subgroup.centralizer ({1} : Set (modelUniv t n p e Fact.out).K) := fun R x _ => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp
  have h2 : (⊤ : Subgroup (modelUniv t n p e Fact.out).K) ≤
      ⨆ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, R := by
    refine h.trans (iSup₂_le fun R hR => ?_)
    rw [iSup_pos (Or.inl (h1 R))]
    exact le_iSup₂_of_le R hR le_rfl
  have h3 := Subgroup.map_mono (f := ψ) h2
  rw [Subgroup.map_top, Subgroup.map_iSup] at h3
  refine h3.trans (iSup_le fun R => ?_)
  rw [Subgroup.map_iSup]
  exact iSup_le fun hR => le_iSup₂_of_le R hR le_rfl

end Gen

section XO

variable (p f : ℕ) [Fact p.Prime]

theorem twinYXOrbit : TwinYXOrbit p f := by
  intro G _ _ _ hnab K z S tY nY hrow hshape T hT clsT e J hJ hJK hJT N hN hNK hNT
  obtain ⟨hG2, hD4, hnA1⟩ := hrow.tag_facts
  have rf := LocalShapeT.twinRowFacts hshape S.odd S.five hG2 hD4 hnA1
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT2 hD4 rf.fsc S.inClass
    (CoreAssembly.mem_conjClass_self K) S.cls hshape
  have hKz : K ∈ centralizingMembers (𝒞 K) {z} :=
    ⟨CoreAssembly.mem_conjClass_self K, le_centralizer_of_isClassicalMember S.cls⟩
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  have hMemU : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → N ≠ T →
      N ∈ centralizingMembers (𝒞 K) {e.u} := fun N hN hNK hNT =>
    e.mem_centralizingMembers_u hN.1 (hKiso N hN hNK).symm (hTiso N hN hNT).symm
  obtain ⟨hfund, hadm⟩ := Exotic.admissible_of_localShapeT hshape hD4
  have hgen := range_le_iSup_fund_of_commuting
    (CFSG.ClassicalInvolution.ModelFacts.commutingFundamentalFactsFive_all S.odd tY nY f hfund
      hadm S.five) rf.nonempty d.ψ
  set H : Subgroup G := ⨆ (L : Subgroup G) (_ : L ∈ centralizingMembers (𝒞 K) {z} ∧ L ≠ K ∧
    L ≠ T), L with hH
  have hHle : ∀ L ∈ centralizingMembers (𝒞 K) {z}, L ≠ K → L ≠ T → L ≤ H :=
    fun L hL hLK hLT => le_iSup₂_of_le L ⟨hL, hLK, hLT⟩ le_rfl
  have hHY : H ≤ locLayer (𝒞 K) z := iSup₂_le fun L hL => le_centralizingLayer hL.1
  have hHu : H ≤ locLayer (𝒞 K) e.u :=
    iSup₂_le fun L hL => le_centralizingLayer (hMemU L hL.1 hL.2.1 hL.2.2)
  set A : Subgroup (locQuot (𝒞 K) z) :=
    (H.subgroupOf (locLayer (𝒞 K) z)).map (locMk (𝒞 K) z) with hA
  have hfundA : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
      R.map d.ψ ≤ A := by
    intro R hR
    obtain ⟨L, hL, hLR⟩ := mem_locFamily_iff.mp (d.mem_fam R hR)
    have hLK : L ≠ K := fun h => not_fund_of_isolated S.inClass S.p1 rf d hL
      (h ▸ hKiso) hR (h ▸ hLR)
    have hLT : L ≠ T := fun h => not_fund_of_isolated S.inClass S.p1 rf d hL
      (h ▸ hTiso) hR (h ▸ hLR)
    rw [← hLR]
    exact Subgroup.map_mono (Subgroup.comap_mono (hHle L hL hLK hLT))
  have hrangeA : d.ψ.range ≤ A := hgen.trans (iSup₂_le fun R hR => hfundA R hR)
  obtain ⟨RJ, hRJ, hJR⟩ := big_of_ne S.inClass S.exact S.p1 rf d hKz hT.mem hT.ne.symm hKiso
    hTiso hJ hJK hJT
  obtain ⟨RN, hRN, hNR⟩ := big_of_ne S.inClass S.exact S.p1 rf d hKz hT.mem hT.ne.symm hKiso
    hTiso hN hNK hNT
  obtain ⟨g, hg⟩ := rf.fsc RJ hRJ RN hRN
  obtain ⟨y', hy', hyg⟩ := Subgroup.mem_map.mp (hrangeA ⟨g, rfl⟩)
  have hy : (y' : G) ∈ H := Subgroup.mem_subgroupOf.mp hy'
  refine ⟨y', hHu hy, ?_⟩
  have hyz : (y' : G) ∈ Subgroup.centralizer ({z} : Set G) :=
    centralizingLayer_le_centralizer (𝒞 K) {z} y'.2
  have hJy : conjSub (y' : G) J ∈ centralizingMembers (𝒞 K) {z} := by
    refine ⟨S.inClass.conjInvariant _ J hJ.1, fun x hx => ?_⟩
    have h1 : (y' : G)⁻¹ * x * y' ∈ J := mem_conjSub_iff.mp hx
    have h2 := hJ.2 h1
    have e : x = (y' : G) * ((y' : G)⁻¹ * x * y') * (y' : G)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hyz h2) (inv_mem hyz)
  refine locImg_injOn S.inClass S.p1 hJy hN ?_
  rw [locImg_conjSub_layer J y', hyg, hJR, hNR, hg]
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  simp

end XO

section Main

variable {p f : ℕ} [Fact p.Prime] {P : StatedLieTag → ℕ → Prop}

theorem twinYTransitiveOn_of_visible (hΩall : HypOmegaModAll p f) (hAall : AEmptyAll p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hGenT : TwinYGenTOn p f P)
    (hVis : TwinYVisibleOn p f P) (hNC : TwinYNoCentralOn p f P) : TwinYTransitiveOn p f P :=
  twinYTransitiveOn_of_p1 hΩall hAall (twinYP1On_of_visible hΩall hAall hP4 hH hGenT hVis)
    (twinYXOrbit p f) hNC

theorem twinYTypeOn_of_visible (hΩall : HypOmegaModAll p f) (hAall : AEmptyAll p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hGenT : TwinYGenTOn p f P)
    (hVis : TwinYVisibleOn p f P) (hNC : TwinYNoCentralOn p f P) (hRank : TwinYRankOn p f P) :
    TwinYTypeOn p f P :=
  twinYTypeOn_of_local hΩall hAall hP4 hH hGenT hVis (twinYXOrbit p f) hNC hRank

theorem twinYInputs_of_visible (hΩall : HypOmegaModAll p f) (hAall : AEmptyAll p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hGenT : TwinYGenT p f)
    (hVis : TwinYVisibleOn p f fun _ _ => True) (hNC : TwinYNoCentralOn p f fun _ _ => True)
    (hRank : TwinYRank p f) (hY3 : TwinYPartner p f) (hY4 : TwinYPattern p f) :
    TwinYInputs p f :=
  ⟨twinYP1_of_visible hΩall hAall hP4 hH hGenT hVis,
    (twinYTypeOn_of_visible hΩall hAall hP4 hH hGenT.on hVis hNC hRank.on).of_true, hY3, hY4⟩

end Main

end CFSG.ClassicalInvolution.RouteD.TwinY
