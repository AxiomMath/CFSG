module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.I32Layer
public import CFSG.LocalAnalysis.ComponentClassification.OddKernelInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayerTransport
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.LocalComponent.Layer
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Aut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.QuasithinUnique.I32

open CFSG.ComponentClassification CFSG.QuasithinUnique.Id2519

section Helpers

@[expose] noncomputable def normalClosureLayer {X : Type*} [Group X] (L : Subgroup X) : Subgroup X :=
  ⨆ g ∈ oddLayerOf X, CFSG.conjugate L g

theorem isSubnormal_of_le_normal {X : Type*} [Group X] {N B : Subgroup X} [N.Normal] (hB : B ≤ N)
    (hn : N ≤ Subgroup.normalizer (B : Set X)) : CFSG.Open.IsSubnormal B ⊤ :=
  CFSG.Open.IsSubnormal.step hB ((Subgroup.normal_subgroupOf_iff_le_normalizer hB).mpr hn)
    (CFSG.Open.IsSubnormal.step le_top Subgroup.normal_subgroupOf (CFSG.Open.IsSubnormal.refl ⊤))

theorem le_of_residual_eq_top_of_map_le {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hoddKernel : Odd (Nat.card quotient.ker)) (component subnormalSubgroup : Subgroup G)
    (hgen : TwoResidual.subgroup ↥component = ⊤)
    (hsubnormal : CFSG.Open.IsSubnormal subnormalSubgroup ⊤)
    (himages : component.map quotient ≤ subnormalSubgroup.map quotient) :
    component ≤ subnormalSubgroup := by
  let image := subnormalSubgroup.map quotient
  let preimage := image.comap quotient
  let restriction : preimage →* image :=
    (quotient.domRestrict preimage).codRestrict image fun element => element.property
  have hsurjectiveRestriction : Function.Surjective restriction := by
    intro element
    obtain ⟨lift, hvalue⟩ := hsurjective element.val
    have hmem : lift ∈ preimage := by
      change quotient lift ∈ image
      rw [hvalue]
      exact element.property
    exact ⟨⟨lift, hmem⟩, Subtype.ext hvalue⟩
  have hkernel : restriction.ker = (quotient.domRestrict preimage).ker := by
    ext element
    change restriction element = 1 ↔ quotient element.val = 1
    exact ⟨fun hone => congrArg Subtype.val hone, fun hone => Subtype.ext hone⟩
  have hoddRestriction : Odd (Nat.card restriction.ker) := by
    rw [hkernel]
    exact OddKernel.odd_card_restriction_kernel quotient hoddKernel preimage
  have hsubnormalLe : subnormalSubgroup ≤ preimage := Subgroup.le_comap_map quotient _
  have hcovering : Function.Surjective
      (restriction.domRestrict (subnormalSubgroup.subgroupOf preimage)) := by
    intro element
    obtain ⟨lift, hmem, hvalue⟩ := Subgroup.mem_map.mp element.property
    exact ⟨⟨⟨lift, hsubnormalLe hmem⟩, hmem⟩, Subtype.ext hvalue⟩
  have hoddIndex := TwoResidual.odd_index_of_covering restriction hsurjectiveRestriction
    hoddRestriction (subnormalSubgroup.subgroupOf preimage) hcovering
  have hlocalChain : CFSG.Open.IsSubnormal (subnormalSubgroup.subgroupOf preimage) ⊤ :=
    Components.chain_of_mathlib_subnormal
      ((Components.mathlib_subnormal_of_chain hsubnormal Subgroup.IsSubnormal.top).subgroupOf)
  have hresidual := TwoResidual.subnormal_contains_of_odd_index
    (subnormalSubgroup.subgroupOf preimage) hlocalChain hoddIndex
  have hcomponentLe : component ≤ preimage := Subgroup.map_le_iff_le_comap.mp himages
  have hgenerated : TwoResidual.subgroup ↥(component.subgroupOf preimage) = ⊤ :=
    TwoComponentTransport.residual_eq_top_of_equiv
      (Subgroup.subgroupOfEquivOfLe hcomponentLe).symm hgen
  have hmap := TwoResidual.map_le (component.subgroupOf preimage).subtype
  rw [hgenerated] at hmap
  intro element hmem
  exact hresidual (hmap ⟨⟨⟨element, hcomponentLe hmem⟩, hmem⟩, Subgroup.mem_top _, rfl⟩)

end Helpers

section Main

local notation "𝒪(" X ")" => CFSG.Open.componentClassificationOddCore X

variable {X : Type} [Group X] [Finite X]

theorem abstract_I32 {t : X} (ht1 : t ≠ 1) (ht2 : t * t = 1) {C : Subgroup X}
    (hC : C = Subgroup.centralizer ({t} : Set X)) {L : Subgroup X} (hLC : L ≤ C)
    (hL : TwoComponents.IsTwoComponent (L.subgroupOf C)) :
    (TwoComponents.IsTwoComponent (normalClosureLayer L) ∧
        CFSG.conjugate (normalClosureLayer L) t = normalClosureLayer L) ∨
      ∃ J : Subgroup X, TwoComponents.IsTwoComponent J ∧ J ≠ CFSG.conjugate J t ∧
        normalClosureLayer L = J ⊔ CFSG.conjugate J t ∧ OddTwoIso J L := by
  classical
  let π : X →* X ⧸ 𝒪(X) := QuotientGroup.mk' 𝒪(X)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective 𝒪(X)
  have hker : Odd (Nat.card π.ker) := by
    rw [show π.ker = 𝒪(X) from QuotientGroup.ker_mk' 𝒪(X)]
    exact OddCore.odd_card X
  have hcore : CFSG.Open.componentClassificationOddCore (X ⧸ 𝒪(X)) = ⊥ :=
    OddCore.quotient_corefree X
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  have hs2 : π t * π t = 1 := by rw [← map_mul, ht2, map_one]
  let s : X ⧸ 𝒪(X) := π t
  let Cb : Subgroup (X ⧸ 𝒪(X)) := Subgroup.centralizer ({s} : Set (X ⧸ 𝒪(X)))
  have hCmap : C.map π = Cb := by
    rw [hC]
    exact OddKernelInvolutions.image_centralizer π hπ hker t hord
  let φ : ↥C →* ↥Cb := (π.comp C.subtype).codRestrict Cb (fun c => by
    rw [← hCmap]
    exact Subgroup.mem_map_of_mem π c.2)
  have hφsurj : Function.Surjective φ := by
    intro y
    have hy : (y : X ⧸ 𝒪(X)) ∈ C.map π := by rw [hCmap]; exact y.2
    obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩
  have hφker : Odd (Nat.card φ.ker) := by
    have hkerEq : φ.ker = (π.domRestrict C).ker := by
      ext element
      change φ element = 1 ↔ π element.val = 1
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [hkerEq]
    exact OddKernel.odd_card_restriction_kernel π hker C
  let L' : Subgroup ↥C := L.subgroupOf C
  let Lc : Subgroup ↥Cb := L'.map φ
  have hLc : TwoComponents.IsTwoComponent Lc :=
    OddKernelTwoComponents.image φ hφsurj hφker L' hL
  let Lb : Subgroup (X ⧸ 𝒪(X)) := Lc.map Cb.subtype
  have hLbπ : Lb = L.map π := by
    ext y
    constructor
    · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      exact ⟨l.1, hl, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨φ ⟨l, hLC hl⟩, ⟨⟨l, hLC hl⟩, hl, rfl⟩, rfl⟩
  have hlayer : Lb ≤ Layer.subgroup (X ⧸ 𝒪(X)) :=
    CFSG.ClassicalInvolution.twoComponent_le_layer_of_l2PrimeBalance
      CFSG.ClassicalInvolution.l2PrimeBalance hcore hs2 rfl hLc
  obtain ⟨Kb, hKb, hLbA'⟩ := exists_component_orbit_le hs2 rfl hLc hlayer
  have hLbA : Lb ≤ orbitSub s Kb := hLbA'
  have hLbperf : ⁅Lb, Lb⁆ = Lb := by
    have : Group.IsPerfect ↥Lc := ⟨TwoComponents.perfect hLc⟩
    have : Group.IsPerfect ↥Lb := Group.IsPerfect.map Cb.subtype
    exact Subgroup.isPerfect_iff.mp this
  have hLbne : Lb ≠ ⊥ := by
    intro hbot
    have hLcbot : Lc = ⊥ := (Subgroup.map_eq_bot_iff_of_injective Lc Cb.subtype_injective).mp hbot
    have : Nontrivial ↥Lc := TwoComponents.nontrivial hLc
    exact (Subgroup.nontrivial_iff_ne_bot Lc).mp this hLcbot
  have hLbfix : Lb ≤ Subgroup.centralizer ({s} : Set (X ⧸ 𝒪(X))) := Subgroup.map_subtype_le Lc
  have hLbsub : CFSG.Open.IsSubnormal Lb (Subgroup.centralizer ({s} : Set (X ⧸ 𝒪(X)))) := by
    have := CFSG.Quasithin.A3.subnormal_map Cb.subtype hLc.1
    rwa [Subgroup.map_top, Subgroup.range_subtype] at this
  have hnc : (⨆ y ∈ Layer.subgroup (X ⧸ 𝒪(X)), CFSG.conjugate Lb y) = orbitSub s Kb :=
    normalClosure_layer_eq hs2 hKb hLbperf hLbne hLbfix hLbA
  have hKmap : (normalClosureLayer L).map π = orbitSub s Kb := by
    rw [← hnc]
    apply le_antisymm
    · refine Subgroup.map_le_iff_le_comap.mpr (iSup₂_le fun g hg => ?_)
      rw [← Subgroup.map_le_iff_le_comap, map_conjugate, ← hLbπ]
      exact le_iSup₂_of_le (π g) hg le_rfl
    · refine iSup₂_le fun y hy => ?_
      obtain ⟨g, rfl⟩ := hπ y
      rw [hLbπ, ← map_conjugate]
      exact Subgroup.map_mono (le_iSup₂_of_le g hy le_rfl)
  have hKbs : CFSG.Open.IsComponentOf (CFSG.conjugate Kb s) ⊤ := isComponentOf_conjugate hKb s
  have hKb2 : TwoComponents.IsTwoComponent Kb :=
    TwoLayerTransport.ordinary_isTwoComponent_of_corefree hcore Kb hKb
  obtain ⟨J, hJ, hJmap⟩ := OddKernelTwoComponents.exists_lift π hπ hker Kb hKb2
  have hconjTwo : ∀ (J₀ : Subgroup X) (g : X), TwoComponents.IsTwoComponent J₀ →
      TwoComponents.IsTwoComponent (CFSG.conjugate J₀ g) := fun J₀ g h =>
    (TwoComponentTransport.equiv_iff (MulAut.conj g⁻¹) J₀).mpr h
  have hJ' : TwoComponents.IsTwoComponent (CFSG.conjugate J t) := hconjTwo J t hJ
  have hJ'map : (CFSG.conjugate J t).map π = CFSG.conjugate Kb s := by
    rw [map_conjugate, hJmap]
  have hNJ : ∀ g ∈ oddLayerOf X, g ∈ Subgroup.normalizer (J : Set X) := by
    intro g hg
    rw [← BenderBranch.conjugate_eq_iff_mem_normalizer]
    refine OddKernelTwoComponents.lift_unique π hπ hker _ _ (hconjTwo J g hJ) hJ ?_
    rw [map_conjugate, hJmap]
    exact BenderBranch.conjugate_eq_iff_mem_normalizer.mpr (layer_le_normalizer hKb hg)
  have hNJ' : ∀ g ∈ oddLayerOf X, g ∈ Subgroup.normalizer (CFSG.conjugate J t : Set X) := by
    intro g hg
    rw [← BenderBranch.conjugate_eq_iff_mem_normalizer]
    refine OddKernelTwoComponents.lift_unique π hπ hker _ _ (hconjTwo _ g hJ') hJ' ?_
    rw [map_conjugate, hJ'map]
    exact BenderBranch.conjugate_eq_iff_mem_normalizer.mpr (layer_le_normalizer hKbs hg)
  have hNA : ∀ g ∈ oddLayerOf X, g ∈ Subgroup.normalizer ((J ⊔ CFSG.conjugate J t : Subgroup X) : Set X) :=
    fun g hg => mem_normalizer_sup (hNJ g hg) (hNJ' g hg)
  have hJN : J ≤ oddLayerOf X :=
    Subgroup.map_le_iff_le_comap.mp (by rw [hJmap]; exact Layer.component_le hKb)
  have hJ'N : CFSG.conjugate J t ≤ oddLayerOf X :=
    Subgroup.map_le_iff_le_comap.mp (by rw [hJ'map]; exact Layer.component_le hKbs)
  have hAN : J ⊔ CFSG.conjugate J t ≤ oddLayerOf X := sup_le hJN hJ'N
  have hAsub : CFSG.Open.IsSubnormal (J ⊔ CFSG.conjugate J t) ⊤ :=
    isSubnormal_of_le_normal hAN hNA
  have hAmap : (J ⊔ CFSG.conjugate J t).map π = orbitSub s Kb := by
    rw [Subgroup.map_sup, hJmap, hJ'map]
    rfl
  have hres : TwoResidual.subgroup ↥L = ⊤ :=
    ((TwoComponentTransport.subgroupOf_iff L C hLC).mp hL).2.1
  have hLA : L ≤ J ⊔ CFSG.conjugate J t :=
    le_of_residual_eq_top_of_map_le π hπ hker L _ hres hAsub (by rw [hAmap, ← hLbπ]; exact hLbA)
  have hKA : normalClosureLayer L ≤ J ⊔ CFSG.conjugate J t :=
    iSup₂_le fun g hg => conjugate_le_of_mem_normalizer hLA (hNA g hg)
  have hKconj : ∀ z ∈ oddLayerOf X, CFSG.conjugate (normalClosureLayer L) z ≤ normalClosureLayer L := by
    intro z hz
    unfold normalClosureLayer
    rw [conjugate_iSup]
    refine iSup_le fun g => ?_
    rw [conjugate_iSup]
    refine iSup_le fun hg => ?_
    rw [BenderBranch.conjugate_conjugate]
    exact le_iSup₂_of_le (g * z) (Subgroup.mul_mem _ hg hz) le_rfl
  have hKsub : CFSG.Open.IsSubnormal (normalClosureLayer L) ⊤ :=
    isSubnormal_of_le_normal (hKA.trans hAN) (le_normalizer_of_conjugate_le hKconj)
  have hAK : J ⊔ CFSG.conjugate J t ≤ normalClosureLayer L :=
    sup_le
      (TwoComponentSubnormal.le_of_odd_kernel_map_le π hπ hker J _ hJ hKsub
        (by rw [hJmap, hKmap]; exact le_sup_left))
      (TwoComponentSubnormal.le_of_odd_kernel_map_le π hπ hker _ _ hJ' hKsub
        (by rw [hJ'map, hKmap]; exact le_sup_right))
  have hKeq : normalClosureLayer L = J ⊔ CFSG.conjugate J t := le_antisymm hKA hAK
  by_cases hcase : CFSG.conjugate Kb s = Kb
  ·
    left
    have hJJ : CFSG.conjugate J t = J :=
      OddKernelTwoComponents.lift_unique π hπ hker _ _ hJ' hJ (by rw [hJ'map, hJmap, hcase])
    have hKJ : normalClosureLayer L = J := by rw [hKeq, hJJ, sup_idem]
    refine ⟨hKJ ▸ hJ, ?_⟩
    rw [hKJ, hJJ]
  · right
    refine ⟨J, hJ, ?_, hKeq, ?_⟩
    · intro h
      apply hcase
      have h2 := congrArg (fun A => A.map π) h
      simp only [hJmap, hJ'map] at h2
      exact h2.symm
    ·
      obtain ⟨ψ, hψ, hRq⟩ := exists_diagonal_hom hs2 hKb hcase hLbperf hLbne hLbfix hLbA hLbsub
      have hT1 : IsSimpleGroup (↥Lb ⧸ Subgroup.center ↥Lb) := hRq.2
      have hT2 : ∃ a b : ↥Lb ⧸ Subgroup.center ↥Lb, a * b ≠ b * a :=
        ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hRq
      let ρL : ↥L →* ↥Lb := (π.domRestrict L).codRestrict Lb
        (fun l => hLbπ ▸ Subgroup.mem_map_of_mem π l.2)
      have hρL : Function.Surjective ρL := by
        intro r
        have hr : (r : X ⧸ 𝒪(X)) ∈ L.map π := hLbπ ▸ r.2
        obtain ⟨l, hl, hlr⟩ := Subgroup.mem_map.mp hr
        exact ⟨⟨l, hl⟩, Subtype.ext hlr⟩
      let ρJ : ↥J →* ↥Kb := (π.domRestrict J).codRestrict Kb
        (fun j => hJmap ▸ Subgroup.mem_map_of_mem π j.2)
      have hρJ : Function.Surjective ρJ := by
        intro r
        have hr : (r : X ⧸ 𝒪(X)) ∈ J.map π := hJmap ▸ r.2
        obtain ⟨j, hj, hjr⟩ := Subgroup.mem_map.mp hr
        exact ⟨⟨j, hj⟩, Subtype.ext hjr⟩
      have hqJ : CFSG.IsQuasisimple (↥J ⧸ CFSG.oddCore ↥J) :=
        CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr (TwoComponents.quasisimple_quotient hJ)
      have hqL : CFSG.IsQuasisimple (↥L ⧸ CFSG.oddCore ↥L) :=
        CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr
          ((TwoComponentTransport.subgroupOf_iff L C hLC).mp hL).2.2
      exact oddTwoIso_of_surjective hqJ hqL hT2
        ((QuotientGroup.mk' (Subgroup.center ↥Lb)).comp (ψ.comp ρJ))
        ((QuotientGroup.mk'_surjective _).comp (hψ.comp hρJ))
        ((QuotientGroup.mk' (Subgroup.center ↥Lb)).comp ρL)
        ((QuotientGroup.mk'_surjective _).comp hρL)

end Main

end CFSG.QuasithinUnique.I32
