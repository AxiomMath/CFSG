module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf13Hyp51
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf13Sup23
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10Fam
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10Pair
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtU
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf10Pair
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3PfBase
public import CFSG.ClassicalInvolution.Q3.TL4D4NCCor

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.P24

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q8P.Asc77
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer (tqMembers exactCore)
open scoped commutatorElement
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section Inner

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

@[expose] def SecLift (Ω : Set (Subgroup G)) (c : G) (K : Subgroup G) : Prop :=
  ∃ (L : Subgroup (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)))
    (u : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)),
    IsLiftOf (secImg Ω c K) L u

theorem card_sec_lt [CoreLike G] (hc1 : c ≠ 1) :
    Nat.card (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) < Nat.card G := by
  have h1 : Nat.card (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) ≤
      Nat.card ↥(coreHull Ω c) :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h2 : Nat.card ↥(coreHull Ω c) ≤ Nat.card ↥(Subgroup.centralizer ({c} : Set G)) :=
    Subgroup.card_le_card_group _
  have h3 := TwinEdge.card_centralizer_lt_of_center CoreLike.center_eq_bot hc1
  omega

theorem liftPair_tf (hΩ : HypOmegaGen Ω) (hc2' : IsPGroup 2 (Subgroup.zpowers c))
    (hcit : CIT3Below (Nat.card G))
    (hlt : Nat.card (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) < Nat.card G)
    (hS : Q8Section (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) (secFam Ω c))
    {J J' : Subgroup G} (hJtq : J ∈ tqMembers3 Ω c) (hJ'tq : J' ∈ tqMembers3 Ω c)
    (hJne : J' ≠ J) {t : G} (htJ : IsUniqueInvolution J t) (htJ' : IsUniqueInvolution J' t)
    (htC : t ∈ Subgroup.centralizer ({c} : Set G))
    (lJ : SecLift Ω c J) (lJ' : SecLift Ω c J')
    {x : G} (hxc : x ∈ Subgroup.centralizer ({c} : Set G))
    (hxJ : x ∈ centralizerModOdd ⊤ J) (hxJ' : x ∈ centralizerModOdd ⊤ J') :
    ∃ M M' : Subgroup G,
      Q3NL.IsSectionMember3 (Subgroup.centralizer ({c} : Set G)) M t ∧
      Q3NL.IsSectionMember3 (Subgroup.centralizer ({c} : Set G)) M' t ∧
      modOdd c M ≠ modOdd c M' ∧
      (∀ a ∈ modOdd c M, ∀ b ∈ modOdd c M', a * b = b * a) ∧
      (∀ a ∈ modOdd c M, oddQuotMk c ⟨x, hxc⟩ * a = a * oddQuotMk c ⟨x, hxc⟩) ∧
      (∀ a ∈ modOdd c M', oddQuotMk c ⟨x, hxc⟩ * a = a * oddQuotMk c ⟨x, hxc⟩) ∧
      (∀ g ∈ TwinADescent.coreAt c J, g * t = t * g → g ∈ M) ∧
      (∀ g ∈ TwinADescent.coreAt c J', g * t = t * g → g ∈ M') := by
  classical
  have ht2 : t * t = 1 := htJ.sq
  have hsq' : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) * ⟨t, htC⟩ = 1 :=
    Subtype.ext ht2
  obtain ⟨L0, u0, hL0⟩ := lJ
  obtain ⟨L0', u0', hL0'⟩ := lJ'
  have hq8 : ∀ J₀ ∈ TwinDisc.secFam Ω c,
      IsPGroup 2 J₀ → Nonempty (↥J₀ ≃* QuaternionGroup 2) := fun J₀ hJ₀ hJ₀2 => by
    have hKS : IsSylow2In J₀ J₀ :=
      ⟨le_rfl, hJ₀2, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
    exact hS.q8 J₀ hJ₀ J₀ hKS
  have htcore : ∀ J₀ : Subgroup G, IsUniqueInvolution J₀ t → t ∈ TwinADescent.coreAt c J₀ := by
    intro J₀ hJ₀
    have hle : Subgroup.zpowers t ≤ J₀ ⊓ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.zpowers_le.mpr ⟨hJ₀.mem, htC⟩
    exact le_tightCore_of_isPGroup hle
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one ht2)
      (Subgroup.mem_zpowers t)
  have htH : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈
      coreHull Ω c :=
    le_coreHull hJtq (Subgroup.mem_subgroupOf.mpr (htcore J htJ))
  set tb : ↥(coreHull Ω c) ⧸
      classicalInvolutionOddCore ↥(coreHull Ω c) :=
    QuotientGroup.mk' _
      (⟨⟨t, htC⟩, htH⟩ : ↥(coreHull Ω c)) with htb
  have tbar : ∀ J₀ : Subgroup G, J₀ ∈ tqMembers3 Ω c →
      IsUniqueInvolution J₀ t →
      ∀ u' : ↥(coreHull Ω c) ⧸
        classicalInvolutionOddCore ↥(coreHull Ω c),
      IsUniqueInvolution (secImg Ω c J₀) u' →
      tb = u' := by
    intro J₀ hJ₀ hJ₀t u' hinv
    have hmem : tb ∈ secImg Ω c J₀ :=
      ⟨⟨⟨t, htC⟩, htH⟩, Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_subgroupOf.mpr (htcore J₀ hJ₀t)), rfl⟩
    have htb1 : tb ≠ 1 := by
      intro h1
      have h1' : (⟨⟨t, htC⟩, htH⟩ : ↥(coreHull Ω c)) ∈
          classicalInvolutionOddCore ↥(coreHull Ω c) :=
        (QuotientGroup.eq_one_iff _).mp h1
      have hord : orderOf (⟨⟨t, htC⟩, htH⟩ :
          ↥(coreHull Ω c)) = 2 := by
        refine orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext hsq') ?_
        intro e
        exact hJ₀t.ne_one (congrArg (fun w : ↥(coreHull Ω c) =>
          (((w : ↥(Subgroup.centralizer ({c} : Set G)))) : G)) e)
      have hdvd := Subgroup.orderOf_dvd_natCard _ h1'
      rw [hord] at hdvd
      exact absurd ((CFSG.ComponentClassification.OddCore.odd_card _).of_dvd_nat hdvd)
        (by decide)
    have htb2 : tb * tb = 1 := by
      rw [htb, ← map_mul]
      have : (⟨⟨t, htC⟩, htH⟩ : ↥(coreHull Ω c)) *
          ⟨⟨t, htC⟩, htH⟩ = 1 := Subtype.ext hsq'
      rw [this, map_one]
    exact (hinv.unique tb hmem htb2).resolve_left htb1
  have hu0 : tb = u0 := tbar J hJtq htJ u0 hL0.inv
  have hu0' : tb = u0' := tbar J' hJ'tq htJ' u0' hL0'.inv
  have hinvJ : IsUniqueInvolution (secImg Ω c J) tb :=
    hu0 ▸ hL0.inv
  have hinvJ' : IsUniqueInvolution (secImg Ω c J') tb :=
    hu0' ▸ hL0'.inv
  have hne_img : secImg Ω c J ≠
      secImg Ω c J' := by
    intro heq
    have hΛ : HypOmegaGen (cFam Ω c) :=
      TwinADescent.hypOmegaGen_coreFamily hΩ hc2'
    have hcore_ne : (TwinADescent.coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G)) ≠
        (TwinADescent.coreAt c J').subgroupOf (Subgroup.centralizer ({c} : Set G)) := by
      intro he
      have := congrArg (Subgroup.map (Subgroup.centralizer ({c} : Set G)).subtype) he
      rw [Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c J),
        Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c J')] at this
      exact hJne (eq_of_coreAt_eq hΩ hc2' hJtq hJ'tq this).symm
    exact TwinExitPf2.false_of_imgOf_eq hΛ
      ⟨TwinADescent.coreAt c J, TwinADescent.coreAt_mem_coreFamily hJtq,
        TwinADescent.coreAt_le_centralizer c J, rfl⟩
      ⟨TwinADescent.coreAt c J', TwinADescent.coreAt_mem_coreFamily hJ'tq,
        TwinADescent.coreAt_le_centralizer c J', rfl⟩
      hcore_ne
      (isUniqueInvolution_subgroupOf
        (isUniqueInvolution_coreAt_of_tq hΩ hc2' hJtq htJ)
        (TwinADescent.coreAt_le_centralizer c J))
      (isUniqueInvolution_subgroupOf
        (isUniqueInvolution_coreAt_of_tq hΩ hc2' hJ'tq htJ')
        (TwinADescent.coreAt_le_centralizer c J'))
      (le_coreHull hJtq) (le_coreHull hJ'tq) heq
  obtain ⟨hJ2, hJ'2, L₁, L₂, hL₁, hL₂, hJL₁, hJL₂, hLne, hcomm, hfix₁, hfix₂⟩ :=
    TwinExitPf10.exists_lifted_pair_Y hcit hS.hyp hS.two hS.q8 hlt hS.oddFree
      (secImg_mem_secFam hJtq) (secImg_mem_secFam hJ'tq) hne_img hinvJ hinvJ' ⟨L0, hu0 ▸ hL0⟩
      ⟨L0', hu0' ▸ hL0'⟩
      (secAut (Ω) c hΩ hc2' ⟨x, hxc⟩)
      (fun K hK => TwinExitPf10.secAut_map_secFam hΩ hc2' ⟨x, hxc⟩ hK)
      (fun hP => secAut_fix_secImg hΩ hc2' hP hxc hxJ)
      (fun hP => secAut_fix_secImg hΩ hc2' hP hxc hxJ')
  have hH : IsSubnormal (coreHull (Ω) c) ⊤ := by
    have := normal_coreHull hΩ hc2'
    exact isSubnormal_of_normal_subgroupOf le_top inferInstance
  obtain ⟨M₁, hM₁, hM₁a, hM₁b, hM₁c⟩ :=
    exists_sectionMember_of_lift3 hH (t := ⟨t, htC⟩) htH hsq' hL₁
  obtain ⟨M₂, hM₂, hM₂a, hM₂b, hM₂c⟩ :=
    exists_sectionMember_of_lift3 hH (t := ⟨t, htC⟩) htH hsq' hL₂
  have hmem₁ := fun a => mem_modOdd_iff_of_lift hΩ hc2' hM₁a hM₁b (a := a)
  have hmem₂ := fun a => mem_modOdd_iff_of_lift hΩ hc2' hM₂a hM₂b (a := a)
  refine ⟨M₁, M₂, hM₁, hM₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro heq
    have inc : ∀ l ∈ L₁, l ∈ L₂ := by
      intro l hl1
      have h1 : secMap _ c hΩ hc2' l ∈ modOdd c M₁ := (hmem₁ _).2 ⟨l, hl1, rfl⟩
      rw [heq] at h1
      obtain ⟨l₂, hl₂, he⟩ := (hmem₂ _).1 h1
      rw [← secMap_injective hΩ hc2' he]
      exact hl₂
    have inc' : ∀ l ∈ L₂, l ∈ L₁ := by
      intro l hl2
      have h1 : secMap _ c hΩ hc2' l ∈ modOdd c M₂ := (hmem₂ _).2 ⟨l, hl2, rfl⟩
      rw [← heq] at h1
      obtain ⟨l₁, hl₁, he⟩ := (hmem₁ _).1 h1
      rw [← secMap_injective hΩ hc2' he]
      exact hl₁
    exact hLne (le_antisymm inc inc')
  · intro a ha b hb
    obtain ⟨l₁, hl₁, rfl⟩ := (hmem₁ a).1 ha
    obtain ⟨l₂, hl₂, rfl⟩ := (hmem₂ b).1 hb
    rw [← map_mul, ← map_mul, hcomm l₁ hl₁ l₂ hl₂]
  · intro a ha
    obtain ⟨l₁, hl₁, rfl⟩ := (hmem₁ a).1 ha
    exact oddQuot_centralizes_of_fix hΩ hc2' ⟨x, hxc⟩ hfix₁ hl₁
  · intro a ha
    obtain ⟨l₂, hl₂, rfl⟩ := (hmem₂ a).1 ha
    exact oddQuot_centralizes_of_fix hΩ hc2' ⟨x, hxc⟩ hfix₂ hl₂
  · intro g hg hgt
    have hgC := TwinADescent.coreAt_le_centralizer c J hg
    have hgH : (⟨g, hgC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈
        coreHull (Ω) c :=
      le_coreHull hJtq (Subgroup.mem_subgroupOf.mpr hg)
    exact hM₁c ⟨⟨g, hgC⟩, hgH⟩ (hJL₁ ⟨⟨⟨g, hgC⟩, hgH⟩, hg, rfl⟩) (Subtype.ext hgt)
  · intro g hg hgt
    have hgC := TwinADescent.coreAt_le_centralizer c J' hg
    have hgH : (⟨g, hgC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈
        coreHull (Ω) c :=
      le_coreHull hJ'tq (Subgroup.mem_subgroupOf.mpr hg)
    exact hM₂c ⟨⟨g, hgC⟩, hgH⟩ (hJL₂ ⟨⟨⟨g, hgC⟩, hgH⟩, hg, rfl⟩) (Subtype.ext hgt)

end Inner

section Out

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}
  {K₀ K K' : Subgroup G} {b d : G} {B : Subgroup G}

theorem TwinInnerHyp.swap (X : TwinInnerHyp Ω K K' b d c B) : TwinInnerHyp Ω K' K b d c B :=
  { hK := X.hK', hK' := X.hK, hne := X.hne.symm, hb := X.hb', hb' := X.hb, htq := X.htq',
    htq' := X.htq, hB := X.hB, hbB := X.hbB, hdB := X.hdB, hcB := X.hcB,
    hgen := X.hgen, hc1 := X.hc1, hbc := X.hbc, hd1 := X.hd1, hdb := X.hdb, hd2 := X.hd2,
    hdK := by rw [sup_comm]; exact X.hdK }

theorem hyp51At_of_secLifts [CoreLike G] (hst : AscStand Ω K₀)
    (hE : CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.EIHAll (Nat.card G))
    (hq2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (X : TwinInnerHyp Ω K K' b d c B) (lK : SecLift Ω c K) (lK' : SecLift Ω c K') :
    Hyp51At B c := by
  classical
  have hΩ : HypOmegaGen Ω := hst.hyp
  have hBelow : CIT3Below (Nat.card G) := hE.1
  have hZ : Subgroup.center G = ⊥ := CoreLike.center_eq_bot
  have hcc : c * c = 1 := by rw [← pow_two]; exact X.hB.2 c X.hcB
  have hc2 : IsPGroup 2 (Subgroup.zpowers c) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hcc
  have hq : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup 2) :=
    fun M hM => forall_sylow_iso_of_exists (exists_sylow_q8 hst hM)
  have hS := q8Section_secFam hΩ hc2 hq2 hq (fun M hM => hst.aEmpty M hM)
  have hlt := card_sec_lt (Ω := Ω) X.hc1
  have hcom : ∀ x ∈ B, x ∈ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      have := X.hB.1.is_comm.comm (⟨x, hx⟩ : B) ⟨c, X.hcB⟩
      exact congrArg Subtype.val this)
  have hbC := hcom b X.hbB
  have hdC := hcom d X.hdB
  have h1 : (1 : G) ∈ Subgroup.centralizer ({c} : Set G) := Subgroup.one_mem _
  obtain ⟨M, M', hM, hM', hne, hcomm, -, -, hmM, hmM'⟩ :=
    liftPair_tf hΩ hc2 hBelow hlt hS X.htq X.htq' X.hne X.hb X.hb' hbC lK lK' h1
      (Subgroup.one_mem _) (Subgroup.one_mem _)
  have hMb : IsUniqueInvolution M b := isUniqueInvolution_of_sectionMember3 hM
  have hM'b : IsUniqueInvolution M' b := isUniqueInvolution_of_sectionMember3 hM'
  have hsnc : ¬ ({c} : Set G) ⊆ Subgroup.center G := fun h => X.hc1 (by
    have h1 : c ∈ Subgroup.center G := h (Set.mem_singleton c)
    rwa [hZ, Subgroup.mem_bot] at h1)
  refine TwinFrame.hyp51At_of_classicalOrQuiet_inner hBelow hZ TL4.d4OddAutInnerNC3_proved X.hB
    X.hgen X.hc1 X.hb.ne_one X.hbc hbC hdC (Or.inl ⟨M, hM⟩) ?_
  intro L hL hmov
  have hΦ := secData3_sFamily3 hM hM' hM
  obtain ⟨ι, -, ⟨D⟩⟩ := lieSystemMod3_of_secData3 hΦ hBelow hsnc
  obtain ⟨j, hj⟩ := exists_modOdd_le_secComp hΦ D (mem_sFamily3_one c M M' M)
  have hbj : oddQuotMk c ⟨b, hbC⟩ ∈ secComp hΦ D j := hj (oddQuotMk_mem_modOdd hMb.mem hbC)
  have hbmov : ∃ w ∈ L, oddQuotMk c ⟨b, hbC⟩ * w ≠ w * oddQuotMk c ⟨b, hbC⟩ :=
    hmov _ (oddQuotMk_mem_modOdd X.hbB hbC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers X.hB X.hcB X.hc1 X.hbB X.hb.ne_one X.hbc hbC)
  have hLj : L = secComp hΦ D j := eq_secComp_of_not_commute hΦ D hbj hL hbmov
  subst hLj
  have hM'j : modOdd c M' ≤ secComp hΦ D j :=
    Q3T7.modOdd_twin_le_secComp3 hΦ D X.hB X.hcB X.hc1 X.hbB X.hb.ne_one X.hbc hbC hmov hL
      (mem_sFamily3_two c M M' M) hM'b.mem
  have hKc : ∀ x ∈ exactCore c K, ∃ hx : x ∈ Subgroup.centralizer ({c} : Set G),
      oddQuotMk c ⟨x, hx⟩ ∈ secComp hΦ D j := by
    intro x hx
    have hxC := TwinLayer.exactCore_le_centralizer c K hx
    have hxM : x ∈ M := hmM x hx (X.hb.commute_of_mem (TwinLayer.exactCore_le_left c K hx)).symm
    exact ⟨hxC, hj (oddQuotMk_mem_modOdd hxM hxC)⟩
  have hK'c : ∀ x ∈ exactCore c K', ∃ hx : x ∈ Subgroup.centralizer ({c} : Set G),
      oddQuotMk c ⟨x, hx⟩ ∈ secComp hΦ D j := by
    intro x hx
    have hxC := TwinLayer.exactCore_le_centralizer c K' hx
    have hxM : x ∈ M' := hmM' x hx (X.hb'.commute_of_mem (TwinLayer.exactCore_le_left c K' hx)).symm
    exact ⟨hxC, hM'j (oddQuotMk_mem_modOdd hxM hxC)⟩
  set Qs : Subgroup G := ((secComp hΦ D j).comap (oddQuotMk c)).map
    (Subgroup.centralizer ({c} : Set G)).subtype with hQs
  have hle : exactCore c K ⊔ exactCore c K' ≤ Qs := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨hxC, h⟩ := hKc x hx
      exact ⟨⟨x, hxC⟩, h, rfl⟩
    · obtain ⟨hxC, h⟩ := hK'c x hx
      exact ⟨⟨x, hxC⟩, h, rfl⟩
  obtain ⟨y, hy, hyd⟩ := hle X.hdK
  have hye : y = ⟨d, hdC⟩ := Subtype.ext hyd
  rw [← hye]
  exact hy

end Out

end CFSG.ClassicalInvolution.Q8P.P24
