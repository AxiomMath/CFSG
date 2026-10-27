module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2Dich
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Sec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL



section Tw

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem twin_lifts_in_section (hP : TL4.TightBelowRPlus 3 n) (h : PerpHypS n Y R S t) {c : Y}
    (hc2 : c * c = 1) (hc1 : c ≠ 1) (hno : SecNoExit R c) {J₁ J₂ : Subgroup Y}
    (hJ₁ : J₁ ∈ Om R) (hJ₂ : J₂ ∈ Om R) (hne : J₂ ≠ J₁) {w : Y}
    (hw₁ : IsUniqueInvolution J₁ w) (hw₂ : IsUniqueInvolution J₂ w) {T₁ T₂ : Subgroup Y}
    (hT₁ : IsSylow2In T₁ J₁) (hT₂ : IsSylow2In T₂ J₂)
    (hT₁c : T₁ ≤ Subgroup.centralizer ({c} : Set Y)) (hT₂c : T₂ ≤ Subgroup.centralizer ({c} : Set Y))
    (hwT₁ : w ∈ T₁) (hwT₂ : w ∈ T₂) :
    ∃ L₁ L₂ : Subgroup (SecQ R c), L₁ ∈ liftFam (TwinDisc.secFam (Om R) c) ∧
      L₂ ∈ liftFam (TwinDisc.secFam (Om R) c) ∧ L₁ ≠ L₂ ∧
      ∃ wb : SecQ R c, IsUniqueInvolution L₁ wb ∧ IsUniqueInvolution L₂ wb := by
  have hC := CoreData.of_S h.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hc2' : IsPGroup 2 (Subgroup.zpowers c) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hKtq : J₁ ∈ tqMembers3 (Om R) c :=
    ⟨hJ₁, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₁ ⟨T₁, hT₁, hT₁c⟩⟩
  have hK'tq : J₂ ∈ tqMembers3 (Om R) c :=
    ⟨hJ₂, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₂ ⟨T₂, hT₂, hT₂c⟩⟩
  have htC : w ∈ Subgroup.centralizer ({c} : Set Y) := hT₁c hwT₁
  have ht2 : w * w = 1 := hw₁.sq
  have hsq' : (⟨w, htC⟩ : ↥(Subgroup.centralizer ({c} : Set Y))) * ⟨w, htC⟩ = 1 :=
    Subtype.ext ht2
  have hS := p23_q8Section h hc2
  have hlt := secQ_card_lt h hc1
  obtain ⟨h2X, hl, -⟩ := lifts_of_noExit hP hlt hS hno
  have hq8 : ∀ J₀ ∈ TwinDisc.secFam (Om R) c, Nonempty (↥J₀ ≃* QuaternionGroup 2) :=
    fun J₀ hJ₀ => hS.q8 J₀ hJ₀ J₀ ⟨le_rfl, h2X J₀ hJ₀, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  have hodd : ∀ K₀ ∈ TwinDisc.secFam (Om R) c,
      ∀ w : ↥(coreHull (Om R) c) ⧸ classicalInvolutionOddCore ↥(coreHull (Om R) c),
      IsUniqueInvolution K₀ w → Balance.oddCoreIn (Subgroup.centralizer ({w} : Set _)) = ⊥ :=
    fun K₀ hK₀ w hw => (hno K₀ hK₀ w hw).1
  have hcoreK : w ∈ TwinADescent.coreAt c J₁ :=
    le_tightCore_of_isPGroup (le_inf hT₁.1 hT₁c) hT₁.2.1 hwT₁
  have hcoreK' : w ∈ TwinADescent.coreAt c J₂ :=
    le_tightCore_of_isPGroup (le_inf hT₂.1 hT₂c) hT₂.2.1 hwT₂
  set wH : ↥(coreHull (Om R) c) :=
    ⟨⟨w, htC⟩, le_coreHull hKtq (Subgroup.mem_subgroupOf.mpr hcoreK)⟩ with hwH
  have hwH2 : wH * wH = 1 := Subtype.ext hsq'
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) c)) with hπ
  have hmemK : π wH ∈ secImg (Om R) c J₁ :=
    ⟨wH, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hcoreK), rfl⟩
  have hmemK' : π wH ∈ secImg (Om R) c J₂ :=
    ⟨wH, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hcoreK'), rfl⟩
  have hπt : ∀ J₀ : Subgroup Y, J₀ ∈ tqMembers3 (Om R) c → IsUniqueInvolution J₀ w →
      π wH ∈ secImg (Om R) c J₀ → IsUniqueInvolution (secImg (Om R) c J₀) (π wH) := by
    intro J₀ hJ₀ hJ₀t hmem
    obtain ⟨L, u', hL⟩ := hl _ (secImg_mem_secFam hJ₀)
    have htb1 : π wH ≠ 1 := by
      intro h1
      have h1' : wH ∈ classicalInvolutionOddCore ↥(coreHull (Om R) c) :=
        (QuotientGroup.eq_one_iff _).mp h1
      have hord : orderOf wH = 2 := by
        refine orderOf_eq_prime (by rw [pow_two]; exact hwH2) ?_
        intro e
        apply hJ₀t.ne_one
        have := congrArg (fun v : ↥(coreHull (Om R) c) =>
          (((v : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y)) e
        simpa [hwH] using this
      have hdvd := Subgroup.orderOf_dvd_natCard _ h1'
      rw [hord] at hdvd
      exact absurd ((CFSG.ComponentClassification.OddCore.odd_card _).of_dvd_nat hdvd) (by decide)
    have htb2 : π wH * π wH = 1 := by rw [← map_mul, hwH2, map_one]
    have hu : π wH = u' := (hL.inv.unique _ hmem htb2).resolve_left htb1
    rw [hu]
    exact hL.inv
  have hπtK := hπt _ hKtq hw₁ hmemK
  have hπtK' := hπt _ hK'tq hw₂ hmemK'
  have hne_img : secImg (Om R) c J₁ ≠ secImg (Om R) c J₂ := by
    intro heq
    have hΛ : HypOmegaGen (cFam (Om R) c) := TwinADescent.hypOmegaGen_coreFamily hΩ hc2'
    have hcore_ne : (TwinADescent.coreAt c J₁).subgroupOf (Subgroup.centralizer ({c} : Set Y)) ≠
        (TwinADescent.coreAt c J₂).subgroupOf (Subgroup.centralizer ({c} : Set Y)) := by
      intro he
      have := congrArg (Subgroup.map (Subgroup.centralizer ({c} : Set Y)).subtype) he
      rw [Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c J₁),
        Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c J₂)] at this
      exact hne (eq_of_coreAt_eq hΩ hc2' hKtq hK'tq this).symm
    exact TwinExitPf2.false_of_imgOf_eq hΛ
      ⟨TwinADescent.coreAt c J₁, TwinADescent.coreAt_mem_coreFamily hKtq,
        TwinADescent.coreAt_le_centralizer c J₁, rfl⟩
      ⟨TwinADescent.coreAt c J₂, TwinADescent.coreAt_mem_coreFamily hK'tq,
        TwinADescent.coreAt_le_centralizer c J₂, rfl⟩
      hcore_ne
      (isUniqueInvolution_subgroupOf
        (isUniqueInvolution_coreAt_of_tq hΩ hc2' hKtq hw₁)
        (TwinADescent.coreAt_le_centralizer c J₁))
      (isUniqueInvolution_subgroupOf
        (isUniqueInvolution_coreAt_of_tq hΩ hc2' hK'tq hw₂)
        (TwinADescent.coreAt_le_centralizer c J₂))
      (le_coreHull hKtq) (le_coreHull hK'tq) heq
  have hJ2 := h2X _ (secImg_mem_secFam hKtq)
  have hJ'2 := h2X _ (secImg_mem_secFam hK'tq)
  have hl₁ : ∃ L, IsLiftOf (secImg (Om R) c J₁) L (π wH) := by
    obtain ⟨L, u, hL⟩ := hl _ (secImg_mem_secFam hKtq)
    have : u = π wH := hL.inv.eq hπtK
    exact ⟨L, this ▸ hL⟩
  have hl₂ : ∃ L, IsLiftOf (secImg (Om R) c J₂) L (π wH) := by
    obtain ⟨L, u, hL⟩ := hl _ (secImg_mem_secFam hK'tq)
    have : u = π wH := hL.inv.eq hπtK'
    exact ⟨L, this ▸ hL⟩
  have hO := hodd _ (secImg_mem_secFam hKtq) (π wH) hπtK
  have hO' := hodd _ (secImg_mem_secFam hK'tq) (π wH) hπtK'
  obtain ⟨L₁, L₂, hL₁, hL₂, hJ₁L, hJ₂L, hLne, -, -, -⟩ :=
    TwinExitPf6.exists_lifted_pair hS.hyp (secImg_mem_secFam hKtq) (secImg_mem_secFam hK'tq)
      hJ2 hJ'2 (hq8 _ (secImg_mem_secFam hKtq)) (hq8 _ (secImg_mem_secFam hK'tq)) hπtK hπtK'
      hl₁ hl₂ hO hne_img (MulEquiv.refl _) (fun _ _ => rfl) (fun _ _ => rfl)
  have hm₁ : L₁ ∈ liftFam (TwinDisc.secFam (Om R) c) := by
    have := satU_mem_liftFam (secImg_mem_secFam hKtq) (⟨hπtK, hJ₁L, hL₁⟩ :
      IsLiftOf (secImg (Om R) c J₁) L₁ (π wH))
    rwa [TwinExitPf6.satU_eq_of_oddCore_eq_bot hO] at this
  have hm₂ : L₂ ∈ liftFam (TwinDisc.secFam (Om R) c) := by
    have := satU_mem_liftFam (secImg_mem_secFam hK'tq) (⟨hπtK', hJ₂L, hL₂⟩ :
      IsLiftOf (secImg (Om R) c J₂) L₂ (π wH))
    rwa [TwinExitPf6.satU_eq_of_oddCore_eq_bot hO'] at this
  exact ⟨L₁, L₂, hm₁, hm₂, hLne, π wH, isUniqueInvolution_liftFam_of_le hm₁ hπtK hJ₁L,
    isUniqueInvolution_liftFam_of_le hm₂ hπtK' hJ₂L⟩

theorem liftFam_transitive (h : PerpHypS n Y R S t) {c : Y} (hc2 : c * c = 1)
    (hc1 : c ≠ 1) (hP : TL4.TightBelowRPlus 3 n)
    (hne : (TwinDisc.secFam (Om R) c).Nonempty) (hno : SecNoExit R c)
    (htr : ∀ K ∈ TwinDisc.secFam (Om R) c, ∀ L ∈ TwinDisc.secFam (Om R) c,
      ∃ g : SecQ R c, conjSub g K = L) :
    ∀ K ∈ liftFam (TwinDisc.secFam (Om R) c), ∀ L ∈ liftFam (TwinDisc.secFam (Om R) c),
      ∃ g : SecQ R c, conjSub g K = L := by
  have hS := p23_q8Section h hc2
  obtain ⟨-, hl, -, -⟩ := lieDecomp_of_noExit (n := n) (CoreData.of_S h.core).below hP
    (secQ_card_lt h hc1) hS hne hno
  obtain ⟨K₀, hK₀⟩ := hne
  obtain ⟨L₀, u₀, hL₀⟩ := hl K₀ hK₀
  have hM₀ := satU_mem_liftFam hK₀ hL₀
  have ht := liftFam_trans hS.hyp hM₀ hL₀.le_sat (fun J' hJ' => htr K₀ hK₀ J' hJ')
  intro K hK L hL
  obtain ⟨g₁, h₁⟩ := ht K hK
  obtain ⟨g₂, h₂⟩ := ht L hL
  exact ⟨g₂ * g₁⁻¹, by rw [conjSub_mul, ← h₁, conjSub_inv_conjSub, h₂]⟩

end Tw

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
