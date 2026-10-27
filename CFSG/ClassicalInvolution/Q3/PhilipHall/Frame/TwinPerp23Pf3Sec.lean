module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Pf3Lift
public import CFSG.ClassicalInvolution.Q3.Q3T7P25A01
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2Dich
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6Sec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL



section Std

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem fuse_stdC (hP : TL4.TightBelowRPlus 3 n) (h : PerpHypS n Y R S t) {K' : Subgroup Y}
    (hK' : K' ∈ twinSet (Om R) (tightCore R)) (hne : K' ≠ tightCore R) {c : Y} (hc2 : c * c = 1)
    (hc1 : c ≠ 1) (hno : SecNoExit R c) {R₁ R₂ : Subgroup Y}
    (hR₁ : IsSylow2In R₁ (tightCore R)) (hR₂ : IsSylow2In R₂ K')
    (hR₁c : R₁ ≤ Subgroup.centralizer ({c} : Set Y))
    (hR₂c : R₂ ≤ Subgroup.centralizer ({c} : Set Y)) (hR₁₂ : IsPGroup 2 ↥(R₁ ⊔ R₂))
    {a x b y : Y} (ha : a ∈ R₁) (hx : x ∈ R₁) (hb : b ∈ R₂) (hy : y ∈ R₂) (haa : a * a = t)
    (hxx : x * x = t) (hbb : b * b = t) (hyy : y * y = t) :
    ∃ g ∈ Subgroup.centralizer ({t} : Set Y), g ∈ Subgroup.centralizer ({c} : Set Y) ∧
      g * a * g⁻¹ = x ∧ g * b * g⁻¹ = y := by
  have hC := CoreData.of_S h.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hzK : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hzK' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hzK hK'
  have hc2' : IsPGroup 2 (Subgroup.zpowers c) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hKtq : tightCore R ∈ tqMembers3 (Om R) c :=
    ⟨hK, TwinADescent3.mem_tq_of_sylCent hΩ h2 hK ⟨R₁, hR₁, hR₁c⟩⟩
  have hK'tq : K' ∈ tqMembers3 (Om R) c :=
    ⟨hK'.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hK'.1 ⟨R₂, hR₂, hR₂c⟩⟩
  have htR₁ : t ∈ R₁ := haa ▸ R₁.mul_mem ha ha
  have htC : t ∈ Subgroup.centralizer ({c} : Set Y) := hR₁c htR₁
  have ht2 : t * t = 1 := hzK.sq
  have hsq' : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({c} : Set Y))) * ⟨t, htC⟩ = 1 :=
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
  have hcoreK : ∀ w ∈ R₁, w ∈ TwinADescent.coreAt c (tightCore R) := fun w hw =>
    le_tightCore_of_isPGroup (le_inf hR₁.1 hR₁c) hR₁.2.1 hw
  have hcoreK' : ∀ w ∈ R₂, w ∈ TwinADescent.coreAt c K' := fun w hw =>
    le_tightCore_of_isPGroup (le_inf hR₂.1 hR₂c) hR₂.2.1 hw
  have hHK : ∀ w (hw : w ∈ R₁), ∃ wH : ↥(coreHull (Om R) c),
      (((wH : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y) = w ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) c)) wH ∈
        secImg (Om R) c (tightCore R) := by
    intro w hw
    have hwC := hR₁c hw
    exact ⟨⟨⟨w, hwC⟩, le_coreHull hKtq (Subgroup.mem_subgroupOf.mpr (hcoreK w hw))⟩, rfl,
      ⟨_, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr (hcoreK w hw)), rfl⟩⟩
  have hHK' : ∀ w (hw : w ∈ R₂), ∃ wH : ↥(coreHull (Om R) c),
      (((wH : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y) = w ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) c)) wH ∈
        secImg (Om R) c K' := by
    intro w hw
    have hwC := hR₂c hw
    exact ⟨⟨⟨w, hwC⟩, le_coreHull hK'tq (Subgroup.mem_subgroupOf.mpr (hcoreK' w hw))⟩, rfl,
      ⟨_, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr (hcoreK' w hw)), rfl⟩⟩
  have hcoe : ∀ h₁ h₂ : ↥(coreHull (Om R) c),
      (((h₁ : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y) =
        (((h₂ : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y) → h₁ = h₂ :=
    fun h₁ h₂ e => Subtype.ext (Subtype.ext e)
  obtain ⟨tH, htH, htHK⟩ := hHK t htR₁
  obtain ⟨aH, haH, haHK⟩ := hHK a ha
  obtain ⟨xH, hxH, hxHK⟩ := hHK x hx
  obtain ⟨bH, hbH, hbHK⟩ := hHK' b hb
  obtain ⟨yH, hyH, hyHK⟩ := hHK' y hy
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) c)) with hπ
  have htH2 : tH * tH = 1 := hcoe _ _ (by
    show (((tH : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y) *
      (((tH : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y) = 1
    rw [htH]; exact ht2)
  have hπt : ∀ J₀ : Subgroup Y, J₀ ∈ tqMembers3 (Om R) c → IsUniqueInvolution J₀ t →
      π tH ∈ secImg (Om R) c J₀ → IsUniqueInvolution (secImg (Om R) c J₀) (π tH) := by
    intro J₀ hJ₀ hJ₀t hmem
    obtain ⟨L, u', hL⟩ := hl _ (secImg_mem_secFam hJ₀)
    have htb1 : π tH ≠ 1 := by
      intro h1
      have h1' : tH ∈ classicalInvolutionOddCore ↥(coreHull (Om R) c) :=
        (QuotientGroup.eq_one_iff _).mp h1
      have hord : orderOf tH = 2 := by
        refine orderOf_eq_prime (by rw [pow_two]; exact htH2) ?_
        intro e
        apply hJ₀t.ne_one
        have := congrArg (fun w : ↥(coreHull (Om R) c) =>
          (((w : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y)) e
        simpa [htH] using this
      have hdvd := Subgroup.orderOf_dvd_natCard _ h1'
      rw [hord] at hdvd
      exact absurd ((CFSG.ComponentClassification.OddCore.odd_card _).of_dvd_nat hdvd) (by decide)
    have htb2 : π tH * π tH = 1 := by rw [← map_mul, htH2, map_one]
    have hu : π tH = u' := (hL.inv.unique _ hmem htb2).resolve_left htb1
    rw [hu]
    exact hL.inv
  have hπtK : IsUniqueInvolution (secImg (Om R) c (tightCore R)) (π tH) := hπt _ hKtq hzK htHK
  have htR₂ : t ∈ R₂ := hbb ▸ R₂.mul_mem hb hb
  have hmem' : π tH ∈ secImg (Om R) c K' :=
    ⟨tH, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr
      (by rw [htH]; exact hcoreK' t htR₂)), rfl⟩
  have hπtK' : IsUniqueInvolution (secImg (Om R) c K') (π tH) := hπt _ hK'tq hzK' hmem'
  have hne_img : secImg (Om R) c (tightCore R) ≠ secImg (Om R) c K' := by
    intro heq
    have hΛ : HypOmegaGen (cFam (Om R) c) := TwinADescent.hypOmegaGen_coreFamily hΩ hc2'
    have hcore_ne : (TwinADescent.coreAt c (tightCore R)).subgroupOf
          (Subgroup.centralizer ({c} : Set Y)) ≠
        (TwinADescent.coreAt c K').subgroupOf (Subgroup.centralizer ({c} : Set Y)) := by
      intro he
      have := congrArg (Subgroup.map (Subgroup.centralizer ({c} : Set Y)).subtype) he
      rw [Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c (tightCore R)),
        Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c K')] at this
      exact hne (eq_of_coreAt_eq hΩ hc2' hKtq hK'tq this).symm
    exact TwinExitPf2.false_of_imgOf_eq hΛ
      ⟨TwinADescent.coreAt c (tightCore R), TwinADescent.coreAt_mem_coreFamily hKtq,
        TwinADescent.coreAt_le_centralizer c (tightCore R), rfl⟩
      ⟨TwinADescent.coreAt c K', TwinADescent.coreAt_mem_coreFamily hK'tq,
        TwinADescent.coreAt_le_centralizer c K', rfl⟩
      hcore_ne
      (isUniqueInvolution_subgroupOf
        (isUniqueInvolution_coreAt_of_tq hΩ hc2' hKtq hzK)
        (TwinADescent.coreAt_le_centralizer c (tightCore R)))
      (isUniqueInvolution_subgroupOf
        (isUniqueInvolution_coreAt_of_tq hΩ hc2' hK'tq hzK')
        (TwinADescent.coreAt_le_centralizer c K'))
      (le_coreHull hKtq) (le_coreHull hK'tq) heq
  have hJ2 := h2X _ (secImg_mem_secFam hKtq)
  have hJ'2 := h2X _ (secImg_mem_secFam hK'tq)
  have hl₁ : ∃ L, IsLiftOf (secImg (Om R) c (tightCore R)) L (π tH) := by
    obtain ⟨L, u, hL⟩ := hl _ (secImg_mem_secFam hKtq)
    have : u = π tH := hL.inv.eq hπtK
    exact ⟨L, this ▸ hL⟩
  have hl₂ : ∃ L, IsLiftOf (secImg (Om R) c K') L (π tH) := by
    obtain ⟨L, u, hL⟩ := hl _ (secImg_mem_secFam hK'tq)
    have : u = π tH := hL.inv.eq hπtK'
    exact ⟨L, this ▸ hL⟩
  have hO := hodd _ (secImg_mem_secFam hKtq) (π tH) hπtK
  have hO' := hodd _ (secImg_mem_secFam hK'tq) (π tH) hπtK'
  obtain ⟨L₁, L₂, hL₁, hL₂, hJ₁L, hJ₂L, hLne, hcomm, -, -⟩ :=
    TwinExitPf6.exists_lifted_pair hS.hyp (secImg_mem_secFam hKtq) (secImg_mem_secFam hK'tq)
      hJ2 hJ'2 (hq8 _ (secImg_mem_secFam hKtq)) (hq8 _ (secImg_mem_secFam hK'tq)) hπtK hπtK'
      hl₁ hl₂ hO hne_img (MulEquiv.refl _) (fun _ _ => rfl) (fun _ _ => rfl)
  have hm₁ : L₁ ∈ liftFam (TwinDisc.secFam (Om R) c) := by
    have := satU_mem_liftFam (secImg_mem_secFam hKtq) (⟨hπtK, hJ₁L, hL₁⟩ :
      IsLiftOf (secImg (Om R) c (tightCore R)) L₁ (π tH))
    rwa [TwinExitPf6.satU_eq_of_oddCore_eq_bot hO] at this
  have hm₂ : L₂ ∈ liftFam (TwinDisc.secFam (Om R) c) := by
    have := satU_mem_liftFam (secImg_mem_secFam hK'tq) (⟨hπtK', hJ₂L, hL₂⟩ :
      IsLiftOf (secImg (Om R) c K') L₂ (π tH))
    rwa [TwinExitPf6.satU_eq_of_oddCore_eq_bot hO'] at this
  have hhy := hypOmegaModU_liftFam hS.hyp.conjInvariant (Δ := TwinDisc.secFam (Om R) c)
  have hmulH : ∀ {u₁ u₂ u₃ : ↥(coreHull (Om R) c)},
      (((u₁ : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y) *
        (((u₂ : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y) =
        (((u₃ : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y) → u₁ * u₂ = u₃ :=
    fun e => hcoe _ _ e
  have haHaH : aH * aH = tH := hmulH (by rw [haH, htH]; exact haa)
  have hxHxH : xH * xH = tH := hmulH (by rw [hxH, htH]; exact hxx)
  have hbHbH : bH * bH = tH := hmulH (by rw [hbH, htH]; exact hbb)
  have hyHyH : yH * yH = tH := hmulH (by rw [hyH, htH]; exact hyy)
  obtain ⟨k, hkL, hk⟩ := CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7B.exists_conj_of_sq_eq hhy hm₁
    (isUniqueInvolution_liftFam_of_le hm₁ hπtK hJ₁L) (hJ₁L haHK) (hJ₁L hxHK)
    (by rw [← map_mul, haHaH]) (by rw [← map_mul, hxHxH])
  obtain ⟨ℓ, hℓL, hℓ⟩ := CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7B.exists_conj_of_sq_eq hhy hm₂
    (isUniqueInvolution_liftFam_of_le hm₂ hπtK' hJ₂L) (hJ₂L hbHK) (hJ₂L hyHK)
    (by rw [← map_mul, hbHbH]) (by rw [← map_mul, hyHyH])
  have hcm : ∀ a ∈ L₁, ∀ b ∈ L₂, b * a * b⁻¹ = a := fun a ha b hb => by
    rw [← hcomm a ha b hb]; group
  have hcm' : ∀ a ∈ L₂, ∀ b ∈ L₁, b * a * b⁻¹ = a := fun a ha b hb => by
    rw [hcomm b hb a ha]; group
  have hLC₁ : L₁ ≤ Subgroup.centralizer ({π tH} : Set _) := TwinEdge.isSubnormal_le' hL₁.subnormal
  have hLC₂ : L₂ ≤ Subgroup.centralizer ({π tH} : Set _) := TwinEdge.isSubnormal_le' hL₂.subnormal
  have hcb : k * ℓ ∈ Subgroup.centralizer ({π tH} : Set _) :=
    Subgroup.mul_mem _ (hLC₁ hkL) (hLC₂ hℓL)
  have h1 : (k * ℓ) * π aH * (k * ℓ)⁻¹ = π xH := by
    calc (k * ℓ) * π aH * (k * ℓ)⁻¹ = k * (ℓ * π aH * ℓ⁻¹) * k⁻¹ := by group
      _ = k * π aH * k⁻¹ := by rw [hcm _ (hJ₁L haHK) ℓ hℓL]
      _ = π xH := hk
  have h2 : (k * ℓ) * π bH * (k * ℓ)⁻¹ = π yH := by
    calc (k * ℓ) * π bH * (k * ℓ)⁻¹ = k * (ℓ * π bH * ℓ⁻¹) * k⁻¹ := by group
      _ = k * π yH * k⁻¹ := by rw [hℓ]
      _ = π yH := hcm' _ (hJ₂L hyHK) k hkL
  set Q : Subgroup ↥(coreHull (Om R) c) :=
    ((R₁ ⊔ R₂).subgroupOf (Subgroup.centralizer ({c} : Set Y))).subgroupOf (coreHull (Om R) c)
    with hQ
  have hQ2 : IsPGroup 2 Q := hR₁₂.comap_subtype.comap_subtype
  have hmQ : ∀ {w : Y} {wH : ↥(coreHull (Om R) c)},
      (((wH : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y) = w → w ∈ R₁ ⊔ R₂ → wH ∈ Q := by
    intro w wH e hw
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ?_)
    rw [e]; exact hw
  have hKt : ∀ {w : Y}, w ∈ tightCore R → w * t = t * w := fun hw =>
    Subgroup.mem_centralizer_singleton_iff.mp
      (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.le_centralizer_of_unique hzK hw)
  have hKt' : ∀ {w : Y}, w ∈ K' → w * t = t * w := fun hw =>
    Subgroup.mem_centralizer_singleton_iff.mp
      (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.le_centralizer_of_unique hzK' hw)
  have hcomH : ∀ {w : Y} {wH : ↥(coreHull (Om R) c)},
      (((wH : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y) = w → w * t = t * w → wH * tH = tH * wH := by
    intro w wH e hw
    exact hcoe _ _ (by
      show (((wH : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y) * (((tH : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y) =
        (((tH : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y) * (((wH : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y)
      rw [e, htH]; exact hw)
  obtain ⟨cH, hcHt, hcHa, hcHb⟩ := exists_lift_fusion (classicalInvolutionOddCore ↥(coreHull (Om R) c))
    (CFSG.ComponentClassification.OddCore.odd_card _) hQ2 hQ2 htH2
    (hmQ haH (Subgroup.mem_sup_left ha))
    (hmQ hbH (Subgroup.mem_sup_right hb)) (hmQ hxH (Subgroup.mem_sup_left hx))
    (hmQ hyH (Subgroup.mem_sup_right hy))
    (hcomH haH (hKt (hR₁.1 ha))) (hcomH hbH (hKt' (hR₂.1 hb))) (hcomH hxH (hKt (hR₁.1 hx)))
    (hcomH hyH (hKt' (hR₂.1 hy))) hcb h1 h2
  have hcoeMul : ∀ u v : ↥(coreHull (Om R) c),
      (((u * v : ↥(coreHull (Om R) c)) : ↥(Subgroup.centralizer ({c} : Set Y))) : Y) =
        (((u : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y) *
          (((v : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y) := fun _ _ => rfl
  have hcoeInv : ∀ u : ↥(coreHull (Om R) c),
      (((u⁻¹ : ↥(coreHull (Om R) c)) : ↥(Subgroup.centralizer ({c} : Set Y))) : Y) =
        (((u : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y)⁻¹ := fun _ => rfl
  refine ⟨(((cH : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y), ?_,
    (cH : ↥(Subgroup.centralizer ({c} : Set Y))).2, ?_, ?_⟩
  · have := congrArg (fun w : ↥(coreHull (Om R) c) =>
      (((w : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y)) (Subgroup.mem_centralizer_singleton_iff.mp hcHt)
    simp only [hcoeMul, htH] at this
    exact Subgroup.mem_centralizer_singleton_iff.mpr this
  · have := congrArg (fun w : ↥(coreHull (Om R) c) =>
      (((w : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y)) hcHa
    simp only [hcoeMul, hcoeInv, haH, hxH] at this
    exact this
  · have := congrArg (fun w : ↥(coreHull (Om R) c) =>
      (((w : ↥(Subgroup.centralizer ({c} : Set Y)))) : Y)) hcHb
    simp only [hcoeMul, hcoeInv, hbH, hyH] at this
    exact this

theorem fuse_std (hP : TL4.TightBelowRPlus 3 n) (h : PerpHypS n Y R S t) {K' : Subgroup Y}
    (hK' : K' ∈ twinSet (Om R) (tightCore R)) (hne : K' ≠ tightCore R) {c : Y} (hc2 : c * c = 1)
    (hc1 : c ≠ 1) (hno : SecNoExit R c) {R₁ R₂ : Subgroup Y}
    (hR₁ : IsSylow2In R₁ (tightCore R)) (hR₂ : IsSylow2In R₂ K')
    (hR₁c : R₁ ≤ Subgroup.centralizer ({c} : Set Y))
    (hR₂c : R₂ ≤ Subgroup.centralizer ({c} : Set Y)) (hR₁₂ : IsPGroup 2 ↥(R₁ ⊔ R₂))
    {a x b y : Y} (ha : a ∈ R₁) (hx : x ∈ R₁) (hb : b ∈ R₂) (hy : y ∈ R₂) (haa : a * a = t)
    (hxx : x * x = t) (hbb : b * b = t) (hyy : y * y = t) :
    ∃ g ∈ Subgroup.centralizer ({t} : Set Y), g * a * g⁻¹ = x ∧ g * b * g⁻¹ = y := by
  obtain ⟨g, hgt, -, h1, h2⟩ := fuse_stdC hP h hK' hne hc2 hc1 hno hR₁ hR₂ hR₁c hR₂c hR₁₂ ha hx hb hy
    haa hxx hbb hyy
  exact ⟨g, hgt, h1, h2⟩

end Std

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
