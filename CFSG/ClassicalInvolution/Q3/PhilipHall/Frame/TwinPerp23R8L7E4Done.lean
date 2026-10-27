module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7E4Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7E4Tr
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7NoLayerAE7
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7NoLayerE64
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7Alpha
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ACaseB
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLAsm
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLSecV
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLTwin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7Sec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

section Ident

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)}

theorem aeIdent7_of_sectionT {n : ℕ} (hP : TL4.TightBelowRPlus 3 n) (hlt : Nat.card G < n)
    (F : Q8Pre G Φ) {K K' : Subgroup G} (hK : K ∈ Φ) (hK'tw : K' ∈ twinSet Φ K) (hne : K' ≠ K)
    (hperp : ∀ J ∈ Φ, J ≠ K → J ≤ Subgroup.normalizer (K : Set G) → J = K') {a : G}
    (ha2 : a * a = 1) (hanc : a ∉ Subgroup.center G) (haE : a ∈ Ea Φ a)
    (hns : ¬ Group.IsSolvable ↥(Ea Φ a)) (hW : ¬ ∃ W : Subgroup G, WSet Φ = {W})
    (mf5 : ModelNoLayer 5 Set.univ ((AE.aeSub 5).map (AE.mkQ 5)))
    (mf6 : ModelNoLayer 6 Set.univ ((AE.aeSub 6).map (AE.mkQ 6)))
    (mf64 : ModelNoLayer 7 AE.e64Sets AE.e64Sub)
    (hE4 : ∀ t : G, IsUniqueInvolution K t → ¬ TightInO2 t → ¬ TwinE4 G)
    (hLong : ∀ t : G, IsUniqueInvolution K t → ¬ LongFundSetE3 K t) :
    TwinDisc.ExitO2.Q8Fam G Φ ∧ Nonempty (AEIdent Φ 7) := by
  obtain ⟨t, ht⟩ := (F.hyp.omega1 K hK).1
  have hO2 : TightInO2 t := by
    by_contra hno
    rcases trichotomy_at (hP.twin rfl) hlt F hK hK'tw hne ht with h | h | h
    · exact hno h
    · exact hE4 t ht hno h
    · exact hLong t ht h
  have F' := Q8Pre.toFam_of_tightInO2 F hK ht hO2
  exact ⟨F', aeIdent7_of_concl F' (F'.thmDConcl hP.thmD.d2 hlt) hK hK'tw hne hperp ha2 hanc haE hns hW
    mf5 mf6 mf64⟩

end Ident

section Cert

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y} {Z V : Subgroup Y}

section Sec

theorem false_of_twinE4_sec (hmodel : E4TwinLayModel)
    (hB : P23E8ACaseB n) (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) (hno : ¬ SecNoExit R e) (hA5 : SecAE R u 5)
    (hA6 : SecAE R e 6) (hαb : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥)
    (h2grp : ∀ J ∈ Om R, IsPGroup 2 ↥J)
    (hOt : oddCoreOf (Subgroup.centralizer ({t} : Set Y)) = ⊥)
    (hOu : classicalInvolutionOddCore ↥(coreHull (Om R) u) = ⊥)
    (hOE : oddCoreOf (rLayer (Om R) e) = ⊥)
    (hOe : classicalInvolutionOddCore ↥(coreHull (Om R) e) = ⊥)
    (hZd : P23ZData t u e Z) {f : Y} (hf : f ∈ p23Orb Z t e) (hfe : f ≠ e)
    (hVe : V ≤ aSub R Z e) (hVf : V ≤ aSub R Z f) (hL : SecCoresTwoGroup (Om R) V)
    (F : Q8Pre (SecQuot (rLayerSub (Om R) V)) (p23SecFamV R V))
    {K₁ : Subgroup (SecQuot (rLayerSub (Om R) V))} (hK₁ : K₁ ∈ p23SecFamV R V)
    {τ : SecQuot (rLayerSub (Om R) V)} (hτ : IsUniqueInvolution K₁ τ) (hτO : ¬ TightInO2 τ) :
    ¬ TwinE4 (SecQuot (rLayerSub (Om R) V)) := by
  intro hE4
  obtain ⟨D⟩ := ZTwo.exists_cover hc hA6
  have hVZ : V ≤ Z := hVe.trans (aSub_le R Z e)
  have hfZ : f ∈ Z := hZd.orb_le hf
  have heO : e ∈ p23Orb Z t e := e_mem_orb Z t e
  have heX : e ∈ rLayerSub (Om R) V := (LemL.p23_cover_V hc hZd hVZ heO hVe).1
  have hfX : f ∈ rLayerSub (Om R) V := (LemL.p23_cover_V hc hZd hVZ hf hVf).1
  have hVefZ : V ⊔ Subgroup.zpowers e ⊔ Subgroup.zpowers f ≤ Z :=
    sup_le (sup_le hVZ (Subgroup.zpowers_le.mpr hZd.he)) (Subgroup.zpowers_le.mpr hfZ)
  obtain ⟨⟨P₀, hP₀, hP₀C'⟩, ⟨P₀', hP₀', hP₀'C'⟩⟩ := exists_sylow_cent_twins hc hZd hVefZ
  have heV' : e ∈ V ⊔ Subgroup.zpowers e ⊔ Subgroup.zpowers f :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers e))
  have hfV' : f ∈ V ⊔ Subgroup.zpowers e ⊔ Subgroup.zpowers f :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers f)
  have hVV' : V ≤ V ⊔ Subgroup.zpowers e ⊔ Subgroup.zpowers f := le_sup_left.trans le_sup_left
  have hP₀C : P₀ ≤ Subgroup.centralizer (V : Set Y) :=
    hP₀C'.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVV'))
  have hP₀'C : P₀' ≤ Subgroup.centralizer (V : Set Y) :=
    hP₀'C'.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVV'))
  have hPe : ∀ x ∈ P₀, e * x = x * e := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (hP₀C' hx) e heV'
  have hPf : ∀ x ∈ P₀, f * x = x * f := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (hP₀C' hx) f hfV'
  have hPe' : ∀ x ∈ P₀', e * x = x * e := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (hP₀'C' hx) e heV'
  have hPf' : ∀ x ∈ P₀', f * x = x * f := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (hP₀'C' hx) f hfV'
  obtain ⟨hKb, hKb', hne', ⟨zb, hzb, hzb'⟩, hperp, -⟩ :=
    p23_twin_pair_of_sylow hc hL hP₀ hP₀' hP₀C hP₀'C
  have hcent : ∀ {c : Y} (hcX : c ∈ rLayerSub (Om R) V) {Q : Subgroup Y}, (∀ x ∈ Q, c * x = x * c) →
      secImage (rLayerSub (Om R) V) Q ≤ Subgroup.centralizer
        ({QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V)) ⟨c, hcX⟩} :
          Set (SecQuot (rLayerSub (Om R) V))) :=
    fun hcX _ hcQ x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (mk_comm_secImage hcX hcQ x hx).symm
  exact false_of_twinE4_lay hmodel F hK₁ hτ hτO hE4 hKb hKb' hzb hne'
    (twin_le_normalizer F hKb hKb' hne' hzb hzb') hperp
    (not_central_e hc hZd hVZ D hf hfe hVf heX) (not_central_f hc hZd hVZ D hf hfe hVe hfX)
    (not_central_inv_mul hc hZd hVZ D hf hfe hVe hVf heX hfX)
    (hcent heX hPe) (hcent heX hPe') (hcent hfX hPf) (hcent hfX hPf')
    (not_isSolvable_Ea hc hZd hVZ D heO hVe heX) (not_isSolvable_Ea hc hZd hVZ D hf hVf hfX)
    (comm_two_of_mem_Ea hB hcit hP hc hno hA5 hA6 hαb h2grp hOt hOu hOE hOe D hZd hVZ hVe heX hfZ hfX)

end Sec

section Leaf

theorem l7NoE4T_proved {n : ℕ} (hE : TwinThmEW.ThmEQ8)
    (hD4 : TwinCentRes.ModelFactD42) (hM12 : TwinCentRes.ModelFactM12) (hT4 : TwinThmE.T4Supply)
    (hmodel : E4TwinLayModel) : L7NoE4T n := by
  intro hcit hP Y _ _ R S t K' W u e g Z f hX F K₁ hK₁ τ hτ hτO
  have hc := hX.cfg
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hα := p23Alpha_proved hD4 hM12 hT4 hcit hP
  have hαb := l7_alpha_eq_bot hE (hT4 n hcit hP) hα hcit hP hX
  have h2grp : ∀ J ∈ Om R, IsPGroup 2 ↥J := p23E8A_members_isPGroup hE hcit hP hc hX.ae5 hαb
  have hOt : oddCoreOf (Subgroup.centralizer ({t} : Set Y)) = ⊥ :=
    p23E8A_oddCoreIn_eq_bot hE hcit hP hc hX.ae5 hαb
  have hOCu : oddCoreOf (Subgroup.centralizer ({u} : Set Y)) = ⊥ := by
    have h := p23E8A_oddCoreIn_eq_bot hE hcit hP hc hX.ae5 hαb
    rw [p23E8A_oddCoreIn_eq hc hX.ae5 hαb] at h
    exact h
  have hOE : oddCoreOf (rLayer (Om R) e) = ⊥ :=
    AXV.layer_bot hΩ (AXV.ce_bot hE hα hcit hP hc hX.ae5 hαb)
  have hOe : classicalInvolutionOddCore ↥(coreHull (Om R) e) = ⊥ :=
    AXV.hull_bot hΩ (ZTwo.hc2e_of hc) (ZTwo.h2_of hc) hOE
  have hc2u : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  have hOu : classicalInvolutionOddCore ↥(coreHull (Om R) u) = ⊥ :=
    AXV.hull_bot hΩ hc2u (ZTwo.h2_of hc) (AXV.layer_bot hΩ hOCu)
  exact false_of_twinE4_sec hmodel (p23E8ACaseB_of_thmEQ8 hE) hcit hP hc hX.noExit hX.ae5 hX.ae6 hαb
    h2grp hOt hOu hOE hOe hX.zdata hX.hf hX.ne inf_le_left inf_le_right
    (l7CoreTwo_proved hE hD4 hM12 hT4 hcit hP Y R S t K' W u e g Z f hX) F hK₁ hτ hτO

end Leaf

section Core

theorem p23_sec_coreT {n : ℕ} (hT : Thm4RTwinBelow 3 n)
    (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g) (hZd : P23ZData t u e Z)
    (hA6 : SecAE R e 6) {f : Y} (hf : f ∈ p23Orb Z t e) (hfe : f ≠ e) {V : Subgroup Y}
    (hVe : V ≤ aSub R Z e) (hVf : V ≤ aSub R Z f) (hV1 : V ≠ ⊥)
    (hL : SecCoresTwoGroup (Om R) V)
    (hW : ¬ ∃ W' : Subgroup (SecQuot (rLayerSub (Om R) V)), WSet (p23SecFamV R V) = {W'})
    (hE4 : Q8Pre (SecQuot (rLayerSub (Om R) V)) (p23SecFamV R V) →
      ∀ K ∈ p23SecFamV R V, ∀ τ : SecQuot (rLayerSub (Om R) V), IsUniqueInvolution K τ →
        ¬ TightInO2 τ → ¬ TwinE4 (SecQuot (rLayerSub (Om R) V)))
    (hLong : ∀ K ∈ p23SecFamV R V, ∀ τ : SecQuot (rLayerSub (Om R) V), IsUniqueInvolution K τ →
      ¬ LongFundSetE3 K τ)
    (mf5 : ModelNoLayer 5 Set.univ ((AE.aeSub 5).map (AE.mkQ 5)))
    (mf6 : ModelNoLayer 6 Set.univ ((AE.aeSub 6).map (AE.mkQ 6)))
    (mf64 : ModelNoLayer 7 AE.e64Sets AE.e64Sub) (Ho : AE7LayerOrbit) :
    ∃ P₀ P₀' : Subgroup Y, IsSylow2In P₀ (tightCore R) ∧ IsSylow2In P₀' K' ∧
      P₀ ≤ Subgroup.centralizer (V : Set Y) ∧ P₀' ≤ Subgroup.centralizer (V : Set Y) ∧
      ∃ w ∈ rLayerSub (Om R) V,
        (∀ x ∈ P₀, w * x * w⁻¹ * x⁻¹ ∈ oddCoreOf (rLayerSub (Om R) V)) ∧
        (∀ x ∈ P₀', w * x * w⁻¹ * x⁻¹ ∈ oddCoreOf (rLayerSub (Om R) V)) ∧
        (w * e * w⁻¹)⁻¹ * f ∈ oddCoreOf (rLayerSub (Om R) V) := by
  obtain ⟨D⟩ := ZTwo.exists_cover hc hA6
  have hVZ : V ≤ Z := hVe.trans (aSub_le R Z e)
  have hfZ : f ∈ Z := hZd.orb_le hf
  have heO : e ∈ p23Orb Z t e := e_mem_orb Z t e
  have heX : e ∈ rLayerSub (Om R) V := (LemL.p23_cover_V hc hZd hVZ heO hVe).1
  have hfX : f ∈ rLayerSub (Om R) V := (LemL.p23_cover_V hc hZd hVZ hf hVf).1
  have hVefZ : V ⊔ Subgroup.zpowers e ⊔ Subgroup.zpowers f ≤ Z :=
    sup_le (sup_le hVZ (Subgroup.zpowers_le.mpr hZd.he)) (Subgroup.zpowers_le.mpr hfZ)
  obtain ⟨⟨P₀, hP₀, hP₀C'⟩, ⟨P₀', hP₀', hP₀'C'⟩⟩ := exists_sylow_cent_twins hc hZd hVefZ
  have heV' : e ∈ V ⊔ Subgroup.zpowers e ⊔ Subgroup.zpowers f :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers e))
  have hfV' : f ∈ V ⊔ Subgroup.zpowers e ⊔ Subgroup.zpowers f :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers f)
  have hVV' : V ≤ V ⊔ Subgroup.zpowers e ⊔ Subgroup.zpowers f := le_sup_left.trans le_sup_left
  have hP₀C : P₀ ≤ Subgroup.centralizer (V : Set Y) :=
    hP₀C'.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVV'))
  have hP₀'C : P₀' ≤ Subgroup.centralizer (V : Set Y) :=
    hP₀'C'.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVV'))
  have hPe : ∀ x ∈ P₀, e * x = x * e := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (hP₀C' hx) e heV'
  have hPf : ∀ x ∈ P₀, f * x = x * f := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (hP₀C' hx) f hfV'
  have hPe' : ∀ x ∈ P₀', e * x = x * e := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (hP₀'C' hx) e heV'
  have hPf' : ∀ x ∈ P₀', f * x = x * f := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (hP₀'C' hx) f hfV'
  have hK₀ : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hK'Ω : K' ∈ Om R := hc.std.hK'.1
  have hP₀X : P₀ ≤ rLayerSub (Om R) V :=
    le_rLayerSub_of_mem (mem_RSet_of_isSylow2In hK₀ hP₀) hP₀C
  have hP₀'X : P₀' ≤ rLayerSub (Om R) V :=
    le_rLayerSub_of_mem (mem_RSet_of_isSylow2In hK'Ω hP₀') hP₀'C
  obtain ⟨hKb, hKb', hne', ⟨zb, hzb, hzb'⟩, hperp, hperp'⟩ :=
    p23_twin_pair_of_sylow hc hL hP₀ hP₀' hP₀C hP₀'C
  have ha2 := mk_sq hZd hZd.he heX
  have hb2 := mk_sq hZd hfZ hfX
  have hanc := not_central_e hc hZd hVZ D hf hfe hVf heX
  have hbnc := not_central_f hc hZd hVZ D hf hfe hVe hfX
  have haE := mem_Ea_self hc hZd hVZ heO hVe heX
  have hbE := mem_Ea_self hc hZd hVZ hf hVf hfX
  have hna := not_isSolvable_Ea hc hZd hVZ D heO hVe heX
  have hnb := not_isSolvable_Ea hc hZd hVZ D hf hVf hfX
  have hcen := central_Ea hc hZd hVZ D hf hVf hfX hbnc
  have hlt := card_secQuot_lt hc hV1
  have hΦΩ := p23SecFamV_hypOmegaGen hc hZd hVZ hL
  have F : Q8Pre (SecQuot (rLayerSub (Om R) V)) (p23SecFamV R V) :=
    { hyp := hΦΩ
      two := p23SecFamV_isPGroup hL
      q8 := p23SecFamV_q8 hc hL
      aEmpty := p23SecFamV_aEmpty hc hZd hVZ hL
      gen := p23SecFamV_pSpan R V
      trans := trans_of_twin' hT hlt hΦΩ (p23SecFamV_isPGroup hL) (p23SecFamV_q8 hc hL)
        (p23SecFamV_aEmpty hc hZd hVZ hL)
        (CFSG.ComponentClassification.OddCore.quotient_corefree ↥(rLayerSub (Om R) V)) hKb
        ⟨hKb', zb, hzb, hzb'⟩ hne' hperp hperp' (not_isPGroup_of_not_isSolvable hna)
      oddFree := CFSG.ComponentClassification.OddCore.quotient_corefree ↥(rLayerSub (Om R) V) }
  obtain ⟨F', ⟨I⟩⟩ := aeIdent7_of_sectionT hP hlt F hKb ⟨hKb', zb, hzb, hzb'⟩ hne' hperp ha2 hanc
    haE hna hW mf5 mf6 mf64 (fun τ hτ hτO => hE4 F _ hKb τ hτ hτO) (hLong _ hKb)
  obtain ⟨wb, hwK, hwK', hwab⟩ := exists_w_of_orbit F' I Ho hKb hKb' hne' hzb hzb' ha2 hb2 hanc hbnc
    haE hbE hna hnb (mk_comm_secImage heX hPe) (mk_comm_secImage heX hPe') (mk_comm_secImage hfX hPf)
    (mk_comm_secImage hfX hPf') hcen
  obtain ⟨w', rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥(rLayerSub (Om R) V)) wb
  refine ⟨P₀, P₀', hP₀, hP₀', hP₀C, hP₀'C, (w' : Y), w'.2, ?_, ?_, ?_⟩
  · intro x hx
    exact comm_mem_oddCoreOf_of_comm w' ⟨x, hP₀X hx⟩ (hwK _ (mk_mem_secImage hx (hP₀X hx)))
  · intro x hx
    exact comm_mem_oddCoreOf_of_comm w' ⟨x, hP₀'X hx⟩ (hwK' _ (mk_mem_secImage hx (hP₀'X hx)))
  · exact conj_mem_oddCoreOf_of_eq w' ⟨e, heX⟩ ⟨f, hfX⟩ hwab

end Core

section Main

theorem p23E8L7Sec_of_modelsT {n : ℕ} (hT : Thm4RTwinBelow 3 n)
    (hL1 : L7CoreTwo n) (hW : L7NoW n) (hE4 : L7NoE4T n) (hLong : L7NoLong n)
    (mf5 : ModelNoLayer 5 Set.univ ((AE.aeSub 5).map (AE.mkQ 5)))
    (mf6 : ModelNoLayer 6 Set.univ ((AE.aeSub 6).map (AE.mkQ 6)))
    (mf64 : ModelNoLayer 7 AE.e64Sets AE.e64Sub) (Ho : AE7LayerOrbit) : P23E8L7Sec n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hA5 hA6 Z hZd f hf hfe hV
  have ctx : L7Ctx n Y R S t K' W u e g Z f := ⟨hc, hno, hA5, hA6, hZd, hf, hfe, hV⟩
  exact p23_sec_coreT hT hP hc hZd hA6 hf hfe inf_le_left inf_le_right hV
    (hL1 hcit hP Y R S t K' W u e g Z f ctx) (hW hcit hP Y R S t K' W u e g Z f ctx)
    (hE4 hcit hP Y R S t K' W u e g Z f ctx) (hLong hcit hP Y R S t K' W u e g Z f ctx) mf5 mf6 mf64 Ho

theorem p23E8L7Sec_doneT {n : ℕ} (hT : Thm4RTwinBelow 3 n)
    (hL1 : L7CoreTwo n) (hW : L7NoW n) (hE4 : L7NoE4T n) (hLong : L7NoLong n) : P23E8L7Sec n :=
  p23E8L7Sec_of_modelsT hT hL1 hW hE4 hLong modelNoLayer_five modelNoLayer_six modelNoLayer_e64
    ae7LayerOrbit_proved

end Main

end Cert

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7
