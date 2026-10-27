module

public import CFSG.CGT.PushingUpLit.BHS7.SevenThirteenQ2
public import CFSG.CGT.PushingUpLit.BHS7.SevenThirteenQ1
public import CFSG.CGT.PushingUpLit.BHS7.QuotModuleW
public import CFSG.CGT.PushingUpLit.BHS7.QuotAmbient
public import CFSG.CGT.PushingUpLit.BHS6.OffenderNormalizes
public import CFSG.CGT.PushingUpLit.BHS7.QuotBlock

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.LieType.BorelTits CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem isPGroup_autOn {R V : Subgroup Γ} (hR : IsPGroup 2 ↥R) : IsPGroup 2 ↥(autOn R V) :=
  CFSG.Quasithin.AutOn.isPGroup_autOn hR

theorem autOn_sup {X Z V : Subgroup Γ} (hX : X ≤ Subgroup.normalizer (V : Set Γ))
    (hZ : Z ≤ Subgroup.normalizer (V : Set Γ)) : autOn (X ⊔ Z) V = autOn X V ⊔ autOn Z V := by
  unfold autOn
  rw [Subgroup.subgroupOf_sup hX hZ, Subgroup.map_sup]

@[expose] noncomputable def preSub (V A : Subgroup Γ) (Y : Subgroup (MulAut ↥V)) : Subgroup Γ :=
  A ⊓ (Y.comap (conjAct V)).map (Subgroup.normalizer (V : Set Γ)).subtype

theorem preSub_le {V A : Subgroup Γ} {Y : Subgroup (MulAut ↥V)} : preSub V A Y ≤ A := inf_le_left

theorem mem_preSub {V A : Subgroup Γ} {Y : Subgroup (MulAut ↥V)} {g : Γ} :
    g ∈ preSub V A Y ↔ g ∈ A ∧ ∃ hg : g ∈ Subgroup.normalizer (V : Set Γ),
      conjAct V ⟨g, hg⟩ ∈ Y := by
  unfold preSub
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨hgA, x, hx, rfl⟩
    exact ⟨hgA, x.2, hx⟩
  · rintro ⟨hgA, hg, h⟩
    exact ⟨hgA, ⟨g, hg⟩, h, rfl⟩

section Finite

variable [Finite Γ]

theorem false_of_offQ {G T E H P M V W : Subgroup Γ}
    (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hV : IsElemAbelian 2 V) (hVQ : V ≤ pCoreOf 2 G)
    (hGV : G ≤ Subgroup.normalizer (V : Set Γ)) (hK2 : pCoreOf 2 (autOn G V) = ⊥)
    (hE : IsBTBlock G T E) (hne : ⁅E, V⁆ ≠ ⊥) (hEH : E ≤ H) (hsub : IsSubnormal E H)
    (hTH : T ≤ H) (hHG : H ≤ G) (hMP : MinPar P T M) (hPG : P ≤ G) (hPE : G ≤ P ⊔ E)
    (hW : IsModuleW P T V W)
    (hoff : ∃ A : Subgroup Γ, A ≤ T ∧ IsOffG V A ∧ Nat.card V < wtG V A) : False := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hV.2 v v.2)
  have hTG : T ≤ G := hT.1
  have hEG : E ≤ G := hE.le
  have hEV : E ≤ Subgroup.normalizer (V : Set Γ) := hEG.trans hGV
  have hPV : P ≤ Subgroup.normalizer (V : Set Γ) := hPG.trans hGV
  have hTP : T ≤ P := hMP.T_le
  set K : Subgroup (MulAut ↥V) := autOn G V with hKdef
  have hinj : Function.Injective (BHS5.quotHom K) := quotHom_injective_of_pCoreOf_eq_bot hV2 hK2
  set TK : Subgroup (MulAut ↥V) := autOn T V with hTKdef
  set PK : Subgroup (MulAut ↥V) := autOn P V with hPKdef
  set EK : Subgroup (MulAut ↥V) := autOn E V with hEKdef
  set HK : Subgroup (MulAut ↥V) := autOn H V with hHKdef
  have hTK : TK ≤ K := autOn_le_autOn V hTG
  have hPK : PK ≤ K := autOn_le_autOn V hPG
  have hEK : EK ≤ K := autOn_le_autOn V hEG
  have hEHK : EK ≤ HK := autOn_le_autOn V hEH
  have hHK : HK ≤ K := autOn_le_autOn V hHG
  have hKPE : K ≤ PK ⊔ EK := by
    have h1 : autOn G V ≤ autOn (P ⊔ E) V := autOn_le_autOn V hPE
    rwa [autOn_sup hPV hEV] at h1
  have hEgen : EK ≤ Subgroup.closure {x | x ∈ EK ∧ Odd (orderOf x)} := by
    have h1 : opResidual 2 EK = EK := by
      rw [hEKdef, opResidual_autOn hEV, opResidual_eq_of_isBTBlock hE]
    have := BHS5.opResidual_le_closure_odd EK
    rwa [h1] at this
  have htype : (∃ k : ℕ, 2 ≤ k ∧ IsSLNatSection EK (commV EK) (commV EK ⊓ fixV EK) k) ∨
      ∃ m : ℕ, 1 ≤ m ∧ IsAltNatSection EK (commV EK) (commV EK ⊓ fixV EK) (2 * m + 1) := by
    rcases hE.type with ⟨n, hn2, hn⟩ | ⟨m, hm1, hm⟩
    · exact Or.inl ⟨n, hn2, isSLNatSection_autOn_of_isBTBlock hG hT hE hn hV hVQ hEV hne⟩
    · exact Or.inr ⟨m, hm1, isAltNatSection_autOn_of_isBTBlock hG hT hE hm hV hVQ hEV hne⟩
  have hsubK : IsSubnormal EK HK := autOn_isSubnormal hsub
  have hQ1 : ∀ B ∈ offQMin K TK, ∀ g ∈ EK, ∀ b ∈ B, g * b = b * g := by
    intro B hB g hg b hb
    have hBH : B ≤ HK := hB.1.1.trans (autOn_le_autOn V hTH)
    have h0 := commutator_eq_bot_of_mem_offQMin hV2 hinj hTK hHK hEHK hsubK hEgen htype hBH hB
    have h1 : ⁅g, b⁆ ∈ (⁅EK, B⁆ : Subgroup (MulAut ↥V)) := Subgroup.commutator_mem_commutator hg hb
    rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hOP : pCoreOf 2 P ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hOT : pCoreOf 2 P ≤ T := (isSylowTwoOf_of_isSylowOf hMP.syl).pCoreOf_le
  set RK : Subgroup (MulAut ↥V) := autOn (pCoreOf 2 P) V with hRKdef
  have hRT : RK ≤ TK := autOn_le_autOn V hOT
  have hR2 : IsPGroup 2 ↥RK :=
    isPGroup_autOn (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 P)
  have hkeyR : ∀ g : ↥(Subgroup.normalizer (V : Set Γ)), (g : Γ) ∈ P → ∀ y ∈ RK,
      conjAct V g * y * (conjAct V g)⁻¹ ∈ RK := by
    intro g hg y hy
    obtain ⟨x, hxO, rfl⟩ := mem_autOn_iff.mp hy
    refine mem_autOn_iff.mpr ⟨g * x * g⁻¹, ?_, ?_⟩
    · show (g : Γ) * x * (g : Γ)⁻¹ ∈ pCoreOf 2 P
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf_self P hg) x).mp hxO
    · rw [map_mul, map_mul, map_inv]
  have hPR : PK ≤ Subgroup.normalizer (RK : Set (MulAut ↥V)) := by
    intro g' hg'
    obtain ⟨g, hgP, rfl⟩ := mem_autOn_iff.mp hg'
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hkeyR g hgP y hy, fun hy => ?_⟩
    have e : (conjAct V g)⁻¹ * (conjAct V g * y * (conjAct V g)⁻¹) * ((conjAct V g)⁻¹)⁻¹ = y := by
      group
    have h2 := hkeyR g⁻¹ (P.inv_mem hgP) _ hy
    rwa [map_inv, e] at h2
  have hInv : ∀ C ∈ offQ K TK, ¬ C ≤ RK := fun C hC hCR =>
    not_le_of_mem_offQ hK2 hPK hKPE hRT hTK hPR hR2 hQ1 hC hCR
  obtain ⟨A, hAT, hAoff, hAwt⟩ := hoff
  have hAV : A ≤ Subgroup.normalizer (V : Set Γ) := hAoff.1
  have hAstar : IsOffStar (autOn A V) :=
    ⟨(isOffG_iff_isOff_autOn hV hAV).mp hAoff, by rw [wt_autOn hV hAV]; exact hAwt⟩
  obtain ⟨B₁, hB₁⟩ := exists_mem_offQ hinj hTK (autOn_le_autOn V hAT) hAstar
  obtain ⟨B, hBmin, -⟩ := exists_offQMin_le hB₁
  have hBT : B ≤ TK := hBmin.1.1
  have hBK : B ≤ K := hBT.trans hTK
  set Q : Subgroup (MulAut ↥V) := qSubQ K TK with hQdef
  have hQc : Q ≤ Subgroup.centralizer (EK : Set (MulAut ↥V)) := qSubQ_le_centralizer hQ1
  set X : Subgroup Γ := preSub V T Q with hXdef
  have hXT : X ≤ T := preSub_le
  have hXn : T ≤ Subgroup.normalizer (X : Set Γ) := by
    have key : ∀ t ∈ T, ∀ y ∈ X, t * y * t⁻¹ ∈ X := by
      intro t ht y hy
      obtain ⟨hyT, hyN, hyQ⟩ := mem_preSub.mp hy
      have htN : t ∈ Subgroup.normalizer (V : Set Γ) := hGV (hTG ht)
      have hty : t * y * t⁻¹ ∈ Subgroup.normalizer (V : Set Γ) :=
        (Subgroup.normalizer (V : Set Γ)).mul_mem
          ((Subgroup.normalizer (V : Set Γ)).mul_mem htN hyN)
          ((Subgroup.normalizer (V : Set Γ)).inv_mem htN)
      refine mem_preSub.mpr ⟨T.mul_mem (T.mul_mem ht hyT) (T.inv_mem ht), hty, ?_⟩
      have hτ : conjAct V ⟨t, htN⟩ ∈ TK := mem_autOn_iff.mpr ⟨⟨t, htN⟩, ht, rfl⟩
      have hle : conjSub (conjAct V ⟨t, htN⟩) Q ≤ Q := conjSub_qSubQ_le (hTK hτ) hτ
      have h1 : conjAct V ⟨t * y * t⁻¹, hty⟩ = conjAct V ⟨t, htN⟩ * conjAct V ⟨y, hyN⟩ *
          (conjAct V ⟨t, htN⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [h1]
      refine hle ?_
      rw [mem_conjSub_iff]
      have e : (conjAct V ⟨t, htN⟩)⁻¹ * (conjAct V ⟨t, htN⟩ * conjAct V ⟨y, hyN⟩ *
          (conjAct V ⟨t, htN⟩)⁻¹) * conjAct V ⟨t, htN⟩ = conjAct V ⟨y, hyN⟩ := by group
      rw [e]
      exact hyQ
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => key t ht y hy, fun hy => ?_⟩
    have h2 := key t⁻¹ (T.inv_mem ht) _ hy
    have e : t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y := by group
    rwa [e] at h2
  have hXE : ∀ y ∈ X, ∀ e ∈ E, ⁅y, e⁆ ∈ Subgroup.centralizer (V : Set Γ) := by
    intro y hy e he
    obtain ⟨hyT, hyN, hyQ⟩ := mem_preSub.mp hy
    have heN : e ∈ Subgroup.normalizer (V : Set Γ) := hEV he
    have heK : conjAct V ⟨e, heN⟩ ∈ EK := mem_autOn_iff.mpr ⟨⟨e, heN⟩, he, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp (hQc hyQ) _ heK
    exact (conjAct_comm_eq_one_iff V ⟨y, hyN⟩ ⟨e, heN⟩).mp h1.symm
  set Wv : Subgroup ↥V := W.subgroupOf V with hWvdef
  have hfixeq : BHS5.fixOp K = (Subgroup.centralizer (opResidual 2 G : Set Γ)).subgroupOf V :=
    fixOp_autOn_eq hV hGV
  have hf1 : ∀ b ∈ B, b ∈ RK → ∀ w ∈ Wv, b w * w⁻¹ ∈ BHS5.fixOp K := by
    intro b hb hbR w hw
    obtain ⟨x, hxO, rfl⟩ := mem_autOn_iff.mp hbR
    have hxT : (x : Γ) ∈ T := hOT hxO
    have hxX : (x : Γ) ∈ X := mem_preSub.mpr ⟨hxT, x.2, le_qSubQ hBmin hb⟩
    have h1 := commutator_mem_centralizer_opResidual hG hT hE hVQ hGV hne hMP.syl hPE hW hXT hXn
      hXE ⟨hxX, hxO⟩ (Subgroup.mem_subgroupOf.mp hw)
    rw [hfixeq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, conjAct_apply', Subgroup.coe_inv]
    exact h1.2
  have hf2 : ∀ c ∈ B, (∀ w ∈ Wv, c w * w⁻¹ ∈ BHS5.fixOp K) → c ∈ RK := by
    intro c hc hcw
    obtain ⟨t, htT, rfl⟩ := mem_autOn_iff.mp (hBT hc)
    refine mem_autOn_iff.mpr ⟨t, ?_, rfl⟩
    refine hW.cen_le t htT fun w hw => ?_
    have h1 := hcw ⟨w, hW.le_V hw⟩ (Subgroup.mem_subgroupOf.mpr hw)
    rw [hfixeq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, conjAct_apply', Subgroup.coe_inv] at h1
    refine ⟨?_, Subgroup.centralizer_le (opResidual_mono 2 hPG) h1⟩
    have hwV : w ∈ V := hW.le_V hw
    have htw : (t : Γ) * w * (t : Γ)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp t.2 w).mp hwV
    exact V.mul_mem htw (V.inv_mem hwV)
  set Bh : Subgroup (MulAut (↥V ⧸ BHS5.fixOp K)) := qImg K B with hBhdef
  have hBoff : IsOffStar Bh := hBmin.1.2
  set W' : Subgroup (↥V ⧸ BHS5.fixOp K) := Wv.map (QuotientGroup.mk' (BHS5.fixOp K)) with hW'
  set C : Subgroup (MulAut ↥V) := BHS5.liftQ K (cenIn Bh W') with hCdef
  have hrange : cenIn Bh W' ≤ (⊤ : Subgroup ↥K).map (BHS5.quotHom K) :=
    (cenIn_le Bh W').trans qImg_le_range
  have hCle : C ≤ B := by
    have := BHS5.liftQ_mono (cenIn_le Bh W')
    rwa [hBhdef, qImg, BHS5.liftQ_quotImg hinj hBK] at this
  have hCimg : qImg K C = cenIn Bh W' := BHS5.quotImg_liftQ hrange
  have hCeq : C = B ⊓ RK := by
    refine le_antisymm (le_inf hCle fun c hc => ?_) fun c hc => ?_
    · refine hf2 c (hCle hc) fun w hw => ?_
      obtain ⟨hcK, hρ⟩ := BHS5.mem_liftQ.mp hc
      have h1 := hρ.2 (QuotientGroup.mk w) ⟨w, hw, rfl⟩
      exact (quotHom_apply_mk_eq_iff ⟨c, hcK⟩ w).1 h1
    · have hcK : c ∈ K := hBK hc.1
      refine BHS5.mem_liftQ.mpr ⟨hcK, mem_qImg.2 ⟨⟨c, hcK⟩, hc.1, rfl⟩, fun u hu => ?_⟩
      obtain ⟨w, hw, rfl⟩ := hu
      exact (quotHom_apply_mk_eq_iff ⟨c, hcK⟩ w).2 (hf1 c hc.1 hc.2 w hw)
  rcases offender_card_lt_or hBoff W' with hlt | hstar
  ·
    have h1 : (cenIn Bh W').relIndex Bh = (B ⊓ RK).relIndex B := by
      rw [← hCimg, hCeq, hBhdef]
      unfold qImg
      rw [Subgroup.relIndex_map_map_of_injective _ _ hinj, Subgroup.relIndex_subgroupOf hBK]
    have h2 : (fixV Bh).relIndex W' = (secFix B Wv (BHS5.fixOp K)).relIndex Wv :=
      relIndex_fixV_qImg hBK Wv
    obtain ⟨B', hB'T, hB'⟩ := exists_autOn_eq hBT
    have hBe : IsElemAbelian2 B := isElemAbelian2_of_mem_offQ hinj hTK hBmin.1
    have h3 : (B' ⊓ pCoreOf 2 P).relIndex B' ≤ (secFix B Wv
        ((V ⊓ Subgroup.centralizer (opResidual 2 P : Set Γ)).subgroupOf V)).relIndex Wv := by
      have := relIndex_pCoreOf_le_secFix hV hPV hMP hW hB'T (by rw [hB']; exact hBe)
      rwa [hB'] at this
    have h4 : (B ⊓ RK).relIndex B = (B' ⊓ pCoreOf 2 P).relIndex B' := by
      have := relIndex_autOn_pCoreOf hPV hMP hW hB'T
      rwa [hB'] at this
    have h5 : secFix B Wv (BHS5.fixOp K) ≤ secFix B Wv
        ((V ⊓ Subgroup.centralizer (opResidual 2 P : Set Γ)).subgroupOf V) := by
      refine secFix_mono_right fun v hv => ?_
      rw [hfixeq, Subgroup.mem_subgroupOf] at hv
      exact Subgroup.mem_subgroupOf.mpr ⟨v.2, Subgroup.centralizer_le (opResidual_mono 2 hPG) hv⟩
    have hpos : 0 < (secFix B Wv (BHS5.fixOp K)).relIndex Wv :=
      Nat.pos_of_ne_zero (by
        show ((secFix B Wv (BHS5.fixOp K)).subgroupOf Wv).index ≠ 0
        exact Subgroup.index_ne_zero_of_finite)
    have h6 : (secFix B Wv
        ((V ⊓ Subgroup.centralizer (opResidual 2 P : Set Γ)).subgroupOf V)).relIndex Wv ≤
        (secFix B Wv (BHS5.fixOp K)).relIndex Wv :=
      Nat.le_of_dvd hpos (Subgroup.relIndex_dvd_of_le_left Wv h5)
    omega
  · have hCmem : C ∈ offQ K TK := ⟨hCle.trans hBT, by rw [hCimg]; exact hstar⟩
    exact hInv C hCmem (hCeq ▸ inf_le_right)

end Finite

end CFSG.CGT.PushingUpLit.BHS7
