module

public import CFSG.Quasithin.H13.L32AC44j
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC44a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC44h

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open hiding StatedSL StatedSU StatedSp StatedProj StatedClassicalModel StatedScalars
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

namespace Top43

variable {W K : Subgroup G} (C : Top43 T L V H W K) [IsMulCommutative ↥(conjClosure V H)]
include C

theorem fixV_autK_eq_bot_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    fixV C.autK = ⊥ := by
  have hH : ∀ h : ↥H, ∀ y ∈ fixV C.autK, C.act h y ∈ fixV C.autK := by
    intro h y hy l hl
    have hl' : (C.act h)⁻¹ * l * C.act h ∈ C.autK := by
      have := (Subgroup.mem_normalizer_iff.mp (C.range_le_normalizer
        (C.act.range.inv_mem ⟨h, rfl⟩)) l).mp hl
      simpa using this
    have := hy _ hl'
    calc l (C.act h y) = C.act h (((C.act h)⁻¹ * l * C.act h) y) := by
          simp [MulAut.mul_apply]
      _ = C.act h y := by rw [this]
  rcases C.irr _ hH with h0 | h1
  · exact h0
  · exfalso
    apply C.commV_autK_ne_bot_F4 h1222 h1332 h1334
    rw [eq_bot_iff]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨l, hl, v, rfl⟩
    have hv : v ∈ fixV C.autK := by rw [h1]; exact Subgroup.mem_top v
    rw [SetLike.mem_coe, hv l hl, mul_inv_cancel]
    exact Subgroup.one_mem _

theorem qhatOf_le_two_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    {B : Subgroup G} (hB : QCrit (fsuV1 T V) V H B) (hBT : B ≤ T) :
    qhatOf C.act.range ≤ ((2 : ℚ) : WithTop ℚ) := by
  have hA := C.isA2_autE_F4 h1222 h1332 h1334 hB hBT
  have hr : rAV (C.autE B) ≤ 2 := by
    rw [rAV_le_two_iff C.hexp hA]
    have h1 := C.index_fixV_autE_le_F4 h1222 h1332 h1334 hB hBT
    have h2 := (fixV (C.autE B)).card_mul_index
    calc Nat.card (Hat V H W) = Nat.card ↥(fixV (C.autE B)) * (fixV (C.autE B)).index := h2.symm
      _ ≤ Nat.card ↥(fixV (C.autE B)) * Nat.card ↥(C.autE B) ^ 2 := Nat.mul_le_mul_left _ h1
      _ = Nat.card ↥(C.autE B) ^ 2 * Nat.card ↥(fixV (C.autE B)) := mul_comm _ _
  exact kq_le_iff.mpr ⟨C.autE B, hA, commSeries_eq_bot_of_le (by norm_num)
    ((isQuadratic_iff_commSeries_two _).mp (C.isQuadratic_autE hB)), hr⟩

theorem vHat_le_fixV_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    {y : MulAut (Hat V H W)}
    (hyN : y ∈ Subgroup.normalizer (C.autTK : Set (MulAut (Hat V H W))))
    (hyV : ∀ v ∈ vHat V H W, y v ∈ vHat V H W) (hfpf : ∀ v ∈ vHat V H W, y v = v → v = 1) :
    vHat V H W ≤ fixV C.autTK := by
  have : Finite (MulAut (Hat V H W)) := finite_mulAut
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 C.S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 C.S.hyp h1222 h1332 h1334 hV2
  have hP2 : IsPGroup 2 ↥C.autTK := C.isSylowTwoOf_autTK.2.1
  have hPV : ∀ p ∈ C.autTK, ∀ x ∈ vHat V H W, p x ∈ vHat V H W := by
    rintro _ ⟨b, hb, rfl⟩ x hx
    exact C.act_mem_vHat (S14.TV_F4 (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hb)).1) hx
  have hcardV := C.card_vHat_F4 h1222 h1332 h1334
  have hVne : vHat V H W ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardV
    omega
  obtain ⟨m, hmV, hm1, hmP⟩ := B1.exists_fixed_ne_one C.hexp hP2 hPV hVne
  have hymP : ∀ p ∈ C.autTK, p (y m) = y m := by
    intro p hp
    have hp' : y⁻¹ * p * y ∈ C.autTK := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hyN) p).mp hp
      simpa using this
    have h1 : (y⁻¹ * p * y) m = m := hmP _ hp'
    calc p (y m) = y ((y⁻¹ * p * y) m) := by simp [MulAut.mul_apply]
      _ = y m := by rw [h1]
  have hym1 : y m ≠ 1 := fun h => hm1 (y.injective (h.trans (map_one y).symm))
  have hymm : m ≠ y m := fun h => hm1 (hfpf m hmV h.symm)
  have h3 : 3 ≤ Nat.card ↥(vHat V H W ⊓ fixV C.autTK) :=
    three_le_card_of_ne (a := (1 : ↥(vHat V H W ⊓ fixV C.autTK)))
      (b := ⟨m, Subgroup.mem_inf.mpr ⟨hmV, mem_fixV.mpr hmP⟩⟩)
      (c := ⟨y m, Subgroup.mem_inf.mpr ⟨hyV m hmV, mem_fixV.mpr hymP⟩⟩)
      (fun h => hm1 (congrArg Subtype.val h).symm) (fun h => hym1 (congrArg Subtype.val h).symm)
      (fun h => hymm (congrArg Subtype.val h))
  have hdvd := Subgroup.card_dvd_of_le (inf_le_left : vHat V H W ⊓ fixV C.autTK ≤ vHat V H W)
  rw [hcardV] at hdvd
  have h4 : Nat.card ↥(vHat V H W ⊓ fixV C.autTK) = 4 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card ↥(vHat V H W ⊓ fixV C.autTK)
    · norm_num at hdvd
    · rfl
  have hMV : vHat V H W ⊓ fixV C.autTK = vHat V H W :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
  intro v hv
  rw [← hMV] at hv
  exact (Subgroup.mem_inf.mp hv).2

theorem false_of_l34_F4
    (h310 : D310) (hA21 : AsA21SQTKSection) (h29 : Thm14_7_29_F4)
    (hN1 : LieSylowOver3) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    {n : ℕ} (hn : 1 < n) (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)))
    (hP : IsPSL 3 2 2 (cStar K ⧸ Subgroup.center (cStar K))) {B : Subgroup G}
    (hB : QCrit (fsuV1 T V) V H B) (hBT : B ≤ T) : False := by
  classical
  have : Finite (MulAut (Hat V H W)) := finite_mulAut
  obtain ⟨hzodd, hcard, hPsl⟩ := C.card_autK_of_isPSL34_F4 h1222 h1332 h1334 hP
  obtain ⟨x, hxK, t, htT, hxN, hxfpf, hxt, hβ⟩ :=
    C.exists_data44_F4 hN1 h29 h1222 h1332 h1334 hn hLie
  have hPsyl := C.isSylowTwoOf_autTK
  have hcardV := C.card_vHat_F4 h1222 h1332 h1334
  have hsolv := isSolvable_szB1_l1T_F4 hN1 h1222 h1332 h1334 C.S C.hK C.hq C.hKn hn hLie C.hl1K

  have hNV : ∀ m ∈ C.autK ⊓ Subgroup.normalizer (C.autTK : Set (MulAut (Hat V H W))),
      ∀ v ∈ vHat V H W, m v ∈ vHat V H W := by
    intro m hm v hv
    obtain ⟨hmK, hmN⟩ := Subgroup.mem_inf.mp hm
    obtain ⟨⟨β, hβH⟩, hβK, rfl⟩ := hmK
    have hβB := C.mem_szB1_F4 h1222 h1332 h1334 ⟨β, hβH⟩ (Subgroup.mem_subgroupOf.mp hβK) hmN
    have hβL := mem_normalizer_L_of_solvable_F4 h29 C.S hsolv le_sup_right
      (Subgroup.mem_sup_left hβB)
    exact C.act_mem_vHat (mem_nX_of_F4 h1332 h1334 C.S hβH hβL).1 hv
  have hyX : C.act ⟨x, C.hKH hxK⟩ ∈ C.autK := ⟨⟨x, C.hKH hxK⟩, hxK, rfl⟩
  have hVP := C.vHat_le_fixV_F4 h1222 h1332 h1334 hxN (hNV _ ⟨hyX, hxN⟩) hxfpf
  have hVne : vHat V H W ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardV
    omega
  obtain ⟨⟨m, hmV⟩, hm1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVne
  have hm1' : m ≠ 1 := fun h => hm1 (Subtype.ext h)
  have hyS : C.act ⟨x, C.hKH hxK⟩ ∉ C.autTK := fun h =>
    hm1' (hxfpf m hmV (mem_fixV.mp (hVP hmV) _ h))

  have hαS : ∀ s (hs : s ∈ C.autK), s ∈ C.autTK →
      ((C.conjAutK ⟨t, C.hTH htT⟩ ⟨s, hs⟩ : ↥C.autK) : MulAut (Hat V H W)) ∈ C.autTK := by
    rintro _ hs ⟨b, hb, rfl⟩
    obtain ⟨hbT, hbK⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hb)
    show C.act ⟨t, C.hTH htT⟩ * C.act b * (C.act ⟨t, C.hTH htT⟩)⁻¹ ∈ C.autTK
    refine ⟨⟨t, C.hTH htT⟩ * b * ⟨t, C.hTH htT⟩⁻¹, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mpr ⟨T.mul_mem (T.mul_mem htT hbT) (T.inv_mem htT), ?_⟩), ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (C.hKn (C.hTH htT)) _).mp hbK
    · rw [map_mul, map_mul, map_inv]
  have hαd : ∀ d (hdX : d ∈ C.autK),
      d ∈ Subgroup.normalizer (C.autTK : Set (MulAut (Hat V H W))) →
      (∀ v ∈ vHat V H W, d v = v) →
      ((C.conjAutK ⟨t, C.hTH htT⟩ ⟨d, hdX⟩ : ↥C.autK) : MulAut (Hat V H W)) * d⁻¹ ∈
        C.autTK := by
    intro d hdX hdN hdY
    show C.act ⟨t, C.hTH htT⟩ * d * (C.act ⟨t, C.hTH htT⟩)⁻¹ * d⁻¹ ∈ C.autTK
    obtain ⟨⟨β, hβH⟩, hβK, rfl⟩ := hdX
    exact hβ β (Subgroup.mem_subgroupOf.mp hβK) hdN hdY

  have key : ∀ U : Subgroup (Hat V H W), BinaryNaturalSL C.autK U ⊥ 3 2 →
      ∀ d (hdX : d ∈ C.autK), d ∈ Subgroup.normalizer (C.autTK : Set (MulAut (Hat V H W))) →
      d ∉ C.autTK → (∀ v ∈ vHat V H W, d v = v) →
      ∀ v ∈ U, (∀ s ∈ C.autTK, s v = v) → d v = v → v = 1 :=
    fun U hU d hdX hdN hdS hdY v hvU hvS hdv => l34BorelFix hU hPsyl
      (C.conjAutK ⟨t, C.hTH htT⟩) hαS hyX hxN hyS hxt hdX hdN hdS (hαd d hdX hdN hdY) hvU hvS
      hdv

  have hexd : ∀ U : Subgroup (Hat V H W), BinaryNaturalSL C.autK U ⊥ 3 2 →
      ∃ d ∈ C.autK ⊓ Subgroup.normalizer (C.autTK : Set (MulAut (Hat V H W))),
        d ∉ C.autTK ∧ ∀ v ∈ vHat V H W, d v = v := by
    intro U hU
    refine exists_trivial_not_mem hNV ?_
    rw [relIndex_normalizer_eq_nine hU hPsyl]
    have := card_mulAut_le_six hcardV
    omega
  rcases C.irr_or_d310Two_F4 h310 h1222 h1332 h1334 hB hBT with hirr | ⟨Vs, h2⟩
  · rcases natural_or_nine C.hexp (C.b4Hyp_F4 hA21 h1222 h1332 h1334 hirr) le_rfl hPsl
      (C.qhatOf_le_two_F4 h1222 h1332 h1334 hB hBT) with hnat | ⟨k, hk1, hk, hnine⟩
    · obtain ⟨d, hdM, hdS, hdY⟩ := hexd ⊤ hnat
      obtain ⟨hdX, hdN⟩ := Subgroup.mem_inf.mp hdM
      exact hm1' (key ⊤ hnat d hdX hdN hdS hdY m (Subgroup.mem_top m)
        (fun s hs => mem_fixV.mp (hVP hmV) s hs) (hdY m hmV))
    · obtain rfl : k = 1 := by omega
      have h1 := CFSG.Quasithin.H.FixSyl.card_fixV_sylow_le_two_binaryNine hnine hPsyl.1
        hPsyl.card_eq
      have h2 := Subgroup.card_le_of_le hVP
      omega
  · obtain ⟨-, hnat⟩ := d310Two_psl34 h2 hzodd hcard rfl hPsl
    have hfix := C.fixV_autK_eq_bot_F4 h1222 h1332 h1334
    rw [hfix, inf_bot_eq] at hnat
    obtain ⟨-, ⟨τ, hτT, hτ⟩, hsum⟩ := h2
    obtain ⟨⟨hsum1, hsum2⟩, -⟩ := hsum τ hτT hτ
    rw [hfix, sup_bot_eq] at hsum1
    rw [hfix, sup_bot_eq, sup_bot_eq] at hsum2
    have hnat' := binaryNaturalSL_map hnat (C.range_le_normalizer (C.autT_le hτT))
    obtain ⟨d, hdM, hdS, hdY⟩ := hexd Vs hnat
    obtain ⟨hdX, hdN⟩ := Subgroup.mem_inf.mp hdM
    have hm : m ∈ Vs ⊔ Vs.map τ.toMonoidHom := by
      rw [← hsum1]
      exact Subgroup.mem_top m
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hm
    have hfixab : ∀ g ∈ C.autK, g m = m → g a = a ∧ g b = b := fun g hg hgm =>
      comp_eq_of_disjoint hsum2 (fun u hu => mem_of_binaryNaturalSL hnat hg hu)
        (fun u hu => mem_of_binaryNaturalSL hnat' hg hu) ha hb (by rw [hab]; exact hgm)
    have hS : ∀ s ∈ C.autTK, s m = m := fun s hs => mem_fixV.mp (hVP hmV) s hs
    have ha1 : a = 1 := key Vs hnat d hdX hdN hdS hdY a ha
      (fun s hs => (hfixab s (hPsyl.1 hs) (hS s hs)).1) (hfixab d hdX (hdY m hmV)).1
    have hb1 : b = 1 := key _ hnat' d hdX hdN hdS hdY b hb
      (fun s hs => (hfixab s (hPsyl.1 hs) (hS s hs)).2) (hfixab d hdX (hdY m hmV)).2
    apply hm1'
    rw [← hab, ha1, hb1, mul_one]

end Top43

theorem lemma14_7_44_of_F4
    (h310 : D310) (hA21 : AsA21SQTKSection) (h29 : Thm14_7_29_F4)
    (hN1 : LieSylowOver3) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h30 : Lemma14_7_30_F4) (h32 : Lemma14_7_32_F4) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK)
    (h42 : Lemma14_7_42_S5S3_F4) : Lemma14_7_44_F4 := by
  intro G _ _ T L V H S K hK hHeq n hn hLie hP
  have hq := (h30 G T L V H S K hK).1
  have hKn := le_normalizer_of_setting hA37 hA38 S hK (h32 G T L V H S K hK)
  by_cases hl1K : l1 T L V ≤ K
  · obtain ⟨-, -, -, hF918⟩ := h30 G T L V H S K hK
    have hTK : T ≤ Subgroup.normalizer (K : Set G) := (Setting147.TH' S).trans hKn
    have hHeq' : conjClosure K T ⊔ (l1 T L V ⊔ T) = H := by
      rw [conjClosure_T_eq_self hTK]
      exact hHeq.symm
    rw [hHeq'] at hF918
    obtain ⟨W, hW⟩ := exists_topW S hF918.toHypF98
    have hHKT : H = K ⊔ T := by
      rw [hHeq, ← sup_assoc, sup_eq_left.mpr hl1K]
    have C : Top43 T L V H W K := ⟨hW, hK, hKn, hHKT, hq, hl1K⟩
    have := C.toTopW.comm
    obtain ⟨B, hB, -⟩ := hF918.F918_2
    have hBT : B ≤ T := hB.1.trans (L32A.pCoreOf_le_of_le S.hyp le_sup_right)
    exact C.false_of_l34_F4 h310 hA21 h29 hN1 h1222 h1332 h1334 hn hLie hP hB.2.1 hBT
  · obtain ⟨ρ, hρs, hρk⟩ := h42 G T L V H S K hK hHeq n hn hLie hl1K
    have := hq.2.1
    have : Nontrivial (cStar K) :=
      (QuotientGroup.mk_surjective (s := Subgroup.center (cStar K))).nontrivial
    obtain ⟨e⟩ := isAlt5_of_s5s3 hK hKn this hρs hρk
    obtain ⟨-, F, _, _, hF, ⟨e'⟩⟩ := hP
    have h1 : Nat.card (cStar K ⧸ Subgroup.center (cStar K)) = 20160 := by
      rw [Nat.card_congr e'.toEquiv, card_psl34 hF]
    have h2 : Nat.card (cStar K ⧸ Subgroup.center (cStar K)) ≤ Nat.card (cStar K) :=
      Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
    have h3 : Nat.card (cStar K) = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    omega

end CFSG.Quasithin.H13.L32A.C
