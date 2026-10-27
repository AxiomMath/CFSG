module

public import CFSG.Quasithin.H13.L32AC43h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC41b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC43e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk12
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AM50j

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open hiding StatedSL StatedSU StatedSp StatedProj StatedClassicalModel
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

namespace Top43

variable {W K : Subgroup G} (C : Top43 T L V H W K) [IsMulCommutative ↥(conjClosure V H)]
include C

theorem ker_autKSurj_le_center_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) : C.autKSurj.ker ≤ Subgroup.center (cStar K) := by
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple C.hq C.autKSurj.ker
    with h | h
  · exact h
  · exfalso
    obtain ⟨x, hxK, -, hx1⟩ := C.exists_act_ne_one_F4 h1222 h1332 h1334
    apply hx1
    have h1 : C.autKSurj (QuotientGroup.mk ⟨x, hxK⟩) = 1 := by
      rw [← MonoidHom.mem_ker, h]
      exact Subgroup.mem_top _
    exact congrArg Subtype.val h1

theorem mem_szB1_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (β : ↥H)
    (hβK : (β : G) ∈ K)
    (hβN : C.act β ∈ Subgroup.normalizer (C.autTK : Set (MulAut (Hat V H W)))) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) β ∈ szB1 T H K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2T : pCoreOf 2 H ≤ T := L32A.pCoreOf_le_of_le C.S.hyp C.hTH
  have hO2K : pCoreOf 2 K ≤ pCoreOf 2 H :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp C.hK)
  obtain ⟨e, he⟩ := (C.S.hyp.fsu.sylow.1 : IsPGroup 2 ↥T).exists_card_eq
  have hpowT : ∀ x ∈ T, x ^ 2 ^ e = 1 := by
    intro x hx
    have h1 := pow_card_eq_one' (G := ↥T) (x := ⟨x, hx⟩)
    rw [he] at h1
    simpa using congrArg Subtype.val h1

  let φ : cStar K →* ↥H ⧸ CFSG.pCore 2 ↥H :=
    QuotientGroup.lift _ ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion C.hKH))
      fun x hx => by
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, mk_pCore_eq_one_iff]
        exact hO2K (Subgroup.mem_subgroupOf.mp hx)
  show _ ∈ Subgroup.normalizer (szS1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) ⊓ modO2Image H K
  refine Subgroup.mem_inf.mpr ⟨mem_normalizer_of_conj_mem_fin fun s hs => ?_,
    mem_modO2Image'.mpr ⟨β, hβK, rfl⟩⟩
  obtain ⟨⟨t, htH⟩, htT, rfl⟩ := mem_modO2Image'.mp (Subgroup.mem_inf.mp hs).1
  obtain ⟨⟨a, haH⟩, haK, hat⟩ := mem_modO2Image'.mp (Subgroup.mem_inf.mp hs).2
  have haT : a ∈ T := by
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ((⟨t, htH⟩ : ↥H)⁻¹ * ⟨a, haH⟩) = 1 := by
      rw [map_mul, map_inv, hat, inv_mul_cancel]
    have h2 : t⁻¹ * a ∈ T := hO2T ((mk_pCore_eq_one_iff _).mp h1)
    have e1 : a = t * (t⁻¹ * a) := by group
    rw [e1]
    exact T.mul_mem htT h2
  rw [← hat, ← map_inv, ← map_mul, ← map_mul]

  have haP : C.act ⟨a, haH⟩ ∈ C.autTK :=
    ⟨⟨a, haH⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨haT, haK⟩), rfl⟩
  have h3 : C.act (β * ⟨a, haH⟩ * β⁻¹) ∈ C.autTK := by
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hβN _).mp haP
  obtain ⟨a', ha', ha'e⟩ := h3
  have ha'T : (a' : G) ∈ T := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ha')).1
  have ha'K : (a' : G) ∈ K := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ha')).2
  have hbK : ((β * ⟨a, haH⟩ * β⁻¹ : ↥H) : G) ∈ K :=
    K.mul_mem (K.mul_mem hβK haK) (K.inv_mem hβK)
  set c : ↥H := a'⁻¹ * (β * ⟨a, haH⟩ * β⁻¹) with hc
  have hcK : (c : G) ∈ K := K.mul_mem (K.inv_mem ha'K) hbK
  have hc1 : C.act c = 1 := by rw [hc, map_mul, map_inv, ha'e, inv_mul_cancel]

  have hcZ : (QuotientGroup.mk ⟨(c : G), hcK⟩ : cStar K) ∈ Subgroup.center (cStar K) := by
    apply C.ker_autKSurj_le_center_F4 h1222 h1332 h1334
    rw [MonoidHom.mem_ker]
    exact Subtype.ext hc1
  have hφc : QuotientGroup.mk' (CFSG.pCore 2 ↥H) c = φ (QuotientGroup.mk ⟨(c : G), hcK⟩) := rfl
  have hφa : QuotientGroup.mk' (CFSG.pCore 2 ↥H) a' =
      φ (QuotientGroup.mk ⟨(a' : G), ha'K⟩) := rfl
  have hcomm : Commute (QuotientGroup.mk' (CFSG.pCore 2 ↥H) a')
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H) c) := by
    rw [hφa, hφc]
    exact (show Commute _ _ from Subgroup.mem_center_iff.mp hcZ _).map φ
  have hcm : QuotientGroup.mk' (CFSG.pCore 2 ↥H) c ^ Nat.card (Subgroup.center (cStar K)) = 1 := by
    rw [hφc, ← map_pow]
    have h1 := pow_card_eq_one' (G := ↥(Subgroup.center (cStar K))) (x := ⟨_, hcZ⟩)
    have h2 : (QuotientGroup.mk ⟨(c : G), hcK⟩ : cStar K) ^
        Nat.card (Subgroup.center (cStar K)) = 1 := by
      have h3 := congrArg Subtype.val h1
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h3
    rw [h2, map_one]

  have ha'2 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) a' ^ 2 ^ e = 1 := by
    rw [← map_pow]
    have : a' ^ 2 ^ e = 1 := Subtype.ext (by simpa using hpowT _ ha'T)
    rw [this, map_one]
  have hprod : QuotientGroup.mk' (CFSG.pCore 2 ↥H) a' * QuotientGroup.mk' (CFSG.pCore 2 ↥H) c =
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) (β * ⟨a, haH⟩ * β⁻¹) := by
    rw [← map_mul, hc, mul_inv_cancel_left]
  have hb2 : (QuotientGroup.mk' (CFSG.pCore 2 ↥H) a' * QuotientGroup.mk' (CFSG.pCore 2 ↥H) c) ^
      2 ^ e = 1 := by
    rw [hprod, ← map_pow]
    have h1 : (⟨a, haH⟩ : ↥H) ^ 2 ^ e = 1 := Subtype.ext (by simpa using hpowT _ haT)
    rw [conj_pow, h1, mul_one, mul_inv_cancel, map_one]
  have hγ1 := eq_one_of_two_pow_odd hcomm (odd_card_center_cStar K) ha'2 hb2 hcm
  show _ ∈ modO2Image H T ⊓ modO2Image H K
  refine Subgroup.mem_inf.mpr ⟨mem_modO2Image'.mpr ⟨a', ha'T, ?_⟩,
    mem_modO2Image'.mpr ⟨_, hbK, rfl⟩⟩
  rw [← hprod, hγ1, mul_one]

theorem false_of_u38_F4
    (h310 : D310) (hA21 : AsA21SQTKSection) (h29 : Thm14_7_29_F4)
    (hN1 : LieSylowOver3) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    {n : ℕ} (hn : 1 < n) (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)))
    (hU : IsPSU 3 2 3 (cStar K ⧸ Subgroup.center (cStar K))) {B : Subgroup G}
    (hB : QCrit (fsuV1 T V) V H B) (hBT : B ≤ T) : False := by
  obtain ⟨z, hz, hcard⟩ := C.card_autK_of_isPSU_F4 h1222 h1332 h1334 hU
  rcases C.irr_or_d310Two_F4 h310 h1222 h1332 h1334 hB hBT with hirr | ⟨Vs, h2⟩
  swap
  · exact false_of_d310Two_u38 h2 hz hcard
  have hnat := C.binaryNaturalSU3_F4 hA21 h1222 h1332 h1334 hirr hU hB hBT
  obtain ⟨ν, hνK, hνN, h64⟩ := exists_scalar_normalizer hnat C.isSylowTwoOf_autTK
  obtain ⟨⟨k, hkH⟩, hkK, rfl⟩ := hνK
  have hkK' : k ∈ K := hkK

  have hkB := C.mem_szB1_F4 h1222 h1332 h1334 ⟨k, hkH⟩ hkK' hνN
  have hsolv := isSolvable_szB1_l1T_F4 hN1 h1222 h1332 h1334 C.S C.hK C.hq C.hKn hn hLie C.hl1K
  have hkL := mem_normalizer_L_of_solvable_F4 h29 C.S hsolv le_sup_right
    (Subgroup.mem_sup_left hkB)
  have hkX := mem_nX_of_F4 h1332 h1334 C.S hkH hkL

  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 C.S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 C.S.hyp h1222 h1332 h1334 hV2

  have hP2 : IsPGroup 2 ↥C.autTK := C.isSylowTwoOf_autTK.2.1
  have hPV : ∀ p ∈ C.autTK, ∀ x ∈ vHat V H W, p x ∈ vHat V H W := by
    rintro _ ⟨y, hy, rfl⟩ x hx
    exact C.act_mem_vHat (S14.TV_F4 (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)).1) hx
  have hcardV := C.card_vHat_F4 h1222 h1332 h1334
  have hVne : vHat V H W ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardV
    omega
  obtain ⟨m, hmV, hm1, hmP⟩ := B1.exists_fixed_ne_one C.hexp hP2 hPV hVne
  have hY1 : vHat V H W ⊓ fixV C.autTK ≠ ⊥ := by
    intro h
    have hm : m ∈ vHat V H W ⊓ fixV C.autTK := Subgroup.mem_inf.mpr ⟨hmV, mem_fixV.mpr hmP⟩
    rw [h, Subgroup.mem_bot] at hm
    exact hm1 hm
  have hYν : ∀ y ∈ vHat V H W ⊓ fixV C.autTK,
      C.act ⟨k, hkH⟩ y ∈ vHat V H W ⊓ fixV C.autTK := by
    intro y hy
    obtain ⟨hyV, hyF⟩ := Subgroup.mem_inf.mp hy
    refine Subgroup.mem_inf.mpr ⟨C.act_mem_vHat hkX.1 hyV, mem_fixV.mpr fun p hp => ?_⟩
    have hp' : (C.act ⟨k, hkH⟩)⁻¹ * p * C.act ⟨k, hkH⟩ ∈ C.autTK := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hνN) p).mp hp
      simpa using this
    have h1 : ((C.act ⟨k, hkH⟩)⁻¹ * p * C.act ⟨k, hkH⟩) y = y := mem_fixV.mp hyF _ hp'
    calc p (C.act ⟨k, hkH⟩ y)
        = C.act ⟨k, hkH⟩ (((C.act ⟨k, hkH⟩)⁻¹ * p * C.act ⟨k, hkH⟩) y) := by
          simp [MulAut.mul_apply]
      _ = C.act ⟨k, hkH⟩ y := by rw [h1]
  have h64' := h64 _ inf_le_right hY1 hYν
  have hle := Subgroup.card_le_of_le (inf_le_left : vHat V H W ⊓ fixV C.autTK ≤ vHat V H W)
  omega

end Top43

theorem lemma14_7_43_of_F4
    (h310 : D310) (hA21 : AsA21SQTKSection) (h29 : Thm14_7_29_F4)
    (hN1 : LieSylowOver3) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h30 : Lemma14_7_30_F4) (h32 : Lemma14_7_32_F4) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK)
    (h42 : Lemma14_7_42_S5S3_F4) : Lemma14_7_43_F4 := by
  intro G _ _ T L V H S K hK hHeq n hn hLie hU
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
    exact C.false_of_u38_F4 h310 hA21 h29 hN1 h1222 h1332 h1334 hn hLie hU hB.2.1 hBT
  · obtain ⟨ρ, hρs, hρk⟩ := h42 G T L V H S K hK hHeq n hn hLie hl1K
    have := hq.2.1
    have : Nontrivial (cStar K) :=
      (QuotientGroup.mk_surjective (s := Subgroup.center (cStar K))).nontrivial
    obtain ⟨e⟩ := isAlt5_of_s5s3 hK hKn this hρs hρk
    obtain ⟨-, F, _, _, hF, ⟨e'⟩⟩ := hU
    have h1 : Nat.card (cStar K ⧸ Subgroup.center (cStar K)) = 5515776 := by
      rw [Nat.card_congr e'.toEquiv, card_psu3_eight hF]
    have h2 : Nat.card (cStar K ⧸ Subgroup.center (cStar K)) ≤ Nat.card (cStar K) :=
      Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
    have h3 : Nat.card (cStar K) = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    omega

end CFSG.Quasithin.H13.L32A.C
