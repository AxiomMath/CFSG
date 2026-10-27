module

public import CFSG.Quasithin.H13.L32AL2i
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL2g
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL2h

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H13.L32A.C
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V K W : Subgroup G} {t₀ : G}

namespace TopCtx

variable (X : TopCtx T L V K W t₀) [IsMulCommutative ↥(conjClosure V (A6.g1 T V))]

theorem exists_pair_F4 (hA37 : A37ForSQTK) (h29 : Thm14_7_29_F4) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    ∃ y₁ ∈ X.img K, ∃ y₂ ∈ X.img (K.map (MulAut.conj t₀ : G →* G)), y₁ ^ 3 = 1 ∧
      y₂ ^ 3 = 1 ∧ vHat V (A6.g1 T V) W ≠ ⊥ ∧ (∀ v ∈ vHat V (A6.g1 T V) W, y₁ v = y₂ v) ∧
      ∀ v ∈ vHat V (A6.g1 T V) W, y₁ v = v → v = 1 := by
  have C := X.C
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 C.S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 C.S.hyp h1222 h1332 h1334 hV2
  obtain ⟨y, hyL, hy3, hfpfy⟩ := exists_l1_fpf_F4 C.S.hyp hMod h1222 h1332 h1334
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hy : y ∈ l1 T L V := by rw [← hl1]; exact hyL
  have hyH : y ∈ A6.g1 T V := Setting147.l1H' C.S hy
  obtain ⟨k₁, hk₁K, k₂, hk₂K, he, hk₁3, hk₂3, hk₁, hk₂⟩ := C.decomp hA37 hy hy3
  obtain ⟨β₁, β₂, rfl, rfl, hβ₁X, -, hβ12, hyβ⟩ :=
    CtxL2Same.exists_same_action_F4 C hA37 h29 h1222 h1332 h1334 S14 hy hy3 hfpfy hk₁K hk₂K he hk₁
      hk₂
  have hVW := Setting147.inf_V_eq_F4 X.top.S h1222 h1332 h1334 X.top.hV₁W X.top.hWU X.top.hHW
  have hF := X.top.hF
  have hcentral : ∀ z ∈ fsuV1 T V, ∀ b ∈ A6.g1 T V, z * b = b * z := fun z hz b hb =>
    (Subgroup.mem_centralizer_iff.mp (hF.H_le_centralizer hb)) z hz
  refine ⟨X.top.act β₁, ?_, X.top.act β₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [img_eq_map]
    exact ⟨_, hk₁K, rfl⟩
  · rw [img_eq_map]
    exact ⟨_, hk₂K, rfl⟩
  · rw [← X.actDot_mk β₁, ← map_pow, hk₁3, map_one]
  · rw [← X.actDot_mk β₂, ← map_pow, hk₂3, map_one]
  ·
    obtain ⟨v, hv, hv1⟩ : ∃ v ∈ V, v ∉ fsuV1 T V := by
      by_contra hno
      push Not at hno
      have := Subgroup.card_le_of_le (show V ≤ fsuV1 T V from hno)
      rw [S14.card_V_F4, S14.card_V1_F4] at this
      omega
    intro hbot
    have hmem : InternalSec.secMk (W.subgroupOf (conjClosure V (A6.g1 T V)))
        ⟨v, le_conjClosure V _ hv⟩ ∈ vHat V (A6.g1 T V) W := ⟨⟨v, le_conjClosure V _ hv⟩, hv, rfl⟩
    rw [hbot, Subgroup.mem_bot, A6.A6Mod.secMk_eq_one_iff] at hmem
    apply hv1
    have : v ∈ V ⊓ W := Subgroup.mem_inf.mpr ⟨hv, hmem⟩
    rwa [hVW] at this
  ·
    rintro _ ⟨u, hu, rfl⟩
    have hu' : (u : G) ∈ V := hu
    rw [X.top.act_secMk, X.top.act_secMk, ← mul_inv_eq_one, ← map_inv, ← map_mul,
      A6.A6Mod.secMk_eq_one_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe]
    obtain ⟨-, -, hβv⟩ := L32NSet14.mem_trivSub.mp hβ12
    have h1 := (Subgroup.mem_normalizer_iff.mp hβ₁X.2 _).mp (hβv (u : G) hu')
    apply X.top.hV₁W
    have e : (β₁ : G) * u * (β₁ : G)⁻¹ * ((β₂ : G) * u * (β₂ : G)⁻¹)⁻¹ =
        ((β₁ : G) * (((β₁ : G)⁻¹ * β₂) * u * ((β₁ : G)⁻¹ * β₂)⁻¹ * (u : G)⁻¹) * (β₁ : G)⁻¹)⁻¹ := by
      group
    rw [e]
    exact inv_mem h1
  ·
    rintro _ ⟨u, hu, rfl⟩ hfix
    have hu' : (u : G) ∈ V := hu
    rw [X.top.act_secMk, ← mul_inv_eq_one, ← map_inv, ← map_mul,
      A6.A6Mod.secMk_eq_one_iff] at hfix
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe] at hfix
    have hβV : (β₁ : G) * u * (β₁ : G)⁻¹ * (u : G)⁻¹ ∈ V :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp hβ₁X.1 _).mp hu') (inv_mem hu')
    have h1 : (β₁ : G) * u * (β₁ : G)⁻¹ * (u : G)⁻¹ ∈ fsuV1 T V := by
      have : (β₁ : G) * u * (β₁ : G)⁻¹ * (u : G)⁻¹ ∈ V ⊓ W := Subgroup.mem_inf.mpr ⟨hβV, hfix⟩
      rwa [hVW] at this
    obtain ⟨-, -, hxv⟩ := L32NSet14.mem_trivSub.mp hyβ
    have h2 := hxv (u : G) hu'
    have hy2H : y ^ 2 ∈ A6.g1 T V := pow_mem hyH 2
    set c := ((y ^ 2)⁻¹ * β₁) * (u : G) * ((y ^ 2)⁻¹ * β₁)⁻¹ * (u : G)⁻¹ with hc
    have hcy : c * y ^ 2 = y ^ 2 * c := hcentral c h2 _ hy2H
    have h3 : y ^ 2 * (u : G) * (y ^ 2)⁻¹ * (u : G)⁻¹ =
        c⁻¹ * ((β₁ : G) * u * (β₁ : G)⁻¹ * (u : G)⁻¹) := by
      calc y ^ 2 * (u : G) * (y ^ 2)⁻¹ * (u : G)⁻¹
          = c⁻¹ * (y ^ 2 * c * (y ^ 2)⁻¹) * (y ^ 2 * (u : G) * (y ^ 2)⁻¹ * (u : G)⁻¹) := by
            rw [← hcy]
            group
        _ = c⁻¹ * ((β₁ : G) * u * (β₁ : G)⁻¹ * (u : G)⁻¹) := by
            rw [hc]
            group
    have h4 : y ^ 2 * (u : G) * (y ^ 2)⁻¹ * (u : G)⁻¹ ∈ fsuV1 T V := by
      rw [h3]
      exact mul_mem (inv_mem h2) h1
    have hy2 : y ^ 2 = y⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ]
      exact hy3
    have h6 := (Subgroup.mem_normalizer_iff.mp (hF.toHypF91.H_normalizes_V₁ hyH) _).mp h4
    have e : y * (u : G) * y⁻¹ * (u : G)⁻¹ =
        (y * (y ^ 2 * (u : G) * (y ^ 2)⁻¹ * (u : G)⁻¹) * y⁻¹)⁻¹ := by
      rw [hy2]
      group
    have hu1 := hfpfy (u : G) hu' (by rw [e]; exact inv_mem h6)
    rw [A6.A6Mod.secMk_eq_one_iff]
    exact X.top.hV₁W hu1

theorem t_not_mem_normalizer_F4 (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4)
    (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    X.top.act ⟨t₀, X.C.ht₀H⟩ ∉
      Subgroup.normalizer (X.img K : Set (MulAut (Hat V (A6.g1 T V) W))) := by
  intro hn
  have C := X.C
  have hinj := X.actDot_injective_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  have hK1 : ∀ k ∈ modO2Image (A6.g1 T V) K, k = 1 := by
    intro k hk
    apply C.eq_one_of_mem_kb_kt hA37 hk
    have h1 : X.actDot k ∈ X.img K := by rw [img_eq_map]; exact ⟨k, hk, rfl⟩
    have h2 : X.actDot k ∈ X.img (K.map (MulAut.conj t₀ : G →* G)) := by
      rw [img_Kt_eq]
      refine ⟨(X.top.act ⟨t₀, C.ht₀H⟩)⁻¹ * X.actDot k * X.top.act ⟨t₀, C.ht₀H⟩, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) _).mp h1
        simpa using this
      · simp [MulAut.conj_apply, mul_assoc]
    rw [img_eq_map] at h2
    obtain ⟨k', hk', hkk'⟩ := h2
    rw [hinj hkk'] at hk'
    exact hk'
  have : IsSimpleGroup ↥(modO2Image (A6.g1 T V) K) := C.isSimpleGroup_kb
  obtain ⟨⟨a, ha⟩, ha1⟩ := exists_ne (1 : ↥(modO2Image (A6.g1 T V) K))
  exact ha1 (Subtype.ext (hK1 a ha))

theorem omega4_F4 (hD36 : D36) (hD37 : D37) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK)
    (h76 : Lemma14_7_6_F4) (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (h29 : Thm14_7_29_F4) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    Omega4PlusModule (autSub (X.img (conjClosure K T)) ⊤) 2 := by
  have hV : ∀ w : Hat V (A6.g1 T V) W, w ^ 2 = 1 := fun w => by
    rw [pow_two]; exact X.top.sec_sq w
  set t := X.top.act ⟨t₀, X.C.ht₀H⟩ with ht

  obtain ⟨V', hV'⟩ := X.exists_irrPlusOn_F4 hA37 h1222 h1332 h1334
  have hD := X.d31_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 hV'.1
  have hne : V' ≠ ⊥ := (bot_le.trans_lt hV'.1.2.2.2.1).ne'
  have hVT : orbSup (X.img T) V' = ⊤ := X.orbSup_eq_top hne hV'.1.2.1
  obtain ⟨B, hBL, hB⟩ := X.top.hF.F916_3_aux
  have hBT : B ≤ T := hBL.trans (L32A.pCoreOf_le_of_le X.R.S.hyp le_sup_right)
  have hA := X.qOff_img_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 hB hBT
  rw [← hVT] at hA
  have hstd : D3Std (X.img (A6.g1 T V)) (X.img (conjClosure K T)) (X.img T) (X.img K) V' :=
    ⟨hD, hA.qhat_VT hD.exp, by rw [hVT]; exact hV'⟩
  have htL := X.t_not_mem_normalizer_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  have hMp : X.img (conjClosure K T) = X.img K ⊔ conjAutSub t (X.img K) := by
    rw [img_K₀_eq, img_Kt_eq]
  have hsq := X.t_sq_mem_normalizer

  have hs1 : ∀ g ∈ X.img K, t⁻¹ * g * t ∈ conjAutSub t (X.img K) := by
    intro g hg
    refine ⟨(t * t)⁻¹ * g * (t * t), ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (inv_mem hsq) g).mp hg
      simpa using this
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hs2 : ∀ g ∈ conjAutSub t (X.img K), t⁻¹ * g * t ∈ X.img K := by
    rintro _ ⟨ℓ, hℓ, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hℓ
  have hs1' : ∀ g ∈ conjAutSub t (X.img K), t⁻¹⁻¹ * g * t⁻¹ ∈ X.img K := by
    rintro _ ⟨ℓ, hℓ, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp hsq ℓ).mp hℓ
    simpa [MulAut.conj_apply, mul_assoc] using this
  have hs2' : ∀ g ∈ X.img K, t⁻¹⁻¹ * g * t⁻¹ ∈ conjAutSub t (X.img K) := fun g hg =>
    ⟨g, hg, by simp [MulAut.conj_apply]⟩

  obtain ⟨y₁, hy₁, y₂, hy₂, hy3, hy3', hP, hsame, hfpf⟩ :=
    X.exists_pair_F4 hA37 h29 h1222 h1332 h1334
  rw [img_Kt_eq] at hy₂
  have hfix : fixV (X.img (conjClosure K T)) = ⊥ := X.fixV_img_K₀_F4 hA37 h1222 h1332 h1334
  by_cases hVeq : V' = orbSup (X.img T) V'
  · have hVtop : V' = ⊤ := hVeq.trans hVT
    rcases hD37 _ _ _ _ _ _ hstd hVeq t X.t_mem_img htL hMp with ⟨n, hn1, hn2⟩ | ⟨hn1, -⟩
    · rw [hVtop] at hn1 hn2
      obtain ⟨φ⟩ := X.nonempty_equiv_img_K_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
      have h60 : Nat.card ↥(autSub (X.img K) ⊤) = 60 := by
        rw [Nat.card_congr (autSubTopEquiv _).toEquiv, Nat.card_congr φ.toEquiv,
          nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        rfl
      have hc := Z4c2.card_of_isPSL_two_two hn1
      rw [h60] at hc
      have hn : n = 2 := by
        rcases Nat.lt_or_ge n 3 with h | h
        · interval_cases n
          · norm_num at hc
          · norm_num at hc
          · rfl
        · exfalso
          have h8 : 8 ≤ 2 ^ n := by
            calc 8 = 2 ^ 3 := by norm_num
              _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
          have h64 : 64 ≤ (2 ^ n) ^ 2 := by
            calc 64 = 8 ^ 2 := by norm_num
              _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h8 2
          have h504 : 8 * 63 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h8 (by omega)
          omega
      rw [hn] at hn2
      exact hn2
    · exfalso
      rw [hVtop] at hn1
      obtain ⟨φ⟩ := X.nonempty_equiv_img_K_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
      have h1 := SBc11.card_of_isPSL_three_two hn1
      rw [Nat.card_congr (autSubTopEquiv _).toEquiv, Nat.card_congr φ.toEquiv,
        nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
      exact absurd h1 (by decide)
  · exfalso
    have hlt : V' < orbSup (X.img T) V' := lt_of_le_of_ne (le_orbSup _ _) hVeq
    rcases hD36.1 _ _ _ _ _ _ hstd hlt t X.t_mem_img htL hMp with hc | hc
    · obtain ⟨-, ⟨hsum, hA'⟩, -⟩ := hc
      rw [hVT, hfix, inf_bot_eq] at hsum
      rw [hVT] at hA'
      exact false_of_sum hV hs1 hs2 hA' (hsum.1.trans (sup_bot_eq _)).le hy₁ hy₂ hy3 hP hsame
        hfpf
    · obtain ⟨-, ⟨hsum, hA'⟩, -⟩ := hc
      rw [hVT, hfix, inf_bot_eq] at hsum
      rw [hVT, conjAutSub_inv_conjAutSub] at hA'
      exact false_of_sum hV hs1' hs2' hA' (hsum.1.trans (sup_bot_eq _)).le hy₂ hy₁ hy3' hP
        (fun v hv => (hsame v hv).symm) (fun v hv h => hfpf v hv ((hsame v hv).trans h))

end TopCtx

end CFSG.Quasithin.H13.L32A.L2
