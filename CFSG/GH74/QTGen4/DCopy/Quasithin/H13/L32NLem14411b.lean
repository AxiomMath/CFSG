module

public import CFSG.Quasithin.H13.L32NLem14411b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1444a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneAbsInst

public section

namespace CFSG.Quasithin.H13.L14411

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Mat8Cert S7Cert L1442M

structure Ctx0_F4 (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V V₂ : Subgroup G) (g : G)
    (D : HatModelU (fsuU T V)) (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) : Prop where

  h1332 : Stmt13_3_2_F4

  h1334 : A6.Stmt13_3_4_F4

  h1222 : Stmt12_2_2_F4

  hyp : Hyp14310One G T L V

  ext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)

  plane : IsL32NPlane T V V₂

  gP : g ∈ p128 T L V

  gH : g ∉ l32nH T V

  zU : centerOf (fsuU T V) = fsuV1 T V

  cHat : l32nCHat T V = pCoreOf 2 (l32nH T V)

  s1282 : Setting1282One G T L V 3 (fsuV1 T V) V₂

  abs : L128A.Setting V₂ (fsuV1 T V) (oTwoUpper (p128 T L V)) T

  uA : L128A.uA V₂ (fsuV1 T V) = fsuU T V

  wwE : ⁅l32nW T V V₂, CFSG.conjugate (l32nW T V V₂) g⁆ ≤ l32nE T V V₂ g

  nWg : l32nH T V ⊓ Subgroup.normalizer (V₂ : Set G) ≤
    Subgroup.normalizer ((CFSG.conjugate (l32nW T V V₂) g ⊔ l32nCHat T V : Subgroup G) : Set G)

  cardW : Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) = 2 ^ 3

  imgH : img8 D e (l32nH T V) = s7

  form : ∀ x y : D.V, D.B x y = b4V (e x) (e y)

structure Ctx_F4 (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V V₂ : Subgroup G) (g : G)
    (D : HatModelU (fsuU T V)) (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) : Prop
    extends Ctx0_F4 G T L V V₂ g D e where

  imgT : img8 D e T = P7

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)} {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)}

namespace Ctx0_F4
open CFSG.Quasithin.H13.L14411.Ctx0_F4

variable (C : Ctx0_F4 G T L V V₂ g D e)
include C

theorem UT_F4 : fsuU T V ≤ T := C.uA ▸ C.abs.uA_le_T

theorem TH_F4 : T ≤ l32nH T V := C.hyp.le_l32nH_F4 (stmtL32NModule_of_inputs_F4 C.h1332 C.h1334)

theorem UH_F4 : fsuU T V ≤ l32nH T V := C.UT_F4.trans C.TH_F4

theorem comm_center_F4 : ∀ a ∈ fsuU T V, ∀ b ∈ fsuU T V, a * b * a⁻¹ * b⁻¹ ∈ centerOf (fsuU T V) :=
  L1444.comm_mem_centerOf C.ext

theorem matOf_eq_one_iff_F4 {h : G} (hh : h ∈ l32nH T V) :
    matOf e (D.ρ ⟨h, HN hh⟩) = 1 ↔ h ∈ pCoreOf 2 (l32nH T V) := by
  rw [← C.cHat, ← L14332.rho_eq_one_iff_mem hh (HN hh), ← (matOf e).map_one]
  exact (matOf_injective e).eq_iff

theorem QT_F4 : pCoreOf 2 (l32nH T V) ≤ T :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  le_of_normalizes (isSylowTwoOf_of_quasithinIsSylowTwo C.hyp.fsu.sylow C.TH_F4)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
    (C.TH_F4.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))

theorem card_img_eq_F4 {Y : Subgroup G} (hYH : Y ≤ l32nH T V) :
    Nat.card (D.img Y) = (pCoreOf 2 (l32nH T V)).relIndex Y := by
  refine L128A.HatU.card_img_eq_relIndex D (hYH.trans HN) fun x hx => ?_
  constructor
  · rintro ⟨hxN, h1⟩
    rw [← C.cHat]
    exact (L14332.rho_eq_one_iff_mem (hYH hx) hxN).mp h1
  · intro hxQ
    refine ⟨HN (hYH hx), ?_⟩
    rw [← C.cHat] at hxQ
    exact (L14332.rho_eq_one_iff_mem (hYH hx) (HN (hYH hx))).mpr hxQ

end Ctx0_F4

section Cert

namespace Ctx0_F4
open CFSG.Quasithin.H13.L14411.Ctx0_F4

variable (C : Ctx0_F4 G T L V V₂ g D e)
include C

theorem card_imgT_F4 : Nat.card (img8 D e T) = 16 := by
  have hH : (pCoreOf 2 (l32nH T V)).relIndex (l32nH T V) = 5040 := by
    rw [← C.card_img_eq_F4 le_rfl, ← card_img8 D e, C.imgH, card_s7]
  have hT : Nat.card (img8 D e T) = (pCoreOf 2 (l32nH T V)).relIndex T := by
    rw [card_img8, C.card_img_eq_F4 C.TH_F4]
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 (l32nH T V)) T (l32nH T V) C.QT_F4 C.TH_F4
  rw [hH, ← hT] at hmul

  have hodd : ¬ 2 ∣ T.relIndex (l32nH T V) :=
    (isSylowTwoOf_of_quasithinIsSylowTwo C.hyp.fsu.sylow C.TH_F4).2.2

  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 ↥(img8 D e T) := by
    rw [img8_eq_map]
    exact (C.hyp.fsu.sylow.1.of_equiv
      (Subgroup.subgroupOfEquivOfLe (C.TH_F4.trans HN)).symm).map _
  obtain ⟨m, hm⟩ := h2.exists_card_eq
  rw [hm] at hmul ⊢
  have hm13 : m < 13 := by
    by_contra hc
    have h13 : 2 ^ 13 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpos : 0 < T.relIndex (l32nH T V) := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, mul_zero] at hmul
      omega
    nlinarith
  interval_cases m <;> norm_num at hmul ⊢ <;> omega

end Ctx0_F4

theorem exists_ctx_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h12811 : Lemma12_8_11_F4)
    (h12812 : Lemma12_8_12_two_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h : Hyp14310One G T L V) (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V))
    (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V) (hgH : g ∉ l32nH T V)
    (h4 : Case1442Four T V V₂ g D) :
    ∃ e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2), Ctx_F4 G T L V V₂ g D e := by
  obtain ⟨e₀, hiso, hW8, -⟩ := h4
  have h13322 := stmt13_3_2_two_of_stmt13_3_2_F4 h1332
  have hV := stmtL32NModule_of_inputs_F4 h1332 h1334
  have hs := h.setting1282One_F4 h13322 hV hV₂
  have hZ2 : Nat.card ↥(centerOf (fsuU T V)) = 2 := by
    rw [l32n_card_centerOf]
    exact hext.2.2.2

  have himgH : img8 D e₀ (l32nH T V) = s7 := by
    ext γ
    rw [mem_img8]
    constructor
    · rintro ⟨y, hy, hyN, rfl⟩
      obtain ⟨γ', hγ', hγ'e⟩ := (hiso.img _).mp (L128A.HatU.rho_mem_img D hy hyN)
      rwa [(matOf_eq_iff e₀ _ γ').mpr hγ'e]
    · intro hγ
      have hψ : e₀.trans ((linOf γ).trans e₀.symm) ∈ D.img (l32nH T V) :=
        (hiso.img _).mpr ⟨γ, hγ, fun v => by simp [linOf_apply]⟩
      obtain ⟨y, hy, hyN, hye⟩ := (L128A.HatU.mem_img D).mp hψ
      refine ⟨y, hy, hyN, ?_⟩
      rw [hye, matOf_eq_iff]
      intro v
      simp [linOf_apply]
  have hform₀ := form_of_quad D e₀ hZ2 (L1444.comm_mem_centerOf hext) hiso.quad
  have C₀ : Ctx0_F4 G T L V V₂ g D e₀ :=
    { h1332 := h1332, h1334 := h1334, h1222 := h1222, hyp := h, ext := hext, plane := hV₂,
      gP := hgP, gH := hgH, zU := L1444.zU_eq_F4 h1332 h1334 h1222 h12213 h hext,
      cHat := L1444.cHat_eq_F4 h1332 h1334 h1222 h12213 h37 h38 h39 h hext, s1282 := hs,
      abs := L128P.setting128A_F4 h1222 h12213 hs, uA := (lemma12_8_8_six_F4 h1222 hs).symm,
      wwE := (h12811 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgH).1,
      nWg := (h12812 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgH).1, cardW := hW8,
      imgH := himgH, form := hform₀ }

  have hKs : img8 D e₀ T ≤ s7 := himgH ▸ img8_mono D e₀ C₀.TH_F4
  have hK16 := C₀.card_imgT_F4
  have hK2 : IsPGroup 2 ↥(img8 D e₀ T) :=
    IsPGroup.of_card (n := 4) (by rw [hK16]; norm_num)
  have hP2 : IsPGroup 2 ↥P7 := IsPGroup.of_card (n := 4) (by rw [card_P7]; norm_num)
  obtain ⟨c, hcs, hc⟩ := exists_conj_of_sylow hKs P7_le_s7 hK2 hP2
    (by rw [relIndex_s7 hKs hK16]; decide) (by rw [relIndex_s7 P7_le_s7 card_P7]; decide)

  obtain ⟨y, hyH, hyN, hyc⟩ := (mem_img8 D e₀).mp (himgH ▸ hcs)
  have hce : ∀ x : D.V, (c : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e₀ x) =
      e₀ (D.ρ ⟨y, hyN⟩ x) := fun x => by rw [← hyc, matOf_mulVec]
  refine ⟨e₀.trans (linOf c), { C₀ with imgH := ?_, form := ?_, imgT := ?_ }⟩
  · rw [img8_trans, himgH, map_conj_of_mem hcs]
  · intro x y'
    simp only [LinearEquiv.trans_apply, linOf_apply, hce]
    rw [← hform₀, L128A.HatU.B_rho]
  · have hle : img8 D (e₀.trans (linOf c)) T ≤ P7 := by
      rw [img8_trans]
      rintro _ ⟨x, hx, rfl⟩
      exact hc x hx
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_P7, img8_trans, Subgroup.card_map_of_injective (MulEquiv.injective _), hK16]

end Cert

end CFSG.Quasithin.H13.L14411
