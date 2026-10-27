module

public import CFSG.Quasithin.H13.L32NLem14412d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems144c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14412c

public section

namespace CFSG.Quasithin.H13.L14412

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open MatNCert M22Cert L1442M L14411 L144B

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)} {e : D.V ≃ₗ[ZMod 2] (Fin 12 → ZMod 2)}

structure Ctx6_F4 (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V V₂ : Subgroup G) (g : G)
    (D : HatModelU (fsuU T V)) (e : D.V ≃ₗ[ZMod 2] (Fin 12 → ZMod 2)) : Prop where

  base : Base_F4 G T L V V₂ g

  cardW : Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) = 2 ^ 5

  imgH : imgN D e (l32nH T V) = m22

  form : ∀ x y : D.V, D.B x y = polV q12 (e x) (e y)

  imgT : imgN D e T = PM


theorem exists_ctx6_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4)
    (h12213 : Stmt12_2_13_F4) (h12811 : Lemma12_8_11_F4) (h12812 : Lemma12_8_12_two_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h : Hyp14310One G T L V)
    (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)) (hV₂ : IsL32NPlane T V V₂)
    (hgP : g ∈ p128 T L V) (hgH : g ∉ l32nH T V) {e₀ : D.V ≃ₗ[ZMod 2] (Fin 12 → ZMod 2)}
    (hiso : IsModelIso D (l32nH T V) e₀ q12 m22)
    (hW32 : Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) = 2 ^ 5) :
    ∃ e : D.V ≃ₗ[ZMod 2] (Fin 12 → ZMod 2), Ctx6_F4 G T L V V₂ g D e := by
  have B := exists_base_F4 h1332 h1334 h1222 h12213 h12811 h12812 h37 h38 h39 h hext hV₂ hgP hgH
  have himgH := imgN_eq_of_iso hiso
  have hT := B.card_imgTN_F4 e₀ himgH (m := 8) (k := 10395) (by rw [card_m22]; norm_num)
    (by decide)
  obtain ⟨e, himgH', hform, himgT⟩ := B.exists_normalizedN_F4 e₀ himgH (form12 hext hiso)
    PM_le_m22 (IsPGroup.of_card (n := 8) (by rw [card_PM]; norm_num))
    (by rw [relIndex_PM]; decide) (by rw [hT, card_PM]; norm_num)
  exact ⟨e, B, hW32, himgH', hform, himgT⟩

namespace Ctx6_F4
open CFSG.Quasithin.H13.L14412.Ctx6_F4

variable (C : Ctx6_F4 G T L V V₂ g D e)
include C

theorem e_pi_a_F4 {a : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V) : e (D.π a) = vecN 12 v0 := by
  rcases eq_of_fixed_PM (e (D.π a)) (fun γ hγ => C.base.T_fixN_F4 e ha haV (by rw [C.imgT]; exact hγ))
    with h | h
  · exact absurd ((map_eq_zero_iff e e.injective).mp h) (C.base.pi_a_ne_F4 D ha haV)
  · exact h

theorem img_Wg_le_S0_F4 : imgN D e (CFSG.conjugate (l32nW T V V₂) g) ≤ S0 := by
  obtain ⟨a, ha, haV⟩ := C.base.abs.exists_mem_not_mem
  intro x hx
  refine mem_S0_of_fix (C.imgH ▸ imgN_mono D e C.base.WgH_F4 hx) ?_
  rw [← C.e_pi_a_F4 ha haV]
  exact C.base.Wg_fixN_F4 e ha hx

theorem img_Wg_norm_F4 : ∀ ν ∈ S0, ∀ x ∈ imgN D e (CFSG.conjugate (l32nW T V V₂) g),
    ν * x * ν⁻¹ ∈ imgN D e (CFSG.conjugate (l32nW T V V₂) g) := by
  obtain ⟨a, ha, haV⟩ := C.base.abs.exists_mem_not_mem
  intro ν hν x hx
  refine C.base.conj_mem_img_WgN_F4 e ha haV (by rw [C.imgH]; exact S0_le hν) ?_ hx
  rw [C.e_pi_a_F4 ha haV]
  exact S0_fix hν


theorem card_img_Wg_F4 : Nat.card (imgN D e (CFSG.conjugate (l32nW T V V₂) g)) = 32 := by
  rw [card_imgN, C.cardW]
  norm_num

theorem img_Wg_eq_F4 : imgN D e (CFSG.conjugate (l32nW T V V₂) g) = E0 := by
  have hP2 : IsPGroup 2 ↥PM := IsPGroup.of_card (n := 8) (by rw [card_PM]; norm_num)
  have hW2 : IsPGroup 2 ↥(imgN D e (CFSG.conjugate (l32nW T V V₂) g)) :=
    IsPGroup.of_card (n := 5) (by rw [C.card_img_Wg_F4]; norm_num)
  have hWP := le_of_normal_of_sylow C.img_Wg_le_S0_F4 PM_le_S0 hW2 hP2
    (by rw [relIndex_PM_S0]; decide) C.img_Wg_norm_F4
  exact eq_E0_of hWP C.img_Wg_norm_F4 C.card_img_Wg_F4

theorem mem_hatE_F4 : ∀ p ∈ wits, vecN 12 p.1 ∈ (D.hat (l32nE T V V₂ g)).map e.toLinearMap := by
  obtain ⟨a, ha, haV⟩ := C.base.abs.exists_mem_not_mem
  intro p hp
  obtain ⟨hp1, hp2, hp3⟩ := witB_spec p hp
  obtain ⟨x, hxE, hx⟩ := exists_mem_of_elemsOf e0B_spec.1 (unit_of_s0E e0G_mem) hp1
  have hxW : x ∈ imgN D e (CFSG.conjugate (l32nW T V V₂) g) := by
    rw [C.img_Wg_eq_F4]
    exact hxE
  have hB : D.B (e.symm (vecN 12 p.2.2)) (D.π a) = 0 := by
    rw [C.form, LinearEquiv.apply_symm_apply, C.e_pi_a_F4 ha haV, ← polN_q12, hp2]
    rfl
  have := C.base.mulVec_add_mem_hatEN_F4 e ha haV hxW hB
  rwa [hx, decN_mulVec ((subB_spec e0B_spec.1).1 _ hp1).1, ← vecN_xor, hp3] at this

theorem planeData_F4 {k : ℕ} (hk : k < 2) {a : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V) :
    PlaneDataN V₂ g D e a (oTwoUpper (Mi k)) (vecN 12 (oWs.getD k (0, 0)).1)
      (vecN 12 (oWs.getD k (0, 0)).2) := by
  have key : ∀ w ∈ (D.hat (l32nE T V V₂ g)).map e.toLinearMap,
      e.symm w ∈ D.hat (l32nE T V V₂ g) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact hx
  obtain ⟨⟨p₁, hp₁, hp₁w⟩, ⟨p₂, hp₂, hp₂w⟩⟩ := oWs_wits hk
  have hE₁ := C.mem_hatE_F4 p₁ hp₁
  have hE₂ := C.mem_hatE_F4 p₂ hp₂
  rw [hp₁w] at hE₁
  rw [hp₂w] at hE₂
  rw [oTwoUpper_Mi hk]
  refine ⟨(oWs_ne hk).1, (oWs_ne hk).2.1, (oWs_ne hk).2.2, fun y hy => ?_, ?_, ?_, ?_,
    key _ hE₁, key _ hE₂⟩
  · rw [C.e_pi_a_F4 ha haV]
    exact OS_vec hk hy
  · obtain ⟨y, hy, hyw⟩ := (OS_vec_eq hk).1
    exact ⟨y, hy, by rw [C.e_pi_a_F4 ha haV]; exact hyw⟩
  · obtain ⟨y, hy, hyw⟩ := (OS_vec_eq hk).2
    exact ⟨y, hy, by rw [C.e_pi_a_F4 ha haV]; exact hyw⟩
  · obtain ⟨y, hy, v, hv⟩ := OS_pol hk
    refine ⟨y, hy, vecN 12 v, ?_⟩
    rw [C.form, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hv]
    exact one_ne_zero

theorem exists_j_F4 : ∃ j < 2, imgN D e (lOne L (fsuV1 T V) ⊔ T) = Mi j := by
  obtain ⟨a, ha, haV⟩ := C.base.abs.exists_mem_not_mem
  have hle : imgN D e (lOne L (fsuV1 T V) ⊔ T) ≤ m22 :=
    (imgN_mono D e C.base.L1TH_F4).trans C.imgH.le
  have hP : PM ≤ imgN D e (lOne L (fsuV1 T V) ⊔ T) :=
    C.imgT.ge.trans (imgN_mono D e le_sup_right)
  have hcard : Nat.card (imgN D e (lOne L (fsuV1 T V) ⊔ T)) = 768 := by
    rw [C.base.card_img_L1TN_F4 e, C.imgT, card_PM]
  obtain ⟨l, hl, hlmove⟩ := C.base.exists_L1_move_F4 (D := D) ha haV
  have hlN := HN (L14411.L1H hl)
  refine eq_Mi_of hle hP hcard (y := matOfN e (D.ρ ⟨l, hlN⟩))
    ((mem_imgN D e).mpr ⟨l, Subgroup.mem_sup_left hl, hlN, rfl⟩) ?_
  rw [← C.e_pi_a_F4 ha haV, matOfN_mulVec]
  exact fun h => hlmove (e.injective h)

theorem img_L1_F4 {j : ℕ} (hj : j < 2) (hjeq : imgN D e (lOne L (fsuV1 T V) ⊔ T) = Mi j) :
    imgN D e (lOne L (fsuV1 T V)) = OS j := by
  rw [C.base.L1_eq_oTwoUpper_F4, imgN_oTwoUpper D e (C.base.L1TH_F4.trans HN), hjeq, oTwoUpper_Mi hj]

theorem Mi_le_F4 {k : ℕ} (hk : k < 2) : Mi k ≤ imgN D e (l32nH T V) := C.imgH ▸ Mi_le_m22 hk

theorem img_X_F4 {k : ℕ} (hk : k < 2) : imgN D e (xMN D e (Mi k)) = OS k := by
  rw [img_xMN (C.Mi_le_F4 hk), oTwoUpper_Mi hk]


theorem JH_F4 (k : ℕ) : lOne L (fsuV1 T V) ⊔ xMN D e (Mi k) ⊔ T ≤ l32nH T V :=
  sup_le (sup_le L14411.L1H (xMN_le_H e _)) C.base.TH_F4

theorem nonempty_quot_F4 {j k : ℕ} (hjk : (j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0))
    (hjeq : imgN D e (lOne L (fsuV1 T V) ⊔ T) = Mi j) :
    Nonempty (OTwoQuot (lOne L (fsuV1 T V) ⊔ xMN D e (Mi k) ⊔ T) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hj : j < 2 := by omega
  have hk : k < 2 := by omega
  have hJN : lOne L (fsuV1 T V) ⊔ xMN D e (Mi k) ⊔ T ≤
      Subgroup.normalizer (fsuU T V : Set G) := (C.JH_F4 k).trans HN
  have himg : imgN D e (lOne L (fsuV1 T V) ⊔ xMN D e (Mi k) ⊔ T) = M12 := by
    rw [imgN_sup D e (sup_le L14411.L1H (xMN_le_H e _) |>.trans HN) (C.base.TH_F4.trans HN),
      imgN_sup D e (L14411.L1H.trans HN) ((xMN_le_H e _).trans HN), C.img_L1_F4 hj hjeq,
      C.img_X_F4 hk, C.imgT, M12_eq]
    rcases hjk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · rw [sup_comm (OS 1)]
  let φ : ↥(lOne L (fsuV1 T V) ⊔ xMN D e (Mi k) ⊔ T) →* ↥M12 :=
    (homN D e hJN).codRestrict M12 fun x => by
      rw [← himg, ← range_homN D e hJN]
      exact ⟨x, rfl⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨γ, hγ⟩
    rw [← himg, ← range_homN D e hJN] at hγ
    obtain ⟨x, rfl⟩ := hγ
    exact ⟨x, rfl⟩
  have hker : IsPGroup 2 (chi.comp φ).ker := by
    rintro ⟨x, hx⟩
    have h4 := pow_four_of_chi (MonoidHom.mem_ker.mp hx)
    have hxx : homN D e hJN (x ^ 2 ^ 2) = 1 := by
      rw [map_pow]
      exact h4
    have hxQ : ((x ^ 2 ^ 2 : ↥(lOne L (fsuV1 T V) ⊔ xMN D e (Mi k) ⊔ T)) : G) ∈
        pCoreOf 2 (l32nH T V) :=
      (C.base.matOfN_eq_one_iff_F4 D e (C.JH_F4 k (x ^ 2 ^ 2).2)).mp hxx
    obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (l32nH T V) ⟨_, hxQ⟩
    refine ⟨n + 2, Subtype.ext (Subtype.ext ?_)⟩
    have h1 : ((x : G) ^ 2 ^ 2) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [show n + 2 = 2 + n by ring, pow_add, pow_mul, h1]
  exact nonempty_quot_equiv_of_surj (chi.comp φ) (chi_surjective.comp hφ) hker s33_normal_two

end Ctx6_F4

theorem y1444Claim_of_ctx6_F4 (C : Ctx6_F4 G T L V V₂ g D e) : Y1444Claim T L V V₂ g := by
  obtain ⟨a, ha, haV⟩ := C.base.abs.exists_mem_not_mem
  obtain ⟨j, hj, hjeq⟩ := C.exists_j_F4
  obtain ⟨k, hk, hjk⟩ : ∃ k < 2, (j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0) := by
    interval_cases j
    · exact ⟨1, by norm_num, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨0, by norm_num, Or.inr ⟨rfl, rfl⟩⟩
  have hP := C.planeData_F4 hk ha haV
  refine ⟨xMN D e (Mi k), ⟨xMN_le_H e _,
    C.base.T_le_normalizer_xMN_F4 (C.imgT.le.trans (PM_le_Mi k)), oTwoUpper_xMN e _,
    C.base.relIndex_xMN_F4 (C.img_X_F4 hk) (index_pCore_OS hk),
    C.base.card_commutator_xMN_F4 (C.Mi_le_F4 hk) ha haV hP,
    C.base.commutator_le_E_xMN_F4 (C.Mi_le_F4 hk) ha haV hP⟩, fun h => ?_, C.nonempty_quot_F4 hjk hjeq⟩
  have h1 := C.img_X_F4 hk
  rw [h, C.img_L1_F4 hj hjeq] at h1
  rcases hjk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact OS_ne h1
  · exact OS_ne h1.symm

theorem lemma14413BigM22_of_inputs_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h12811 : Lemma12_8_11_F4)
    (h12812 : Lemma12_8_12_two_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    Lemma14413BigM22_F4 := by
  intro G _ _ T L V h hext _ V₂ g hV₂ hgP hgH D h6
  obtain ⟨e₀, hiso, hW32⟩ := h6
  obtain ⟨e, C⟩ := exists_ctx6_F4 h1332 h1334 h1222 h12213 h12811 h12812 h37 h38 h39 h hext hV₂
    hgP hgH hiso hW32
  exact y1444Claim_of_ctx6_F4 C

end CFSG.Quasithin.H13.L14412
