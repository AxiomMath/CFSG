module

public import CFSG.Quasithin.H13.L32NLem14410b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems144d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14410a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem144Bc

public section

namespace CFSG.Quasithin.H13.L14410

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Mat8Cert S7Cert S8Cert G5Cert L1442M L14411 L144B

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)} {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)}

structure Ctx5_F4 (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V V₂ : Subgroup G) (g : G)
    (D : HatModelU (fsuU T V)) (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) : Prop where

  base : Base_F4 G T L V V₂ g

  cardW : Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) = 2 ^ 3

  imgH : img8 D e (l32nH T V) = g5 true true

  form : ∀ x y : D.V, D.B x y = b5V (e x) (e y)

  imgT : img8 D e T = PS


theorem exists_ctx5_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4)
    (h12213 : Stmt12_2_13_F4) (h12811 : Lemma12_8_11_F4) (h12812 : Lemma12_8_12_two_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h : Hyp14310One G T L V)
    (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)) (hV₂ : IsL32NPlane T V V₂)
    (hgP : g ∈ p128 T L V) (hgH : g ∉ l32nH T V) {e₀ : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)}
    (hiso : IsModelIso D (l32nH T V) e₀ (q5 true) (g5 true true))
    (hW8 : Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) = 2 ^ 3) :
    ∃ e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2), Ctx5_F4 G T L V V₂ g D e := by
  have B := exists_base_F4 h1332 h1334 h1222 h12213 h12811 h12812 h37 h38 h39 h hext hV₂ hgP hgH
  have himgH := img8_eq_of_iso hiso
  have hT16 := B.card_imgT_F4 e₀ himgH (m := 4) (k := 45) (by rw [card_gS]; norm_num) (by decide)
  obtain ⟨e, himgH', hform, himgT⟩ := B.exists_normalized_F4 e₀ himgH (form5 hext hiso)
    PS_le_gS (IsPGroup.of_card (n := 4) (by rw [card_PS]; norm_num))
    (by rw [relIndex_PS]; decide) (by rw [hT16, card_PS]; norm_num)
  exact ⟨e, B, hW8, himgH', hform, himgT⟩

namespace Ctx5_F4
open CFSG.Quasithin.H13.L14410.Ctx5_F4

variable (C : Ctx5_F4 G T L V V₂ g D e)
include C

theorem e_pi_a_F4 {a : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V) : e (D.π a) = vec8 vS := by
  rcases eq_of_fixed_PS (e (D.π a)) (fun γ hγ => C.base.T_fix_F4 e ha haV (by rw [C.imgT]; exact hγ))
    with h | h
  · exact absurd ((map_eq_zero_iff e e.injective).mp h) (C.base.pi_a_ne_F4 D ha haV)
  · exact h

theorem img_Wg_le_F4 : img8 D e (CFSG.conjugate (l32nW T V V₂) g) ≤ PS := by
  obtain ⟨a, ha, haV⟩ := C.base.abs.exists_mem_not_mem
  intro x hx
  refine mem_PS_of_fix (C.imgH ▸ img8_mono D e C.base.WgH_F4 hx) ?_
  rw [← C.e_pi_a_F4 ha haV]
  exact C.base.Wg_fix_F4 e ha hx


theorem card_img_Wg_F4 : Nat.card (img8 D e (CFSG.conjugate (l32nW T V V₂) g)) = 8 := by
  rw [card_img8, C.cardW]
  norm_num

theorem mem_img_Wg_of_central_F4 {z : GL (Fin 8) (ZMod 2)}
    (hz : colsOf (z : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ zPG) :
    z ∈ img8 D e (CFSG.conjugate (l32nW T V V₂) g) := by
  set K := img8 D e (CFSG.conjugate (l32nW T V V₂) g) with hK
  have hzP : z ∈ PS := (mem_PS_iff z).mpr (zB_spec.1 _ hz).1
  by_contra hzK
  set KZ : Subgroup (GL (Fin 8) (ZMod 2)) := K ⊔ Subgroup.zpowers z with hKZ
  have hKz : KZ ≤ PS := sup_le C.img_Wg_le_F4 ((Subgroup.zpowers_le).mpr hzP)

  have hcomm : KZ ≤ Subgroup.centralizer (KZ : Set (GL (Fin 8) (ZMod 2))) := by
    have hzc : Subgroup.zpowers z ≤ Subgroup.centralizer (PS : Set (GL (Fin 8) (ZMod 2))) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro p hp
      exact (zPS_central hz hp).symm
    have hK : K ≤ Subgroup.centralizer (KZ : Set (GL (Fin 8) (ZMod 2))) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hle : KZ ≤ Subgroup.centralizer ({k} : Set (GL (Fin 8) (ZMod 2))) := by
        refine sup_le (fun k' hk' => ?_) (fun w hw => ?_)
        · rw [Subgroup.mem_centralizer_iff]
          intro k'' hk''
          rw [Set.mem_singleton_iff] at hk''
          subst hk''
          exact (C.base.img_Wg_comm_F4 e _ hk' _ hk).symm
        · rw [Subgroup.mem_centralizer_iff]
          intro k'' hk''
          rw [Set.mem_singleton_iff] at hk''
          subst hk''
          exact (Subgroup.mem_centralizer_iff.mp (hzc hw) _ (C.img_Wg_le_F4 hk))
      exact (Subgroup.mem_centralizer_iff.mp (hle hy) k rfl).symm
    refine sup_le hK fun w hw => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hzc hw) y (hKz hy))

  have hlt : K < KZ :=
    lt_of_le_of_ne le_sup_left fun h => hzK (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have hcard : Nat.card ↥KZ = 16 := by
    have h1 := Subgroup.card_dvd_of_le hKz
    rw [card_PS] at h1
    have h2 := Subgroup.card_lt_of_lt hlt
    rw [C.card_img_Wg_F4] at h2
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show _ ∣ 2 ^ 4 from h1)
    rw [hk'] at h2 ⊢
    interval_cases k <;> simp_all
  have hPeq : KZ = PS :=
    Subgroup.eq_of_le_of_card_ge hKz (by rw [hcard, card_PS])
  obtain ⟨p, hp, p', hp', hpp'⟩ := not_comm_PS
  rw [← hPeq] at hp hp'
  exact hpp' (Subgroup.mem_centralizer_iff.mp (hcomm hp') p hp)

theorem mem_hatE_F4 : ∀ p ∈ eWS, vec8 (mv8 p.1 p.2 ^^^ p.2) ∈
    (D.hat (l32nE T V V₂ g)).map e.toLinearMap := by
  obtain ⟨a, ha, haV⟩ := C.base.abs.exists_mem_not_mem
  intro p hp
  obtain ⟨hp1, hp2⟩ := wB_spec.1 p hp
  have hval : Valid8 p.1 := (subB_spec CFSG.Quasithin.H13.G5Cert.pB_spec.2.1).1 _ (zB_spec.1 _ hp1).1
  obtain ⟨x, hx⟩ : ∃ x : GL (Fin 8) (ZMod 2), (x : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 p.1 := by
    obtain ⟨w₀, hw₀⟩ := mem_elemsOf (zB_spec.1 _ hp1).1
    obtain ⟨u, -, hu⟩ := exists_evalW pSG (subB_spec CFSG.Quasithin.H13.G5Cert.pB_spec.2.1).2.2.2.2
      (unit_of_gSE CFSG.Quasithin.H13.G5Cert.pB_spec.2.2.1) w₀
    exact ⟨u, by rw [hu, hw₀]⟩
  have hxz : colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ zPG := by
    rw [hx, colsOf_dec8 hval]
    exact hp1
  have hxW := C.mem_img_Wg_of_central_F4 hxz
  have hB : D.B (e.symm (vec8 p.2)) (D.π a) = 0 := by
    rw [C.form, LinearEquiv.apply_symm_apply, C.e_pi_a_F4 ha haV, ← b5N_spec, hp2]
    rfl
  have := C.base.mulVec_add_mem_hatE_F4 e ha haV hxW hB
  rwa [hx, dec8_mulVec, ← vec8_xor] at this

theorem planeData_F4 {k : ℕ} (hk : k < 2) {a : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V) :
    PlaneData V₂ g D e a (oTwoUpper (MS k)) (vec8 (oWsS.getD k (0, 0)).1)
      (vec8 (oWsS.getD k (0, 0)).2) := by
  have hE := oWsS_mem hk _ C.mem_hatE_F4
  have key : ∀ w ∈ (D.hat (l32nE T V V₂ g)).map e.toLinearMap,
      e.symm w ∈ D.hat (l32nE T V V₂ g) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact hx
  rw [oTwoUpper_MS hk]
  refine ⟨(oWsS_ne hk).1, (oWsS_ne hk).2.1, (oWsS_ne hk).2.2, fun y hy => ?_, ?_, ?_, ?_,
    key _ hE.1, key _ hE.2⟩
  · rw [C.e_pi_a_F4 ha haV]
    exact OS_vec hk hy
  · obtain ⟨y, hy, hyw⟩ := (OS_vec_eq hk).1
    exact ⟨y, hy, by rw [C.e_pi_a_F4 ha haV]; exact hyw⟩
  · obtain ⟨y, hy, hyw⟩ := (OS_vec_eq hk).2
    exact ⟨y, hy, by rw [C.e_pi_a_F4 ha haV]; exact hyw⟩
  · obtain ⟨y, hy, v, hv⟩ := OS_b5 hk
    refine ⟨y, hy, vec8 v, ?_⟩
    rw [C.form, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hv]
    exact one_ne_zero

theorem exists_j_F4 : ∃ j < 2, img8 D e (lOne L (fsuV1 T V) ⊔ T) = MS j := by
  have hle : img8 D e (lOne L (fsuV1 T V) ⊔ T) ≤ g5 true true :=
    (img8_mono D e C.base.L1TH_F4).trans C.imgH.le
  have hP : PS ≤ img8 D e (lOne L (fsuV1 T V) ⊔ T) :=
    C.imgT.ge.trans (img8_mono D e le_sup_right)
  have hcard : Nat.card (img8 D e (lOne L (fsuV1 T V) ⊔ T)) = 48 := by
    rw [C.base.card_img_L1T_F4 e, C.imgT, card_PS]
  exact eq_MS_of hle hP hcard

theorem img_L1_F4 {j : ℕ} (hj : j < 2) (hjeq : img8 D e (lOne L (fsuV1 T V) ⊔ T) = MS j) :
    img8 D e (lOne L (fsuV1 T V)) = OS j := by
  rw [C.base.L1_eq_oTwoUpper_F4, img8_oTwoUpper D e (C.base.L1TH_F4.trans HN), hjeq, oTwoUpper_MS hj]

theorem MS_le_F4 {k : ℕ} (hk : k < 2) : MS k ≤ img8 D e (l32nH T V) := C.imgH ▸ MS_le_gS hk

theorem img_X_F4 {k : ℕ} (hk : k < 2) : img8 D e (xM D e (MS k)) = OS k := by
  rw [img_xM (C.MS_le_F4 hk), oTwoUpper_MS hk]


theorem JH_F4 (k : ℕ) : lOne L (fsuV1 T V) ⊔ xM D e (MS k) ⊔ T ≤ l32nH T V :=
  sup_le (sup_le L14411.L1H (xM_le_H e _)) C.base.TH_F4

theorem nonempty_quot_F4 {j k : ℕ} (hjk : (j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0))
    (hjeq : img8 D e (lOne L (fsuV1 T V) ⊔ T) = MS j) :
    Nonempty (OTwoQuot (lOne L (fsuV1 T V) ⊔ xM D e (MS k) ⊔ T) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hj : j < 2 := by omega
  have hk : k < 2 := by omega
  have hJN : lOne L (fsuV1 T V) ⊔ xM D e (MS k) ⊔ T ≤ Subgroup.normalizer (fsuU T V : Set G) :=
    (C.JH_F4 k).trans HN
  have himg : img8 D e (lOne L (fsuV1 T V) ⊔ xM D e (MS k) ⊔ T) = M12S := by
    rw [img8_sup D e (sup_le L14411.L1H (xM_le_H e _) |>.trans HN) (C.base.TH_F4.trans HN),
      img8_sup D e (L14411.L1H.trans HN) ((xM_le_H e _).trans HN), C.img_L1_F4 hj hjeq,
      C.img_X_F4 hk, C.imgT, M12S_eq]
    rcases hjk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · rw [sup_comm (OS 1)]
  let φ : ↥(lOne L (fsuV1 T V) ⊔ xM D e (MS k) ⊔ T) →* ↥M12S :=
    (hom8 D e hJN).codRestrict M12S fun x => by
      rw [← himg, ← range_hom8 D e hJN]
      exact ⟨x, rfl⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨γ, hγ⟩
    rw [← himg, ← range_hom8 D e hJN] at hγ
    obtain ⟨x, rfl⟩ := hγ
    exact ⟨x, rfl⟩
  have hker : IsPGroup 2 (chiS.comp φ).ker := by
    rintro ⟨x, hx⟩
    have hsq := sq_eq_one_of_chiS (MonoidHom.mem_ker.mp hx)
    have hxx : hom8 D e hJN (x * x) = 1 := by
      rw [map_mul]
      exact hsq
    have hxQ : ((x * x : ↥(lOne L (fsuV1 T V) ⊔ xM D e (MS k) ⊔ T)) : G) ∈
        pCoreOf 2 (l32nH T V) :=
      (C.base.matOf_eq_one_iff_F4 D e (C.JH_F4 k (x * x).2)).mp hxx
    obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (l32nH T V) ⟨_, hxQ⟩
    refine ⟨n + 1, Subtype.ext (Subtype.ext ?_)⟩
    have h1 : ((x : G) * x) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [pow_succ', pow_mul, sq, h1]
  exact nonempty_quot_equiv_of_surj (chiS.comp φ) (chiS_surjective.comp hφ) hker s33_normal_two

end Ctx5_F4

theorem y1444Claim_of_ctx5_F4 (C : Ctx5_F4 G T L V V₂ g D e) : Y1444Claim T L V V₂ g := by
  obtain ⟨a, ha, haV⟩ := C.base.abs.exists_mem_not_mem
  obtain ⟨j, hj, hjeq⟩ := C.exists_j_F4
  obtain ⟨k, hk, hjk⟩ : ∃ k < 2, (j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0) := by
    interval_cases j
    · exact ⟨1, by norm_num, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨0, by norm_num, Or.inr ⟨rfl, rfl⟩⟩
  have hP := C.planeData_F4 hk ha haV
  refine ⟨xM D e (MS k), ⟨xM_le_H e _, C.base.T_le_normalizer_xM_F4 (C.imgT.le.trans (PS_le_MS k)),
    oTwoUpper_xM e _, C.base.relIndex_xM_F4 (C.img_X_F4 hk) (index_pCore_OS hk),
    C.base.card_commutator_xM_F4 (C.MS_le_F4 hk) ha haV hP,
    C.base.commutator_le_E_xM_F4 (C.MS_le_F4 hk) ha haV hP⟩, fun h => ?_, C.nonempty_quot_F4 hjk hjeq⟩
  have h1 := C.img_X_F4 hk
  rw [h, C.img_L1_F4 hj hjeq] at h1
  rcases hjk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact OS_ne h1
  · exact OS_ne h1.symm

theorem y1444Claim_of_case5_F4 (hA5 : Lemma14410A5_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h12811 : Lemma12_8_11_F4)
    (h12812 : Lemma12_8_12_two_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h : Hyp14310One G T L V) (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V))
    (hU32 : Nat.card ↥(fsuU T V) ≠ 2 ^ 5) (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V)
    (hgH : g ∉ l32nH T V) (h5 : Case1442Five T V V₂ g D) : Y1444Claim T L V V₂ g := by
  obtain ⟨b₁, b₂, e₀, hiso, hW8⟩ := h5
  cases b₂ with
  | false => exact (hA5 G T L V h hext hU32 V₂ g hV₂ hgP hgH D b₁ e₀ hiso hW8).elim
  | true =>
    cases b₁ with
    | false =>
      exact (false_of_A5_F4 h1332 h1334 h1222 h12213 h12811 h12812 h37 h38 h39 h hext hV₂ hgP hgH
        hiso hW8).elim
    | true =>
      obtain ⟨e, C⟩ := exists_ctx5_F4 h1332 h1334 h1222 h12213 h12811 h12812 h37 h38 h39 h hext hV₂
        hgP hgH hiso hW8
      exact y1444Claim_of_ctx5_F4 C

end CFSG.Quasithin.H13.L14410
