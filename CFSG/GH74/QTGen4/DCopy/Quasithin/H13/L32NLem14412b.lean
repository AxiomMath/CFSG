module

public import CFSG.Quasithin.H13.L32NLem14412b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem144Bb

public section

namespace CFSG.Quasithin.H13.L144B

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L14411 L1442M

variable {n : ℕ} {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)}

namespace Base_F4
open CFSG.Quasithin.H13.L144B.Base_F4

variable (C : Base_F4 G T L V V₂ g)
include C

theorem matOfN_eq_one_iff_F4 (D : HatModelU (fsuU T V)) (e : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    {h : G} (hh : h ∈ l32nH T V) :
    matOfN e (D.ρ ⟨h, L14332.l32nH_le_normalizer_fsuU T V hh⟩) = 1 ↔
      h ∈ pCoreOf 2 (l32nH T V) := by
  rw [← C.cHat, ← L14332.rho_eq_one_iff_mem hh (L14332.l32nH_le_normalizer_fsuU T V hh),
    ← (matOfN e).map_one]
  exact (matOfN_injective e).eq_iff

theorem card_imgTN_F4 (e : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2)) {Γ : Subgroup (GL (Fin n) (ZMod 2))}
    (himgH : imgN D e (l32nH T V) = Γ) {m k : ℕ} (hΓ : Nat.card Γ = 2 ^ m * k) (hk : Odd k) :
    Nat.card (imgN D e T) = 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : (pCoreOf 2 (l32nH T V)).relIndex (l32nH T V) = 2 ^ m * k := by
    rw [← C.card_img_eq_F4 D le_rfl, ← card_imgN D e, himgH, hΓ]
  have hT : Nat.card (imgN D e T) = (pCoreOf 2 (l32nH T V)).relIndex T := by
    rw [card_imgN, C.card_img_eq_F4 D C.TH_F4]
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 (l32nH T V)) T (l32nH T V) C.QT_F4 C.TH_F4
  rw [hH, ← hT] at hmul
  have hodd : ¬ 2 ∣ T.relIndex (l32nH T V) :=
    (isSylowTwoOf_of_quasithinIsSylowTwo C.hyp.fsu.sylow C.TH_F4).2.2
  have h2 : IsPGroup 2 ↥(imgN D e T) := by
    rw [imgN_eq_map]
    exact (C.hyp.fsu.sylow.1.of_equiv
      (Subgroup.subgroupOfEquivOfLe (C.TH_F4.trans HN)).symm).map _
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  rw [hn] at hmul ⊢

  have hk2 : Nat.Coprime 2 k := Nat.coprime_two_left.mpr hk
  have ht2 : Nat.Coprime 2 (T.relIndex (l32nH T V)) :=
    Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega))
  have h1 : 2 ^ n ∣ 2 ^ m :=
    (Nat.Coprime.pow_left n hk2).dvd_of_dvd_mul_right (Dvd.intro _ hmul)
  have h2' : 2 ^ m ∣ 2 ^ n :=
    (Nat.Coprime.pow_left m ht2).dvd_of_dvd_mul_right (Dvd.intro _ hmul.symm)
  exact Nat.dvd_antisymm h1 h2'

theorem exists_normalizedN_F4 (e : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    {Γ P : Subgroup (GL (Fin n) (ZMod 2))} (himgH : imgN D e (l32nH T V) = Γ)
    {F : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2} (hform : ∀ x y, D.B x y = F (e x) (e y))
    (hPΓ : P ≤ Γ) (hP2 : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.relIndex Γ)
    (hcard : Nat.card (imgN D e T) = Nat.card P) :
    ∃ e' : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2), imgN D e' (l32nH T V) = Γ ∧
      (∀ x y, D.B x y = F (e' x) (e' y)) ∧ imgN D e' T = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKΓ : imgN D e T ≤ Γ := himgH ▸ imgN_mono D e C.TH_F4
  have hK2 : IsPGroup 2 ↥(imgN D e T) := by
    rw [imgN_eq_map]
    exact (C.hyp.fsu.sylow.1.of_equiv
      (Subgroup.subgroupOfEquivOfLe (C.TH_F4.trans HN)).symm).map _
  have hKi : ¬ 2 ∣ (imgN D e T).relIndex Γ := by
    have h1 := Subgroup.relIndex_mul_card (imgN D e T) Γ
    have h2 := Subgroup.relIndex_mul_card P Γ
    rw [inf_eq_left.mpr hKΓ, hcard] at h1
    rw [inf_eq_left.mpr hPΓ] at h2
    have hpos : 0 < Nat.card P := Nat.card_pos
    have : (imgN D e T).relIndex Γ = P.relIndex Γ := by
      have := h1.trans h2.symm
      exact Nat.eq_of_mul_eq_mul_right hpos this
    rw [this]
    exact hPi
  obtain ⟨c, hcΓ, hc⟩ := exists_conj_of_sylow hKΓ hPΓ hK2 hP2 hKi hPi
  obtain ⟨y, hyH, hyN, hyc⟩ := (mem_imgN D e).mp (himgH ▸ hcΓ)
  have hce : ∀ x : D.V, (c : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (e x) =
      e (D.ρ ⟨y, hyN⟩ x) := fun x => by rw [← hyc, matOfN_mulVec]
  refine ⟨e.trans (linOfN c), ?_, fun x x' => ?_, ?_⟩
  · rw [imgN_trans, himgH, map_conj_of_mem hcΓ]
  · simp only [LinearEquiv.trans_apply, linOfN_apply, hce]
    rw [← hform, L128A.HatU.B_rho]
  · have hle : imgN D (e.trans (linOfN c)) T ≤ P := by
      rw [imgN_trans]
      rintro _ ⟨x, hx, rfl⟩
      exact hc x hx
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [imgN_trans, Subgroup.card_map_of_injective (MulEquiv.injective _), hcard]

theorem T_fixN_F4 (e : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2)) {a : G} (ha : a ∈ V₂)
    (haV : a ∉ fsuV1 T V) {γ : GL (Fin n) (ZMod 2)} (hγ : γ ∈ imgN D e T) :
    (γ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (e (D.π a)) = e (D.π a) := by
  obtain ⟨t, ht, htN, rfl⟩ := (mem_imgN D e).mp hγ
  rw [matOfN_mulVec, C.rho_T_pi_a_F4 D ha haV ht htN]

theorem Wg_fixN_F4 (e : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2)) {a : G} (ha : a ∈ V₂)
    {γ : GL (Fin n) (ZMod 2)} (hγ : γ ∈ imgN D e (CFSG.conjugate (l32nW T V V₂) g)) :
    (γ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (e (D.π a)) = e (D.π a) := by
  obtain ⟨w, hw, hwN, rfl⟩ := (mem_imgN D e).mp hγ
  rw [matOfN_mulVec, C.rho_Wg_pi_a_F4 D ha hw hwN]

theorem conj_mem_img_WgN_F4 (e : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2)) {a : G} (ha : a ∈ V₂)
    (haV : a ∉ fsuV1 T V) {ν : GL (Fin n) (ZMod 2)} (hν : ν ∈ imgN D e (l32nH T V))
    (hνfix : (ν : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (e (D.π a)) = e (D.π a))
    {x : GL (Fin n) (ZMod 2)} (hx : x ∈ imgN D e (CFSG.conjugate (l32nW T V V₂) g)) :
    ν * x * ν⁻¹ ∈ imgN D e (CFSG.conjugate (l32nW T V V₂) g) := by
  obtain ⟨w, hw, hwN, rfl⟩ := (mem_imgN D e).mp hx
  obtain ⟨h, hh, hhN, rfl⟩ := (mem_imgN D e).mp hν
  have hfix : D.ρ ⟨h, L14332.l32nH_le_normalizer_fsuU T V hh⟩ (D.π a) = D.π a := by
    apply e.injective
    rw [← matOfN_mulVec]
    exact hνfix
  have hhV₂ := C.mem_normalizer_of_fix_F4 D ha haV hh hfix
  have hconj : h * w * h⁻¹ ∈ CFSG.conjugate (l32nW T V V₂) g ⊔ l32nCHat T V :=
    (Subgroup.mem_normalizer_iff.mp (C.nWg ⟨hh, hhV₂⟩) w).mp (Subgroup.mem_sup_left hw)
  have h1 : imgN D e (CFSG.conjugate (l32nW T V V₂) g ⊔ l32nCHat T V) =
      imgN D e (CFSG.conjugate (l32nW T V V₂) g) := by
    rw [imgN_sup D e (C.WgH_F4.trans HN) (fun c (hc : c ∈ l32nCHat T V) => HN hc.1),
      imgN_cHat, sup_bot_eq]
  rw [← h1]
  refine (mem_imgN D e).mpr ⟨h * w * h⁻¹, hconj,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hhN hwN) (Subgroup.inv_mem _ hhN), ?_⟩
  rw [show (⟨h * w * h⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hhN hwN)
      (Subgroup.inv_mem _ hhN)⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) =
      ⟨h, hhN⟩ * ⟨w, hwN⟩ * ⟨h, hhN⟩⁻¹ from rfl, map_mul, map_mul, map_inv, map_mul,
    map_mul, map_inv]

theorem mulVec_add_mem_hatEN_F4 (e : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2)) {a : G} (ha : a ∈ V₂)
    (haV : a ∉ fsuV1 T V) {x : GL (Fin n) (ZMod 2)}
    (hx : x ∈ imgN D e (CFSG.conjugate (l32nW T V V₂) g)) {v : Fin n → ZMod 2}
    (hv : D.B (e.symm v) (D.π a) = 0) :
    (x : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v + v ∈
      (D.hat (l32nE T V V₂ g)).map e.toLinearMap := by
  obtain ⟨_, S⟩ := C.set14_F4
  have haU := C.V2U_F4 ha
  obtain ⟨w, hw, hwN, rfl⟩ := (mem_imgN D e).mp hx
  obtain ⟨u, hu, hue⟩ := D.π_surj (e.symm v)
  have hev : e (D.π u) = v := by rw [hue, LinearEquiv.apply_symm_apply]
  have huW : u ∈ l32nW T V V₂ := by
    refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun v' hv' => ?_⟩
    have hua : u * a * u⁻¹ * a⁻¹ = 1 := (D.B_spec u hu a haU).mp (by rw [hue]; exact hv)
    have hua' : a * u = u * a := by
      calc a * u = (u * a * u⁻¹ * a⁻¹)⁻¹ * u * a := by group
        _ = u * a := by rw [hua]; group
    have hcen : ∀ z ∈ fsuV1 T V, z * u = u * z := fun z hz => by
      rw [← C.zU] at hz
      exact (Subgroup.mem_centralizer_iff.mp hz.2 u hu).symm
    rcases S.mem_V2_F4 ha haV hv' with h1 | h1
    · exact hcen v' h1
    · have haa : a * a = 1 := S.mul_self_V_F4 (C.plane.1.1 ha)
      have hv'' : v' = a * (a * v') := by rw [← mul_assoc, haa, one_mul]
      rw [hv'']
      calc a * (a * v') * u = a * ((a * v') * u) := by group
        _ = a * (u * (a * v')) := by rw [hcen _ h1]
        _ = (a * u) * (a * v') := by group
        _ = u * (a * (a * v')) := by rw [hua']; group
  have hcommE : w * u * w⁻¹ * u⁻¹ ∈ l32nE T V V₂ g := by
    have h1 := C.wwE (Subgroup.commutator_mem_commutator huW hw)
    have h2 : w * u * w⁻¹ * u⁻¹ = (u * w * u⁻¹ * w⁻¹)⁻¹ := by group
    rw [h2]
    exact Subgroup.inv_mem _ (by simpa [commutatorElement_def] using h1)
  have hcU : w * u * w⁻¹ * u⁻¹ ∈ fsuU T V :=
    Subgroup.mul_mem _ (L128A.HatU.conj_mem hwN hu) (Subgroup.inv_mem _ hu)
  refine ⟨D.π (w * u * w⁻¹ * u⁻¹), L128A.HatU.π_mem_hat D hcommE hcU, ?_⟩
  rw [← L128A.HatU.rho_sub_π D hwN hu, sub_eq_add_neg, neg_eq_self_zmod2, LinearEquiv.coe_coe,
    map_add, ← matOfN_mulVec, hev]

theorem card_img_L1TN_F4 (e : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :
    Nat.card (imgN D e (lOne L (fsuV1 T V) ⊔ T)) = Nat.card (imgN D e T) * 3 := by
  rw [card_imgN, card_imgN, C.card_img_eq_F4 D C.L1TH_F4, C.card_img_eq_F4 D C.TH_F4,
    ← Subgroup.relIndex_mul_relIndex (pCoreOf 2 (l32nH T V)) T (lOne L (fsuV1 T V) ⊔ T) C.QT_F4
      le_sup_right, C.relIndex_L1T_F4]

end Base_F4

end CFSG.Quasithin.H13.L144B
