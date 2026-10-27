module

public import CFSG.Quasithin.H13.L32NLem1442o
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1442e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem144Bb

public section

namespace CFSG.Quasithin.H13.L1442

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Fischer L14411 L1442M
  Mat8Cert

variable {G : Type} [Group G]

namespace Ctx_F4

variable [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} {g a : G} {D : HatModelU (fsuU T V)}
  (C : Ctx_F4 G T L V V₂ g a D)
include C

theorem exists_coords7_F4 (h12213 : Stmt12_2_13_F4)
    (h7 : G11.SzG11S.G112Concl7S (D.img (l32nH T V))
      (D.img (CFSG.conjugate (l32nW T V V₂) g))) :
    ∃ e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2),
      img8 D e (oTwoUpper (l32nH T V)) = omega3 ∧ img8 D e (l32nH T V) ≤ omega3N ∧
      (∀ γ ∈ img8 D e (l32nH T V), ∀ w,
        quadOf q3 ((γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w) = quadOf q3 w) ∧
      (∀ u ∈ fsuU T V, quadOf q3 (e (D.π u)) = 0 ↔ u * u = 1) ∧
      ¬ img8 D e (CFSG.conjugate (l32nW T V V₂) g) ≤ omega3 := by
  classical
  have : Finite (D.V ≃ₗ[ZMod 2] D.V) :=
    Finite.of_injective (fun e => (e : D.V → D.V)) fun _ _ h => LinearEquiv.ext (congrFun h)
  set Γ := D.img (l32nH T V) with hΓ
  obtain ⟨⟨hd8, ⟨φ⟩, hXF⟩, hnat⟩ := h7
  set N : Subgroup ↥Γ := genFittingFStar ↥Γ with hN
  have hNn : N.Normal := A7Mod.genFittingFStar_normal' ↥Γ
  set Fs : Subgroup (D.V ≃ₗ[ZMod 2] D.V) := N.map Γ.subtype with hFs
  have hFsΓ : Fs ≤ Γ := Subgroup.map_subtype_le N
  obtain ⟨Θ₀, hfwd₀, hbwd₀⟩ := exists_theta hnat

  have hcardF : Nat.card Fs = 3600 := by
    rw [hFs, Subgroup.card_map_of_injective Γ.subtype_injective, Nat.card_congr φ.toEquiv,
      Nat.card_prod, SL2MinimalFaithful.card_specialLinearGroup_fin_two,
      GaloisField.card 2 2 (by norm_num)]
    norm_num

  obtain ⟨q, hqU, hqB, hqΓ⟩ := C.exists_quad_F4 h12213
  have hFq : ∀ γ ∈ Fs, ∀ v, q (γ v) = q v := fun γ hγ v => hqΓ γ (hFsΓ hγ) v
  have hinv : ∀ A B : Matrix.SpecialLinearGroup (Fin 2) F4, ∀ X,
      q (Θ₀.symm ((A : Matrix (Fin 2) (Fin 2) F4) * X * (B : Matrix (Fin 2) (Fin 2) F4))) =
        q (Θ₀.symm X) := by
    intro A B X
    obtain ⟨γ, hγ, hγΘ⟩ := hbwd₀ A B
    have h1 : Θ₀.symm ((A : Matrix (Fin 2) (Fin 2) F4) * X * (B : Matrix (Fin 2) (Fin 2) F4)) =
        γ (Θ₀.symm X) := by
      apply Θ₀.injective
      rw [AddEquiv.apply_symm_apply, hγΘ, AddEquiv.apply_symm_apply]
    rw [h1, hFq γ hγ]
  obtain ⟨l, hl⟩ := exists_eq_trace_det (q := fun X => q (Θ₀.symm X))
    (b := fun X Y => D.B (Θ₀.symm X) (Θ₀.symm Y))
    (fun X Y => by simp only [map_add, hqB])
    (fun X X' Y => by simp only [map_add, LinearMap.add_apply])
    (fun X Y Y' => by simp only [map_add])
    hinv

  have hl0 : l ≠ 0 := by
    intro hl0
    have hq0 : ∀ v, q v = 0 := fun v => by
      have := hl (Θ₀ v)
      rwa [AddEquiv.symm_apply_apply, hl0, zero_mul, trF4_zero] at this
    have hB0 : ∀ v w, D.B v w = 0 := fun v w => by
      have := hqB v w
      rw [hq0, hq0, hq0, zero_add, zero_add] at this
      exact this.symm
    have : Module.Finite (ZMod 2) D.V := Module.Finite.of_finite
    have hpos : 0 < Module.finrank (ZMod 2) D.V := by rw [hd8]; norm_num
    obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    exact hv (C.g111.nondegenerate v (hB0 v))

  have hμ : l * l ≠ 0 := mul_ne_zero hl0 hl0
  set Θ : D.V ≃+ Matrix (Fin 2) (Fin 2) F4 := Θ₀.trans (smulEquiv (l * l) hμ) with hΘdef
  have hΘ : ∀ v, Θ v = (l * l) • Θ₀ v := fun v => rfl
  have hqΘ : ∀ v, q v = trF4 (Θ v).det := by
    intro v
    rw [hΘ, trace_det_smul, ← hl, AddEquiv.symm_apply_apply]
  have hO : O3Data Fs Θ := by
    refine ⟨fun γ hγ => ?_, fun A B => ?_, hcardF⟩
    · obtain ⟨A, B, hAB⟩ := hfwd₀ γ hγ
      refine ⟨A, B, fun v => ?_⟩
      rw [hΘ, hΘ, hAB, Matrix.mul_smul, Matrix.smul_mul]
    · obtain ⟨γ, hγ, hγΘ⟩ := hbwd₀ A B
      refine ⟨γ, hγ, fun v => ?_⟩
      rw [hΘ, hΘ, hγΘ, Matrix.mul_smul, Matrix.smul_mul]
  set e := eOf Θ with he
  have hqe : ∀ v, quadOf q3 (e v) = q v := fun v => by
    rw [he, eOf_apply, quad_bitsE, hqΘ]

  have hK : Fs.map (matOf e) = omega3 := hO.map_eq_omega3

  have hFn : ∀ γ ∈ Γ, ∀ δ, δ ∈ Fs ↔ γ * δ * γ⁻¹ ∈ Fs := by
    intro γ hγ δ
    constructor
    · rintro ⟨δ', hδ', rfl⟩
      exact ⟨⟨γ, hγ⟩ * δ' * ⟨γ, hγ⟩⁻¹, hNn.conj_mem δ' hδ' ⟨γ, hγ⟩, rfl⟩
    · rintro ⟨δ', hδ', hδ'e⟩
      refine ⟨⟨γ, hγ⟩⁻¹ * δ' * ⟨γ, hγ⟩, ?_, ?_⟩
      · have := hNn.conj_mem δ' hδ' ⟨γ, hγ⟩⁻¹
        simpa using this
      · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hδ'e ⊢
        rw [hδ'e]
        group

  have hHN : img8 D e (l32nH T V) ≤ omega3N := by
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := hx
    exact hO.matOf_mem_omega3N (hFn γ hγ) fun v => by rw [← hqΘ, ← hqΘ, hqΓ γ hγ v]

  have hperf : ⁅Fs, Fs⁆ = Fs := by
    let ψ : (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) ×
        Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) →* (D.V ≃ₗ[ZMod 2] D.V) :=
      Γ.subtype.comp (N.subtype.comp φ.symm.toMonoidHom)
    have hrange : ψ.range = Fs := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨φ.symm y, (φ.symm y).2, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨φ ⟨y, hy⟩, by simp [ψ]⟩
    have hSL := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card
      (GaloisField 2 2) four_le_card_gf
    have hP := G11.P3Ortho.Om4.isPerfect_prod hSL hSL
    have hR := Group.IsPerfect.range ψ
    rw [hrange] at hR
    exact Subgroup.isPerfect_iff.1 hR
  have hidx : Fs.relIndex Γ ∣ 4 := by
    have h1 := Subgroup.relIndex_mul_card Fs Γ
    rw [inf_of_le_left hFsΓ, hcardF] at h1
    have h2 : Nat.card Γ ∣ 14400 := by
      rw [← O3Cert.card_omega3N, ← card_img8 D e (l32nH T V)]
      exact Subgroup.card_dvd_of_le hHN
    rw [← h1] at h2
    obtain ⟨r, hr⟩ := h2
    exact ⟨r, by linarith⟩
  have hO2 : D.img (oTwoUpper (l32nH T V)) = Fs := by
    rw [img_oTwoUpper D (L14332.l32nH_le_normalizer_fsuU T V)]
    refine (eq_oTwoUpper_of_pow_mem hFsΓ (fun x hx => ⟨2, ?_⟩)
      (oTwoUpper_eq_self_of_perfect hperf).symm).symm
    have hNF : (Fs.subgroupOf Γ).Normal := ⟨fun n hn γ => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact (hFn γ γ.2 n).mp hn⟩
    have h1 := Subgroup.pow_index_mem (Fs.subgroupOf Γ) (⟨x, hx⟩ : ↥Γ)
    obtain ⟨r, hr⟩ := hidx
    have h2 : (⟨x, hx⟩ : ↥Γ) ^ 2 ^ 2 ∈ Fs.subgroupOf Γ := by
      rw [show 2 ^ 2 = Fs.relIndex Γ * r by rw [← hr]; norm_num]
      rw [pow_mul]
      exact Subgroup.pow_mem _ h1 r
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  refine ⟨e, ?_, hHN, ?_, fun u hu => ?_, ?_⟩
  · rw [img8, hO2, hK]
  · rintro _ ⟨γ, hγ, rfl⟩ w
    rw [← LinearEquiv.apply_symm_apply e w, matOf_mulVec, hqe, hqe, hqΓ γ hγ]
  · rw [hqe, hqU u hu, sq]
  · intro hle
    apply hXF
    intro x hx
    have h1 : matOf e x ∈ omega3 := hle ⟨x, hx, rfl⟩
    rw [← hK] at h1
    obtain ⟨y, hy, hye⟩ := h1
    rw [← matOf_injective e hye]
    exact hy

theorem case3_of_concl7_F4
    (h12213 : Stmt12_2_13_F4)
    (h7 : G11.SzG11S.G112Concl7S (D.img (l32nH T V))
      (D.img (CFSG.conjugate (l32nW T V V₂) g))) :
    Case1442Three T V V₂ g D := by
  classical
  have : Finite (D.V ≃ₗ[ZMod 2] D.V) :=
    Finite.of_injective (fun e => (e : D.V → D.V)) fun _ _ h => LinearEquiv.ext (congrFun h)
  have hd8 : Module.finrank (ZMod 2) D.V = 8 := h7.1.1
  obtain ⟨e, hO, hHN, hqq, hquad, hX3⟩ := C.exists_coords7_F4 h12213 h7
  have h3Γ : omega3 ≤ img8 D e (l32nH T V) := hO ▸ img8_mono D e (oTwoUpper_le _)
  have hT' : IsSylowTwoOf (img8 D e T) (img8 D e (l32nH T V)) :=
    isSylowTwoOf_map_inj C.isSylow_F4 (matOf_injective e)

  have hm := Subgroup.relIndex_mul_card omega3 (img8 D e (l32nH T V))
  rw [inf_of_le_left h3Γ, O3Cert.card_omega3] at hm
  have hdvd : Nat.card (img8 D e (l32nH T V)) ∣ 14400 :=
    O3Cert.card_omega3N ▸ Subgroup.card_dvd_of_le hHN
  set m := omega3.relIndex (img8 D e (l32nH T V)) with hmdef
  have hm4 : m ∣ 4 := by
    rw [← hm] at hdvd
    obtain ⟨r, hr⟩ := hdvd
    exact ⟨r, by linarith⟩

  have hTcard : Nat.card (img8 D e T) = 16 * m := by
    have hm' : m = 1 ∨ m = 2 ∨ m = 4 := by
      have h4 : m ∣ 2 ^ 2 := by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact hm4
      obtain ⟨i, hi, hmi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
      interval_cases i <;> simp [hmi]
    rcases hm' with h | h | h
    · have h1 := C.base.card_imgT_F4 e rfl (m := 4) (k := 225) (by rw [← hm, h]; norm_num)
        (by decide)
      rw [h1, h]
      norm_num
    · have h1 := C.base.card_imgT_F4 e rfl (m := 5) (k := 225) (by rw [← hm, h]; norm_num)
        (by decide)
      rw [h1, h]
      norm_num
    · have h1 := C.base.card_imgT_F4 e rfl (m := 6) (k := 225) (by rw [← hm, h]; norm_num)
        (by decide)
      rw [h1, h]
      norm_num

  have hTi : (img8 D e T ⊓ omega3).relIndex (img8 D e T) ≤ m := by
    have h1 := Subgroup.relIndex_inf_le (H := img8 D e T) (K := omega3) (L := img8 D e T)
    rw [Subgroup.relIndex_self, one_mul] at h1
    refine h1.trans (Subgroup.relIndex_le_of_le_right hT'.1 ?_)
    rw [← hmdef]
    intro h0
    rw [h0, zero_mul] at hm
    exact absurd hm.symm Nat.card_pos.ne'
  have hTm := Subgroup.relIndex_mul_card (img8 D e T ⊓ omega3) (img8 D e T)
  rw [inf_of_le_left inf_le_left, hTcard] at hTm
  have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hm4 (by norm_num)
  have hge : 16 ≤ Nat.card ↥(img8 D e T ⊓ omega3) := by
    by_contra hlt'
    have hlt := Nat.lt_of_not_le hlt'
    have : (img8 D e T ⊓ omega3).relIndex (img8 D e T) * Nat.card ↥(img8 D e T ⊓ omega3) <
        m * 16 := Nat.mul_lt_mul_of_le_of_lt hTi hlt hm0
    linarith
  have hT2 : IsPGroup 2 ↥(img8 D e T ⊓ omega3) := hT'.2.1.to_le inf_le_left
  have hle16 : Nat.card ↥(img8 D e T ⊓ omega3) ≤ 16 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    have h1 : Nat.card ↥(img8 D e T ⊓ omega3) ∣ 3600 :=
      O3Cert.card_omega3 ▸ Subgroup.card_dvd_of_le inf_le_right
    rw [hk] at h1 ⊢
    have hk4 : k ≤ 4 := by
      by_contra hk5'
      have hk5 : 5 ≤ k := by omega
      have h2 : 2 ^ 5 ∣ 3600 := (Nat.pow_dvd_pow 2 hk5).trans h1
      norm_num at h2
    calc 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hk4
      _ = 16 := by norm_num
  have h16 : Nat.card ↥(img8 D e T ⊓ omega3) = 16 := le_antisymm hle16 hge

  have hP2 : IsPGroup 2 ↥O3cCert.P0 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := 4) (by rw [O3cCert.card_P0]; norm_num)
  have hidx : ∀ {S : Subgroup (GL (Fin 8) (ZMod 2))}, S ≤ omega3 → Nat.card S = 16 →
      ¬ 2 ∣ S.relIndex omega3 := by
    intro S hS hS16 h2
    have h1 := Subgroup.relIndex_mul_card S omega3
    rw [inf_of_le_left hS, hS16, O3Cert.card_omega3] at h1
    have h3 : S.relIndex omega3 = 225 := by omega
    rw [h3] at h2
    norm_num at h2
  obtain ⟨c, hc3, hc⟩ := exists_conj_of_sylow inf_le_right O3cCert.P0_le_omega3 hT2 hP2
    (hidx inf_le_right h16) (hidx O3cCert.P0_le_omega3 O3cCert.card_P0)
  have hcΓ : c ∈ img8 D e (l32nH T V) := h3Γ hc3
  set e₁ := e.trans (linOf c) with he₁
  have himg : ∀ Y, img8 D e₁ Y = (img8 D e Y).map (MulAut.conj c).toMonoidHom :=
    fun Y => img8_trans D e c Y
  have hO₁ : img8 D e₁ (oTwoUpper (l32nH T V)) = omega3 := by
    rw [himg, hO, map_conj_of_mem hc3]
  have hH₁ : img8 D e₁ (l32nH T V) = img8 D e (l32nH T V) := by
    rw [himg, map_conj_of_mem hcΓ]
  have hconj3 : ∀ {Y : Subgroup (GL (Fin 8) (ZMod 2))},
      Y.map (MulAut.conj c).toMonoidHom ≤ omega3 ↔ Y ≤ omega3 := by
    intro Y
    constructor
    · intro h y hy
      have h1 : c * y * c⁻¹ ∈ omega3 := h ⟨y, hy, rfl⟩
      have h2 := omega3.mul_mem (omega3.mul_mem (omega3.inv_mem hc3) h1) hc3
      simpa [mul_assoc] using h2
    · rintro h _ ⟨y, hy, rfl⟩
      exact omega3.mul_mem (omega3.mul_mem hc3 (h hy)) (omega3.inv_mem hc3)
  have hTP : img8 D e₁ T ⊓ omega3 = O3cCert.P0 := by
    rw [himg]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨⟨t, ht, rfl⟩, ht3⟩
      have ht3' : t ∈ omega3 := by
        rw [← map_conj_of_mem hc3 (S := omega3)] at ht3
        exact (Subgroup.mem_map_iff_mem (MulEquiv.injective _)).mp ht3
      exact hc t ⟨ht, ht3'⟩
    · rw [O3cCert.card_P0, ← map_conj_of_mem hc3 (S := omega3),
        ← Subgroup.map_inf_eq _ _ _ (MulEquiv.injective _),
        Subgroup.card_map_of_injective (MulEquiv.injective _), h16]

  have hv₀ : e₁ (D.π a) ≠ 0 := by
    intro h0
    apply C.πa_ne_F4
    rw [← e₁.map_zero] at h0
    exact e₁.injective h0
  have hn3 : ∀ γ ∈ img8 D e₁ (l32nH T V), ∀ k ∈ omega3, γ * k * γ⁻¹ ∈ omega3 := by
    intro γ hγ k hk
    rw [← hO₁] at hk ⊢
    obtain ⟨y, hy, hyN, rfl⟩ := (mem_img8 D e₁).mp hγ
    obtain ⟨z, hz, hzN, rfl⟩ := (mem_img8 D e₁).mp hk
    refine (mem_img8 D e₁).mpr ⟨y * z * y⁻¹,
      conj_mem_oTwoUpper (Subgroup.le_normalizer hy) hz,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hyN hzN) (Subgroup.inv_mem _ hyN), ?_⟩
    rw [show (⟨y * z * y⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hyN hzN)
      (Subgroup.inv_mem _ hyN)⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) =
      ⟨y, hyN⟩ * ⟨z, hzN⟩ * ⟨y, hyN⟩⁻¹ from rfl, map_mul, map_mul, map_inv, map_mul, map_mul,
      map_inv]
  have hX8 : 8 ≤ Nat.card ↥(img8 D e₁ (CFSG.conjugate (l32nW T V V₂) g)) := by
    rw [card_img8]
    have := C.lower_F4
    rw [hd8] at this
    exact this
  obtain ⟨-, xs', hxs', hxsF, hfull, hshape⟩ := O3cCert.shape_of (Γ := img8 D e₁ (l32nH T V))
    (T := img8 D e₁ T) (X := img8 D e₁ (CFSG.conjugate (l32nW T V V₂) g)) (v₀ := e₁ (D.π a))
    (hH₁ ▸ hHN) (hO₁ ▸ img8_mono D e₁ (oTwoUpper_le _)) hn3
    (isSylowTwoOf_map_inj C.isSylow_F4 (matOf_injective e₁)) hTP
    (fun t ht => C.base.T_fix_F4 e₁ C.aV₂ C.a1 ht) hv₀
    (img8_mono D e₁ C.base.WgH_F4) (fun x hx => C.base.Wg_fix_F4 e₁ C.aV₂ hx)
    (C.base.img_Wg_comm_F4 e₁) (fun x hx => C.base.img_Wg_sq_F4 e₁ hx)
    (fun m hm hmv x hx => C.base.conj_mem_img_Wg_F4 e₁ C.aV₂ C.a1 hm hmv hx)
    (fun hle => hX3 ((hconj3 (Y := img8 D e (CFSG.conjugate (l32nW T V V₂) g))).mp
      (by rw [← himg]; exact hle))) hX8
  obtain ⟨xs, hxsD, rfl⟩ := hxs'
  refine ⟨e₁, ⟨fun u hu => ?_, fun φ => ?_⟩, fun φ hφ => ?_, xs, hxsD, ⟨matOf e₁ xs,
    hHN (by rw [← hH₁]; exact img8_mono D e₁ C.base.WgH_F4 ⟨xs, hxsD, rfl⟩), hxsF,
    fun v => (matOf_mulVec e₁ xs v).symm⟩,
    ?_, ?_⟩
  ·
    rw [he₁, LinearEquiv.trans_apply, linOf_apply, hqq c hcΓ, hquad u hu]
  ·
    constructor
    · intro hφ
      exact ⟨matOf e₁ φ, hO₁ ▸ ⟨φ, hφ, rfl⟩, fun v => (matOf_mulVec e₁ φ v).symm⟩
    · rintro ⟨γ, hγ, hγe⟩
      rw [← hO₁] at hγ
      obtain ⟨φ', hφ', hφ'e⟩ := hγ
      have : matOf e₁ φ = γ := (matOf_eq_iff e₁ φ γ).mpr hγe
      rw [← matOf_injective e₁ (hφ'e.trans this.symm)]
      exact hφ'
  ·
    exact ⟨matOf e₁ φ, hHN (by rw [← hH₁]; exact ⟨φ, hφ, rfl⟩),
      fun v => (matOf_mulVec e₁ φ v).symm⟩
  ·
    have hfull' := (O3Cert.full_image hfull).1
    have hR : ∀ u : D.V, u ∈ LinearMap.range (xs.toLinearMap - LinearMap.id) ↔
        e₁ u ∈ (Finset.univ.image fun w =>
          ((matOf e₁ xs : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w +
            w) := by
      intro u
      rw [LinearMap.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨v, rfl⟩
        refine ⟨e₁ v, Finset.mem_univ _, ?_⟩
        rw [matOf_mulVec, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, map_sub]
        funext i
        exact zmod2_add_eq_sub _ _
      · rintro ⟨w, -, hw⟩
        refine ⟨e₁.symm w, e₁.injective ?_⟩
        rw [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, map_sub, ← hw,
          ← matOf_mulVec, LinearEquiv.apply_symm_apply]
        funext i
        exact (zmod2_add_eq_sub _ _).symm
    have hcard : Nat.card ↥(LinearMap.range (xs.toLinearMap - LinearMap.id)) = 16 := by
      rw [← hfull', ← Nat.card_eq_finsetCard]
      refine Nat.card_congr
        { toFun := fun u => ⟨e₁ u, (hR u).mp u.2⟩
          invFun := fun w => ⟨e₁.symm w, (hR _).mpr ((LinearEquiv.apply_symm_apply e₁ w).symm ▸
            w.2)⟩
          left_inv := fun u => Subtype.ext (e₁.symm_apply_apply u)
          right_inv := fun w => Subtype.ext (e₁.apply_symm_apply w) }
    have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := ↥(LinearMap.range (xs.toLinearMap - LinearMap.id)))
    rw [hcard, Nat.card_zmod] at h2
    have h3 : (2 : ℕ) ^ 4 = 2 ^ Module.finrank (ZMod 2)
        ↥(LinearMap.range (xs.toLinearMap - LinearMap.id)) := by
      rw [← h2]
      norm_num
    exact (Nat.pow_right_injective (le_refl 2) h3).symm
  ·
    apply Subgroup.map_injective (matOf_injective e₁)
    change img8 D e₁ (CFSG.conjugate (l32nW T V V₂) g) = _
    rw [Subgroup.map_sup, Subgroup.map_inf_eq _ _ _ (matOf_injective e₁),
      Subgroup.map_inf_eq _ _ _ (matOf_injective e₁), map_centralizer_matOf, MonoidHom.map_zpowers]
    change _ = (img8 D e₁ T ⊓ img8 D e₁ (oTwoUpper (l32nH T V)) ⊓ _) ⊔ _
    rw [hO₁]
    exact hshape

end Ctx_F4

end CFSG.Quasithin.H13.L1442
