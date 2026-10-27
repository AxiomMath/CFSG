module

public import CFSG.Quasithin.H13.L32NLemE8b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLemE8a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneHat

public section

namespace CFSG.Quasithin.H13.L1442E8

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Mat8Cert S7Cert S8Cert L1442M L14411 L144B

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)}


theorem exists_ctx8_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4)
    (h12213 : Stmt12_2_13_F4) (h12811 : Lemma12_8_11_F4) (h12811h : Lemma12_8_11_hat_F4)
    (h12812 : Lemma12_8_12_two_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h : Hyp14310One G T L V) (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V))
    (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V) (hgH : g ∉ l32nH T V)
    (h8 : Case1442EightPrime T V V₂ g D) :
    ∃ (a : G) (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)), Ctx8_F4 G T L V V₂ g a D e := by
  have B := exists_base_F4 h1332 h1334 h1222 h12213 h12811 h12812 h37 h38 h39 h hext hV₂ hgP hgH
  obtain ⟨_, S⟩ := B.set14_F4
  obtain ⟨e₀, hiso, xs, hxs, v, hv, hxv⟩ := h8
  have himgH := img8_eq_of_iso hiso
  have hZ2 : Nat.card ↥(centerOf (fsuU T V)) = 2 := by
    rw [l32n_card_centerOf]
    exact hext.2.2.2
  have hform₀ := form_of_quad D e₀ hZ2 B.comm_center_F4 hiso.quad
  obtain ⟨a, ha, haV⟩ := B.abs.exists_mem_not_mem
  have haU := B.V2U_F4 ha

  have hv0 : e₀ (D.π a) ≠ 0 := fun h0 =>
    B.pi_a_ne_F4 D ha haV ((map_eq_zero_iff e₀ e₀.injective).mp h0)
  have hcode : vec8 (code8 (e₀ (D.π a))) = e₀ (D.π a) := vec8_code8 _
  have hc0 : code8 (e₀ (D.π a)) ≠ 0 := fun h0 => hv0 (by rw [← hcode, h0, vec8_zero])
  have hq : q4N (code8 (e₀ (D.π a))) = false := by
    have h1 : quadOf q4 (e₀ (D.π a)) = 0 := (hiso.quad a haU).mpr (S.mul_self_V_F4 (hV₂.1.1 ha))
    rw [quadOf_q4, ← hcode, ← q4N_spec] at h1
    cases hq' : q4N (code8 (e₀ (D.π a)))
    · rfl
    · rw [hq'] at h1
      exact absurd h1 (by decide)

  have hII : inII (code8 (e₀ (D.π a))) = false := by
    by_contra hc
    have hmem : code8 (e₀ (D.π a)) ∈ iiList :=
      List.mem_filter.mpr ⟨List.mem_range.mpr (code8_lt _), by
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
        exact ⟨hc0, by simpa using hc⟩⟩
    obtain ⟨w, hw, hwN, rfl⟩ := (L128A.HatU.mem_img D).mp hxs
    have hγ : matOf e₀ (D.ρ ⟨w, hwN⟩) ∈ s8 := by
      rw [← himgH]
      exact (mem_img8 D e₀).mpr ⟨w, B.WgH_F4 hw, hwN, rfl⟩
    have hfix : ((matOf e₀ (D.ρ ⟨w, hwN⟩) : GL (Fin 8) (ZMod 2)) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 (code8 (e₀ (D.π a)))) =
          vec8 (code8 (e₀ (D.π a))) := by
      rw [hcode, matOf_mulVec, B.rho_Wg_pi_a_F4 D ha hw hwN]
    have := mem_subI_of_fix hγ hmem hfix hv
    rw [matOf_mulVec] at this
    exact hxv this

  obtain ⟨y, hy, hyv⟩ := exists_mem_s8_vR (code8_lt _) hc0 hII hq
  rw [hcode] at hyv
  have hcs : y⁻¹ ∈ s8 := s8.inv_mem hy
  obtain ⟨y', hy'H, hy'N, hy'c⟩ := (mem_img8 D e₀).mp (by rw [himgH]; exact hcs)
  have hce : ∀ x : D.V, ((y⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
      (e₀ x) = e₀ (D.ρ ⟨y', hy'N⟩ x) := fun x => by rw [← hy'c, matOf_mulVec]
  have hs := h.setting1282One_F4 (stmt13_3_2_two_of_stmt13_3_2_F4 h1332)
    (stmtL32NModule_of_inputs_F4 h1332 h1334) hV₂
  have hhat := h12811h G T L V 3 (fsuV1 T V) V₂ hs g hgP hgH a ha haV D
  refine ⟨a, e₀.trans (linOf y⁻¹),
    { base := B, aV₂ := ha, aV₁ := haV, imgH := ?_, form := ?_, ePiA := ?_, hat3 := hhat.1.2,
      hat5 := hhat.2.1 }⟩
  · rw [img8_trans, himgH, map_conj_of_mem hcs]
  · intro x x'
    simp only [LinearEquiv.trans_apply, linOf_apply, hce]
    rw [← hform₀, L128A.HatU.B_rho]
  · rw [LinearEquiv.trans_apply, linOf_apply, ← hyv, Matrix.mulVec_mulVec, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

namespace Ctx8_F4
open CFSG.Quasithin.H13.L1442E8.Ctx8_F4

variable {a : G} {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} (C : Ctx8_F4 G T L V V₂ g a D e)
include C

theorem false_F4 : False := by
  have hKZ := C.img_Wg_le_F4
  have hsum := C.finrank_add_F4
  have hsq := C.card_hatE_sq_F4
  have hcardE := L14323.card_submodule (D.hat (l32nE T V V₂ g))

  have hdvd : Nat.card (img8 D e (CFSG.conjugate (l32nW T V V₂) g)) ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = Nat.card Z8 by rw [card_Z8]; norm_num]
    exact Subgroup.card_dvd_of_le hKZ
  obtain ⟨k, hk4, hkK⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hkK, Nat.log_pow (by norm_num)] at hsum

  have hm4 : Module.finrank (ZMod 2) ↥(D.hat (l32nE T V V₂ g)) ≤ 4 := by
    rw [hcardE] at hsq
    by_contra hc
    push Not at hc
    have : 2 ^ 5 ≤ 2 ^ Module.finrank (ZMod 2) ↥(D.hat (l32nE T V V₂ g)) :=
      Nat.pow_le_pow_right (by norm_num) hc
    nlinarith
  by_cases hNK : ∃ x ∈ img8 D e (CFSG.conjugate (l32nW T V V₂) g), x ∉ N8
  ·
    obtain ⟨x, hx, hxN⟩ := hNK
    have hKeq : img8 D e (CFSG.conjugate (l32nW T V V₂) g) = Z8 :=
      eq_Z8_of hKZ (fun n hn hnfix k hk => C.conj_mem_img_F4 hn hnfix hk) hx hxN
    have hk : k = 4 := by
      have h16 : 2 ^ k = 16 := by rw [← hkK, hKeq, card_Z8]
      interval_cases k <;> simp_all
    have h16 := card_le_of_eSpan8 _ (C.mem_hatE_F4 (N8_le_Z8.trans hKeq.symm.le))
    rw [card_map_hat e, hcardE] at h16
    have : Module.finrank (ZMod 2) ↥(D.hat (l32nE T V V₂ g)) = 3 := by omega
    rw [this] at h16
    norm_num at h16
  ·
    push Not at hNK
    have hKN : img8 D e (CFSG.conjugate (l32nW T V V₂) g) ≤ N8 := hNK
    have hk3 : k ≤ 3 := by
      have := Subgroup.card_le_of_le hKN
      rw [hkK, card_N8] at this
      by_contra hc
      push Not at hc
      have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hc
      omega
    have hk : k = 3 := by omega
    have hKeq : img8 D e (CFSG.conjugate (l32nW T V V₂) g) = N8 :=
      Subgroup.eq_of_le_of_card_ge hKN (by rw [hkK, card_N8, hk]; norm_num)
    have hW := C.mem_hatE_F4 hKeq.symm.le
    have hfa : fC e (D.π a) = 0 := by
      rw [fC_apply e, C.ePiA, ← dotN_spec, fB_spec.1]
      rfl
    obtain ⟨x, hx, hxw⟩ := C.hat3 (fC e) hfa
    have hxK : matOf e x ∈ N8 := by
      rw [← hKeq]
      exact Subgroup.mem_map_of_mem _ hx
    refine not_transv hxK fun c hc => ?_
    obtain ⟨y, hyE, hye⟩ := Submodule.mem_map.mp (eSpan8_mem _ hW c hc)
    rw [LinearEquiv.coe_coe] at hye
    rw [← hye, matOf_mulVec, hxw y hyE, map_add, map_smul, C.ePiA, fC_apply]

end Ctx8_F4

theorem false_of_case1442EightPrime_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h12811 : Lemma12_8_11_F4)
    (h12811h : Lemma12_8_11_hat_F4) (h12812 : Lemma12_8_12_two_F4) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h : Hyp14310One G T L V)
    (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)) (hV₂ : IsL32NPlane T V V₂)
    (hgP : g ∈ p128 T L V) (hgH : g ∉ l32nH T V) (h8 : Case1442EightPrime T V V₂ g D) : False := by
  obtain ⟨a, e, C⟩ := exists_ctx8_F4 h1332 h1334 h1222 h12213 h12811 h12811h h12812 h37 h38 h39 h
    hext hV₂ hgP hgH h8
  exact C.false_F4

end CFSG.Quasithin.H13.L1442E8
