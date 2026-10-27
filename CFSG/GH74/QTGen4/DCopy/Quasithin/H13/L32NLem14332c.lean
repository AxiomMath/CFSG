module

public import CFSG.Quasithin.H13.L32NLem14332c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14312a

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace L14332

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} {g a : G}
  {D : HatModelU (fsuU T V)}

theorem card_hat_E_sq_le_F4 (h12811 : Lemma12_8_11_F4) (C : Ctx14332 G T L V V₂ g a D) :
    Nat.card ↥(D.hat (l32nE T V V₂ g)) ^ 2 ≤ Nat.card D.V := by
  obtain ⟨-, hE, -⟩ := h12811 G T L V 3 (fsuV1 T V) V₂ C.setting g C.gP C.gN
  have hEU : l32nE T V V₂ g ≤ fsuU T V := inf_le_left.trans inf_le_left
  have hEc : ∀ x ∈ l32nE T V V₂ g, ∀ y ∈ l32nE T V V₂ g, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  exact card_sq_le_of_isotropic D.nondegenerate (D.isotropic_hat hEU hEc)

theorem card_zU_eq_four_of_g22_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    (h12811 : Lemma12_8_11_F4) (h12811h : Lemma12_8_11_hat_F4) (hKGr : KGG22Rank)
    (C : Ctx14332 G T L V V₂ g a D) (h6 : G112Concl6 (D.img (l32nH T V))) :
    Nat.card ↥(D.img (CFSG.conjugate (centerOf (fsuU T V)) g)) = 2 := by
  have := finite_linearEquiv D
  have hd : Module.finrank (ZMod 2) D.V = 6 := h6.1

  have H := L14312.g101Hyp_F4 h1222 h12213 C.setting C.gP C.gN C.aV₂ C.a1 D
  have hX8 : Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) ≤ 8 :=
    hKGr D.V D.B H.alt H.nondegenerate hd (D.img (l32nH T V)) H.isometry h6.2 _ H.X_le
      H.X_comm H.X_sq

  obtain ⟨-, h5, -⟩ := h12811h G T L V 3 (fsuV1 T V) V₂ C.setting g C.gP C.gN a C.aV₂ C.a1 D
  have hE := card_hat_E_sq_le_F4 h12811 C
  have : Module.Finite (ZMod 2) D.V := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D.V), hd,
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(D.hat (l32nE T V V₂ g))), Nat.card_zmod,
    ← pow_mul] at hE
  have hE3 : Module.finrank (ZMod 2) ↥(D.hat (l32nE T V V₂ g)) ≤ 3 := by
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hE
    omega
  rw [hd] at h5
  set r := (D.img (CFSG.conjugate (centerOf (fsuU T V)) g)).relIndex
    (D.img (CFSG.conjugate (l32nW T V V₂) g)) with hr
  have hlog : 2 ≤ Nat.log 2 r := by
    change Module.finrank (ZMod 2) ↥(D.hat (l32nE T V V₂ g)) + Nat.log 2 r = 6 - 1 at h5
    omega
  have hle := img_zU_le C
  have hmul := Subgroup.relIndex_mul_card (H := D.img (CFSG.conjugate (centerOf (fsuU T V)) g))
    (K := D.img (CFSG.conjugate (l32nW T V V₂) g))
  rw [inf_eq_left.mpr hle, ← hr] at hmul
  have hXpos : 0 < Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) := Nat.card_pos
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    omega
  have hr4 : 4 ≤ r := by
    have := Nat.pow_log_le_self 2 hr0
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ Nat.log 2 r := Nat.pow_le_pow_right (by norm_num) hlog
      _ ≤ r := this
  have hZ := C.card_zU
  have h4 := four_le_card_zU C
  have hpos : 0 < Nat.card ↥(D.img (CFSG.conjugate (centerOf (fsuU T V)) g)) := Nat.card_pos
  have : Nat.card ↥(D.img (CFSG.conjugate (centerOf (fsuU T V)) g)) ≤ 2 := by
    by_contra hc
    push Not at hc
    have : 4 * 3 ≤ r * Nat.card ↥(D.img (CFSG.conjugate (centerOf (fsuU T V)) g)) :=
      Nat.mul_le_mul hr4 hc
    omega
  omega

theorem img_normalizer_le_normalizer_zU_F4 (h12812 : Lemma12_8_12_two_F4)
    (C : Ctx14332 G T L V V₂ g a D) :
    D.img (l32nH T V ⊓ Subgroup.normalizer (V₂ : Set G)) ≤
      Subgroup.normalizer (D.img (CFSG.conjugate (centerOf (fsuU T V)) g) :
        Set (D.V ≃ₗ[ZMod 2] D.V)) := by
  intro γ hγ
  obtain ⟨h, hh, hN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
  obtain ⟨-, h2⟩ := h12812 G T L V 3 (fsuV1 T V) V₂ C.setting g C.gP C.gN
  exact rho_mem_normalizer_img D C.zUg_le hN (h2 hh)

theorem not_g22_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h12811 : Lemma12_8_11_F4)
    (h12811h : Lemma12_8_11_hat_F4) (h12812 : Lemma12_8_12_two_F4) (hKGr : KGG22Rank)
    (hKG : KGG22PointStab) (C : Ctx14332 G T L V V₂ g a D)
    (h6 : G112Concl6 (D.img (l32nH T V))) : False := by
  have := finite_linearEquiv D
  have hZ2 := card_zU_eq_four_of_g22_F4 h1222 h12213 h12811 h12811h hKGr C h6
  have hZ4 : Nat.card ↥(centerOf (fsuU T V)) = 4 := by
    have := C.card_zU; omega
  have hodd := odd_centralizes_of_card_four C hZ4
  have hstab := stab_le C hodd
  have hnorm := img_normalizer_le_normalizer_zU_F4 h12812 C
  set Hd := D.img (l32nH T V) with hHd
  set Td := D.img T with hTd
  set Zd := D.img (CFSG.conjugate (centerOf (fsuU T V)) g) with hZd
  have hTH : Td ≤ Hd ⊓ MulAction.stabilizer (D.V ≃ₗ[ZMod 2] D.V) (D.π a) := by
    intro γ hγ
    obtain ⟨x, hx, hxN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
    exact img_normalizer_le_stab D C.aV₂ C.aU C.a1 C.V₂_cases C.lt.le
      (L128A.HatU.rho_mem_img D (C.T_le hx) hxN)
  have hTN : Td ≤ Subgroup.normalizer (Zd : Set (D.V ≃ₗ[ZMod 2] D.V)) := fun γ hγ =>
    hnorm (hstab (hTH hγ))

  have hT64 : Nat.card Td = 64 := by
    obtain ⟨k, hk⟩ := (isPGroup_img_T C).exists_card_eq
    have hmul := Subgroup.relIndex_mul_card (H := Td) (K := Hd)
    rw [inf_eq_left.mpr (hTH.trans inf_le_left), hk, h6.2] at hmul
    have hr := Nat.odd_iff.mp C.T_odd
    change Td.relIndex Hd % 2 = 1 at hr
    have hdvd : 2 ^ k ∣ 2 ^ 6 * 189 := Dvd.intro_left _ (by rw [hmul]; norm_num)
    have hk6 : k ≤ 6 := by
      have hcop : Nat.Coprime (2 ^ k) 189 := Nat.Coprime.pow_left k (by norm_num)
      have := hcop.dvd_of_dvd_mul_right hdvd
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
    rw [hk]
    interval_cases k <;> norm_num at hmul ⊢ <;> omega

  have hZ2p : IsPGroup 2 ↥Zd := IsPGroup.of_card (n := 1) (by rw [hZ2, pow_one])
  have hsup := IsPGroup.to_sup_of_normal_left' hZ2p (isPGroup_img_T C) hTN
  have hZH : Zd ≤ Hd := by
    intro γ hγ
    obtain ⟨x, hx, hxN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
    exact L128A.HatU.rho_mem_img D (C.zUg_le hx) hxN
  have hsupH : Zd ⊔ Td ≤ Hd := sup_le hZH (hTH.trans inf_le_left)
  have hcard : Nat.card ↥(Zd ⊔ Td) ≤ 64 := by
    obtain ⟨k, hk⟩ := hsup.exists_card_eq
    have hdvd := Subgroup.card_dvd_of_le hsupH
    rw [hk, h6.2] at hdvd
    have hdvd' : 2 ^ k ∣ 2 ^ 6 * 189 := by simpa using hdvd
    have hcop : Nat.Coprime (2 ^ k) 189 := Nat.Coprime.pow_left k (by norm_num)
    have := hcop.dvd_of_dvd_mul_right hdvd'
    rw [hk]
    exact Nat.le_of_dvd (by norm_num) this
  have heq : Td = Zd ⊔ Td :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hT64]; exact hcard)
  have hZT : Zd ≤ Td := heq ▸ le_sup_left

  have hB : ∀ γ ∈ Hd, ∀ v w, D.B (γ v) (γ w) = D.B v w := by
    intro γ hγ v w
    obtain ⟨x, -, hxN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
    exact L128A.HatU.B_rho D ⟨x, hxN⟩ v w
  exact hKG D.V D.B (L128A.HatU.B_isAlt D) (L128A.HatU.B_nondegenerate D) h6.1 Hd hB h6.2
    (D.π a) C.pi_ne Td Zd hTH hT64 hZT hZ2 hTN (hstab.trans hnorm)

end L14332

end CFSG.Quasithin.H13
