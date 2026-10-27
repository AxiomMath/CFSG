module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestJ4
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupCenterTrans
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Parts
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Defs

public section

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
  CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier
open scoped commutatorElement

theorem ys03_two_ne_zero_zmod11 : (2 : ZMod 11) ≠ 0 := by decide

theorem ys03_matrix_eq_one (M : Matrix (Fin 2) (Fin 2) (ZMod 11)) (hMM : M * M = 1)
    (hdet : M.det = 1) (w : Fin 2 → ZMod 11) (hw : w ≠ 0) (hMw : M.mulVec w = w) : M = 1 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have h00 := congrFun (congrFun hMM 0) 0
  have h01 := congrFun (congrFun hMM 0) 1
  have h10 := congrFun (congrFun hMM 1) 0
  have h11 := congrFun (congrFun hMM 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne,
    ne_eq, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true, Fin.one_eq_zero_iff,
    OfNat.ofNat_ne_zero, Nat.succ_ne_self] at h00 h01 h10 h11
  rw [Matrix.det_fin_two] at hdet
  have hw0 := congrFun hMw 0
  have hw1 := congrFun hMw 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hw0 hw1
  have h2 : M 0 0 * (M 0 0 + M 1 1) = 2 := by linear_combination h00 + hdet
  have hne : M 0 0 + M 1 1 ≠ 0 := by
    intro h
    rw [h, mul_zero] at h2
    exact ys03_two_ne_zero_zmod11 h2.symm
  have hb : M 0 1 = 0 :=
    (mul_eq_zero.1 (by linear_combination h01 : M 0 1 * (M 0 0 + M 1 1) = 0)).resolve_right hne
  have hc : M 1 0 = 0 :=
    (mul_eq_zero.1 (by linear_combination h10 : M 1 0 * (M 0 0 + M 1 1) = 0)).resolve_right hne
  have ha0 : M 0 0 ≠ 0 := by
    intro h
    rw [h] at h00
    rw [hb] at h00
    simp at h00
  have hda : M 1 1 = M 0 0 := by
    apply mul_left_cancel₀ ha0
    rw [hb, hc] at hdet
    linear_combination hdet - h00 + M 1 0 * hb
  have hw0' : (M 0 0 - 1) * w 0 = 0 := by
    rw [hb] at hw0
    linear_combination hw0
  have hw1' : (M 1 1 - 1) * w 1 = 0 := by
    rw [hc] at hw1
    linear_combination hw1
  have ha1 : M 0 0 = 1 := by
    by_cases hw0z : w 0 = 0
    · have hw1z : w 1 ≠ 0 := fun h => hw (by ext i; fin_cases i <;> simp [hw0z, h])
      have : M 1 1 - 1 = 0 := (mul_eq_zero.1 hw1').resolve_right hw1z
      have hd1 : M 1 1 = 1 := by linear_combination this
      rw [← hda, hd1]
    · have : M 0 0 - 1 = 0 := (mul_eq_zero.1 hw0').resolve_right hw0z
      linear_combination this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha1, hb, hc, hda]


theorem ys03_J4_no_involution {t : J} (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (htz : t * qz = qz * t) {u : J} (hu : u ∈ Q11) (hnu : u ∉ Subgroup.zpowers qz)
    (htu : t * u = u * t) : False := by
  have htN : t ∈ Subgroup.normalizer (Q11 : Set J) :=
    centralizer_qz_le_normalizer_J4 (Subgroup.mem_centralizer_singleton_iff.2 htz)
  set n : Subgroup.normalizer (Q11 : Set J) := ⟨t, htN⟩ with hn
  have hMM : heisData.actMat n * heisData.actMat n = 1 := by
    rw [← heisData.actMat_mul, ← heisData.actMat_one]
    exact congrArg _ (Subtype.ext ht2)
  have hxy : ⁅(heisData.x : J), (heisData.y : J)⁆ = qz := by
    rw [heisData_x, heisData_y]
    rfl
  have hz : orderOf (⁅(heisData.x : J), (heisData.y : J)⁆) = 11 := by
    rw [hxy]; exact orderOf_qz
  have hconj := heis_conj_comm_eq heisData center_Q11_eq_zpowers_comm hz n
  rw [hxy] at hconj
  have hqz : (n : J) * qz * (n : J)⁻¹ = qz := (mul_inv_eq_iff_eq_mul).2 htz
  rw [hqz] at hconj
  have hdet : Matrix.det (heisData.actMat n) = 1 := by
    have h1 : qz ^ (Matrix.det (heisData.actMat n)).val = qz ^ 1 := by rw [← hconj, pow_one]
    rw [pow_eq_pow_iff_modEq, orderOf_qz] at h1
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 h1
    rwa [ZMod.natCast_zmod_val, Nat.cast_one] at h2
  set q : Q11 := ⟨u, hu⟩ with hq
  have hnq : Q11.normalizerMonoidHom n q = q := by
    apply Subtype.ext
    rw [normalizerMonoidHom_coe]
    exact (mul_inv_eq_iff_eq_mul).2 htu
  have hMw : (heisData.actMat n).mulVec (Multiplicative.toAdd (heisData.π q)) =
      Multiplicative.toAdd (heisData.π q) := by
    rw [← heisData.π_conj, hnq]
  have hw : Multiplicative.toAdd (heisData.π q) ≠ 0 := by
    intro h0
    have h1 : heisData.π q = 1 := Multiplicative.toAdd.injective (by rw [h0]; rfl)
    have h2 : q ∈ heisData.π.ker := h1
    rw [heisData.ker_eq, center_Q11_eq] at h2
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 h2
    exact hnu (Subgroup.mem_zpowers_iff.2 ⟨m, by simpa using congrArg Subtype.val hm⟩)
  have hM1 := ys03_matrix_eq_one _ hMM hdet _ hw hMw
  have htQ : t ∈ Q11 := actMat_eq_one_mem n hM1
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  have hdvd : orderOf (⟨t, htQ⟩ : Q11) ∣ Nat.card Q11 := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hord, card_Q11] at hdvd
  norm_num at hdvd

theorem ys03_J4_oPrime_noncentral {u : J} (hu : u ∈ Q11) (hnu : u ∉ Subgroup.zpowers qz) :
    GLAPPrimeCoreOf 11 (Subgroup.centralizer ({u} : Set J)) = ⊥ := by
  have h11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  set C := Subgroup.centralizer ({u} : Set J) with hC
  set O := GLAPPrimeCoreOf 11 C with hO
  obtain ⟨h121, h242⟩ := card_centralizer_noncentral_le hu hnu
  have hdvd : Nat.card O ∣ Nat.card C := Subgroup.card_dvd_of_le (GLAPPrimeCoreOf_le C)
  have hcop : Nat.Coprime (Nat.card O) 121 :=
    ((coprime_card_GLAPPrimeCoreOf (by norm_num) C).pow_left 2).symm
  obtain ⟨k, hk⟩ := h121
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, mul_zero] at hk
      exact absurd hk Nat.card_pos.ne'
    · exact h0
  have hk2 : k ≤ 2 := by omega
  rw [hk] at hdvd
  have hOk : Nat.card O ∣ k := hcop.dvd_of_dvd_mul_left hdvd
  have hO2 : Nat.card O ≤ 2 := (Nat.le_of_dvd hk0 hOk).trans hk2
  by_contra hne
  have hO1 : Nat.card O ≠ 1 := fun h => hne (Subgroup.card_eq_one.1 h)
  have hOc : Nat.card O = 2 := by
    have := Nat.card_pos (α := O)
    omega
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := O) 2 (by rw [hOc])
  have ht' : orderOf (t : J) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have ht2 : (t : J) * (t : J) = 1 := by
    have h2 := pow_orderOf_eq_one (t : J)
    rw [ht', pow_two] at h2
    exact h2
  have ht1 : (t : J) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht'
    exact absurd ht' (by norm_num)
  have htC : (t : J) ∈ C := GLAPPrimeCoreOf_le C t.2
  have htu : (t : J) * u = u * (t : J) := by
    have h := (Subgroup.mem_centralizer_singleton_iff (G := ↥J)).1 (hC ▸ htC)
    exact h
  have hquz : qz ∈ C := by
    rw [hC]
    exact (Subgroup.mem_centralizer_singleton_iff (G := ↥J)).2 (qz_commute_of_mem hu).symm
  have hconj : qz * (t : J) * qz⁻¹ ∈ O := GLAPPrimeCoreOf_conj_mem qz hquz _ t.2
  have hz : Subgroup.zpowers (t : J) = O := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 t.2) ?_
    rw [Nat.card_zpowers, ht', hOc]
  have hmem : qz * (t : J) * qz⁻¹ ∈ Subgroup.zpowers (t : J) := by
    rw [hz]
    exact hconj
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hm' : (t : J) ^ (m % 2) = qz * (t : J) * qz⁻¹ := by
    rw [← hm]
    have h2 := zpow_mod_orderOf (t : J) m
    rw [ht', Nat.cast_ofNat] at h2
    exact h2
  have hqt : qz * (t : J) * qz⁻¹ = (t : J) := by
    rcases Int.emod_two_eq_zero_or_one m with h | h
    · exfalso
      rw [h, zpow_zero] at hm'
      apply ht1
      have : qz * (t : J) * qz⁻¹ = 1 := hm'.symm
      calc (t : J) = qz⁻¹ * (qz * (t : J) * qz⁻¹) * qz := by group
        _ = 1 := by rw [this]; group
    · rw [h, zpow_one] at hm'
      exact hm'.symm
  have htz : (t : J) * qz = qz * (t : J) := ((mul_inv_eq_iff_eq_mul).1 hqt).symm
  exact ys03_J4_no_involution ht2 ht1 htz hu hnu htu

theorem ys03_oPrime_J : OPrimeCoreTrivialAt 11 ↥J := by
  intro x hx
  obtain ⟨h, hh⟩ := exists_conj_mem_of_orderOf Q11 card_Q11 not_eleven_pow_four_dvd_card_J hx
  have huo : orderOf (h⁻¹ * x * h) = 11 := by
    have := orderOf_conj_eq' h⁻¹ x
    rw [inv_inv] at this
    rw [this, hx]
  have hbot : GLAPPrimeCoreOf 11 (Subgroup.centralizer ({h⁻¹ * x * h} : Set ↥J)) = ⊥ := by
    by_cases hz : h⁻¹ * x * h ∈ Subgroup.zpowers qz
    · have hzp : Subgroup.zpowers (h⁻¹ * x * h) = Subgroup.zpowers qz :=
        Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hz)
          (by rw [Nat.card_zpowers, Nat.card_zpowers, huo, orderOf_qz])
      rw [centralizer_singleton_eq_of_zpowers hzp]
      exact gLAPPrimeCoreOf_centralizer_qz_eq_bot
    · exact ys03_J4_oPrime_noncentral hh hz
  have key := (gLAPPrimeCoreOf_centralizer_conj (p := 11) h (h⁻¹ * x * h)).2 hbot
  rwa [show h * (h⁻¹ * x * h) * h⁻¹ = x by group] at key

noncomputable def ys03_seedEquivJ4 :
    @MulEquiv CFSG.Blueprint.NativeSporadic.J4 ↥J MulOneClass.toMul MulOneClass.toMul :=
  seedEquiv j4Facts.mat

theorem ys03_oPrime_J4_carrier : OPrimeCoreTrivialAt 11 (CFSG.Blueprint.NativeSporadic.Carrier .J4) :=
  OPrimeCoreTrivialAt.of_mulEquiv (K' := ↥J) ys03_seedEquivJ4 ys03_oPrime_J

theorem ys03_sporadicOPrimeHolds_J4_eleven : SporadicOPrimeHolds .J4 11 :=
  fun _ _ _ _ ⟨e⟩ => OPrimeCoreTrivialAt.of_mulEquiv e ys03_oPrime_J4_carrier

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
