module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OutU
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4U4Order
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvolutionCentralizer

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace UnitaryConj

open Matrix CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher UnitaryOut

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem exists_dual_pair (V₁ V₂ : Submodule K (Fin 4 → K))
    (h1 : Module.finrank K V₁ = 2) (h2 : Module.finrank K V₂ = 2)
    (hpair : ∀ w ∈ V₂, (∀ v ∈ V₁, stdHermForm h 4 v w = 0) → w = 0) :
    ∃ e g : Fin 2 → (Fin 4 → K), (∀ a, e a ∈ V₁) ∧ (∀ b, g b ∈ V₂) ∧
      ∀ a b, stdHermForm h 4 (e a) (g b) = if a = b then 1 else 0 := by
  classical
  let bV := Module.finBasisOfFinrankEq K V₁ h1
  set e : Fin 2 → (Fin 4 → K) := fun a => (bV a : Fin 4 → K) with he
  let Θ : V₂ →ₗ[K] (Fin 2 → K) :=
    LinearMap.pi fun a => (stdHermForm h 4 (e a)).comp V₂.subtype
  have hΘ : ∀ w : V₂, ∀ a, Θ w a = stdHermForm h 4 (e a) w := fun w a => rfl
  have hΘinj : Function.Injective Θ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker] at hw
    rw [Submodule.mem_bot]
    apply Subtype.ext
    apply hpair w w.2
    intro v hv
    have hw' : ∀ a, stdHermForm h 4 (e a) w = 0 := fun a => by
      rw [← hΘ, hw, Pi.zero_apply]
    have hv' : (⟨v, hv⟩ : V₁) = ∑ a, (bV.repr ⟨v, hv⟩ a) • bV a := (bV.sum_repr _).symm
    have hv'' : v = ∑ a, (bV.repr ⟨v, hv⟩ a) • e a := by
      have := congrArg Subtype.val hv'
      rw [Submodule.coe_sum] at this
      exact this
    rw [hv'', map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hw', smul_zero]
  have hΘsurj : Function.Surjective Θ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [h2, Module.finrank_fin_fun])).1 hΘinj
  choose g' hg' using fun b : Fin 2 => hΘsurj (Pi.single b 1)
  refine ⟨e, fun b => (g' b : Fin 4 → K), fun a => (bV a).2, fun b => (g' b).2, ?_⟩
  intro a b
  have := congrFun (hg' b) a
  rw [hΘ] at this
  rw [this, Pi.single_apply]

@[expose] def stdG : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

@[expose] def stdDl (l : K) : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![l, l, -l, -l]

theorem uStar_mul_apply (P : Matrix (Fin 4) (Fin 4) K) (a b : Fin 4) :
    (uStar h P * P) a b = stdHermForm h 4 (fun k => P k a) (fun k => P k b) := by
  rw [stdHermForm_apply, Matrix.mul_apply]
  rfl

theorem norm_eq_neg_one_of_sq (hq : p ^ f % 4 = 1) {c : K} (hc : c ^ 2 = -1) :
    h.norm c = -1 := by
  rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, ← pow_succ']
  obtain ⟨t, ht⟩ : ∃ t, p ^ f + 1 = 2 * (2 * t + 1) := ⟨(p ^ f - 1) / 4, by omega⟩
  rw [ht, pow_mul, hc, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]

theorem apply_eq_of_mem_eigenPlus {V : Type*} [AddCommGroup V] [Module K V]
    {l : K} (hl : l ≠ 0) {T : Module.End K V} {v : V} (hv : v ∈ eigenPlus l T) : T v = l • v := by
  have hv' : (invSMulOp l T - 1) v = 0 := hv
  rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, invSMulOp,
    LinearMap.smul_apply] at hv'
  conv_rhs => rw [← hv']
  rw [smul_smul, mul_inv_cancel₀ hl, one_smul]

theorem apply_eq_of_mem_eigenMinus {V : Type*} [AddCommGroup V] [Module K V]
    {l : K} (hl : l ≠ 0) {T : Module.End K V} {v : V} (hv : v ∈ eigenMinus l T) :
    T v = -l • v := by
  have hv' : (invSMulOp l T + 1) v = 0 := hv
  rw [LinearMap.add_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg, invSMulOp,
    LinearMap.smul_apply] at hv'
  have : T v = l • (l⁻¹ • T v) := by rw [smul_smul, mul_inv_cancel₀ hl, one_smul]
  rw [this, hv', smul_neg, neg_smul]

theorem exists_hyperbolic_basis (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1)
    (X : ClassicalGroups.UnitaryFlag.unitarySU p f K 4)
    (hX : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = -1) {l : K} (hl : l ^ 2 = -1) :
    ∃ P : Matrix (Fin 4) (Fin 4) K, uStar h P * P = stdG ∧
      ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * P = P * stdDl l := by
  classical
  set B := stdHermForm h 4 with hB
  set A := toSesq h 4 X with hAdef
  set M := ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hM
  have hAv : ∀ v, unitaryOp A v = M *ᵥ v := fun v => toSesq_apply h 4 X v
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have hAA : unitaryOp A * unitaryOp A = -1 := by
    refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, hAv, hAv, Matrix.mulVec_mulVec, hX, LinearMap.neg_apply,
      Module.End.one_apply, Matrix.neg_mulVec, Matrix.one_mulVec]
  have hA2 : orderOf (QuotientGroup.mk A : sesqProjUnitary h B) = 2 := by
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      refine ⟨-1, ?_, ?_⟩
      · rw [UnitaryFieldData.norm, map_neg, map_one]
        ring
      · change (((A ^ 2 : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup K (Fin 4 → K)) :
          Module.End K (Fin 4 → K)) = _
        rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, pow_two]
        change unitaryOp A * unitaryOp A = _
        rw [hAA]
        ext v
        simp
    · intro h1
      rw [QuotientGroup.eq_one_iff] at h1
      obtain ⟨c, hc, hAc⟩ := h1
      have hAc' : unitaryOp A = c • 1 := hAc
      have hc2 : c ^ 2 = -1 := by
        have h3 := hAA
        rw [hAc', smul_mul_smul_comm, one_mul, ← sq] at h3
        have h4 := congrArg (fun T : Module.End K (Fin 4 → K) => T (Pi.single 0 1) 0) h3
        simpa using h4
      rw [norm_eq_neg_one_of_sq h hq hc2] at hc
      apply h2K
      linear_combination -hc
  obtain ⟨l', hl'0, hAA', hN, -, -, hcompl, -, hpair, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp2
      (by rw [Module.finrank_fin_fun]; norm_num) (stdHermForm_isSymm h 4)
      (stdHermForm_separatingLeft h 4) hA2
  have hl'2 : l' ^ 2 = -1 := by
    rw [hAA] at hAA'
    have h4 := congrArg (fun T : Module.End K (Fin 4 → K) => T (Pi.single 0 1) 0) hAA'
    simp at h4
    linear_combination -h4
  have hN1 : h.norm l' = -1 := norm_eq_neg_one_of_sq h hq hl'2
  obtain ⟨hisoP, hisoM, hdeq, h2d, hpairP, hpairM, -⟩ := hpair hN1
  rw [Module.finrank_fin_fun] at h2d
  have hdP : Module.finrank K (eigenPlus l' (unitaryOp A)) = 2 := by omega
  have hdM : Module.finrank K (eigenMinus l' (unitaryOp A)) = 2 := by omega
  have hsymm : ∀ v w, B v w = 0 → B w v = 0 := by
    intro v w hvw
    rw [← (stdHermForm_isSymm h 4).eq, hvw, map_zero]
  have hll' : l' = l ∨ l' = -l := by
    have : (l' - l) * (l' + l) = 0 := by linear_combination hl'2 - hl
    rcases mul_eq_zero.1 this with h1 | h1
    · left; linear_combination h1
    · right; linear_combination h1
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hl
    exact zero_ne_one (neg_eq_zero.1 hl.symm).symm
  obtain ⟨V₁, V₂, hd1, hd2, hiso1, hiso2, hpair12, heig1, heig2⟩ :
      ∃ V₁ V₂ : Submodule K (Fin 4 → K), Module.finrank K V₁ = 2 ∧ Module.finrank K V₂ = 2 ∧
        (∀ v ∈ V₁, ∀ w ∈ V₁, B v w = 0) ∧ (∀ v ∈ V₂, ∀ w ∈ V₂, B v w = 0) ∧
        (∀ w ∈ V₂, (∀ v ∈ V₁, B v w = 0) → w = 0) ∧
        (∀ v ∈ V₁, M *ᵥ v = l • v) ∧ (∀ w ∈ V₂, M *ᵥ w = -l • w) := by
    rcases hll' with rfl | rfl
    · refine ⟨_, _, hdP, hdM, hisoP, hisoM, hpairM, fun v hv => ?_, fun w hw => ?_⟩
      · rw [← hAv]
        exact apply_eq_of_mem_eigenPlus hl'0 hv
      · rw [← hAv]
        exact apply_eq_of_mem_eigenMinus hl'0 hw
    · refine ⟨_, _, hdM, hdP, hisoM, hisoP, fun w hw hall => hpairP w hw fun v hv =>
        hsymm _ _ (hall v hv), fun v hv => ?_, fun w hw => ?_⟩
      · rw [← hAv, apply_eq_of_mem_eigenMinus hl'0 hv, neg_neg]
      · rw [← hAv, apply_eq_of_mem_eigenPlus hl'0 hw]
  obtain ⟨e, g, he, hg, hdual⟩ := exists_dual_pair h V₁ V₂ hd1 hd2 hpair12
  set col : Fin 4 → Fin 4 → K := ![e 0, e 1, g 0, g 1] with hcol
  set P : Matrix (Fin 4) (Fin 4) K := Matrix.of fun i j => col j i with hP
  have hPcol : ∀ j, (fun k => P k j) = col j := fun j => rfl
  refine ⟨P, ?_, ?_⟩
  · ext a b
    rw [uStar_mul_apply, hPcol, hPcol]
    have hge : ∀ a b, stdHermForm h 4 (g a) (e b) = if a = b then 1 else 0 := by
      intro a b
      rw [← (stdHermForm_isSymm h 4).eq, hdual]
      by_cases hab : b = a
      · subst hab; simp
      · simp [hab, Ne.symm hab]
    have hee : ∀ a b, stdHermForm h 4 (e a) (e b) = 0 := fun a b => hiso1 _ (he a) _ (he b)
    have hgg : ∀ a b, stdHermForm h 4 (g a) (g b) = 0 := fun a b => hiso2 _ (hg a) _ (hg b)
    fin_cases a <;> fin_cases b <;> simp [hcol, stdG, hdual, hge, hee, hgg]
  · ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    change (M *ᵥ col j) i = _
    fin_cases j <;> simp [hcol, stdDl, hP, heig1 _ (he _), heig2 _ (hg _),
      Matrix.diagonal_apply, mul_comm]

omit [Field K] in
theorem det_stdG {R : Type*} [CommRing R] :
    (!![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0] : Matrix (Fin 4) (Fin 4) R).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

@[expose] noncomputable def stdE (μ : K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.diagonal ![μ, 1, (h.bar μ)⁻¹, 1]

theorem uStar_stdE_mul (μ : K) (hμ : μ ≠ 0) :
    uStar h (stdE h μ) * stdG * stdE h μ = stdG := by
  have hb : h.bar μ ≠ 0 := fun h0 => hμ ((map_eq_zero h.bar).1 h0)
  have hbb : h.bar (h.bar μ)⁻¹ = μ⁻¹ := by rw [map_inv₀, h.bar_bar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uStar, stdE, stdG, Matrix.mul_apply, Matrix.diagonal_apply, hbb, hμ, hb]

theorem exists_mul_inv_bar_eq (u : Kˣ) (hu : (u : K) ^ (p ^ f + 1) = 1) :
    ∃ μ : Kˣ, (μ : K) * (h.bar μ)⁻¹ = u := by
  classical
  have : Finite K := h.finite
  have hcard : Nat.card Kˣ = (p ^ f) ^ 2 - 1 := by
    rw [Nat.card_units, h.card, ← pow_mul, mul_comm]
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf γ = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, hcard]
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hγ u)
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
  have hu' : u ^ (p ^ f + 1) = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hu, Units.val_one])
  have hdvd : ((orderOf γ : ℕ) : ℤ) ∣ m * ((p ^ f + 1 : ℕ) : ℤ) := by
    rw [← orderOf_dvd_iff_zpow_eq_one.symm.trans Iff.rfl]
    rw [_root_.zpow_mul, hm, zpow_natCast, hu']
  rw [hord] at hdvd
  obtain ⟨k, hk⟩ := hdvd
  have hfac : (((p ^ f) ^ 2 - 1 : ℕ) : ℤ) = ((p ^ f - 1 : ℕ) : ℤ) * ((p ^ f + 1 : ℕ) : ℤ) := by
    have : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := by
      zify [hq1, Nat.one_le_pow 2 (p ^ f) (by omega)]
      ring
    rw [this]
    push_cast [hq1]
    ring
  have hm' : m = ((p ^ f - 1 : ℕ) : ℤ) * k := by
    rw [hfac] at hk
    have hne : ((p ^ f + 1 : ℕ) : ℤ) ≠ 0 := by positivity
    have : m * ((p ^ f + 1 : ℕ) : ℤ) = (((p ^ f - 1 : ℕ) : ℤ) * k) * ((p ^ f + 1 : ℕ) : ℤ) := by
      rw [hk]
      ring
    exact mul_right_cancel₀ hne this
  refine ⟨γ ^ (-k), ?_⟩
  have hbar : ∀ ν : Kˣ, h.bar (ν : K) = ((ν ^ (p ^ f) : Kˣ) : K) := fun ν => by
    rw [UnitaryFieldData.bar_apply, Units.val_pow_eq_pow_val]
  rw [hbar, ← Units.val_inv_eq_inv_val, ← Units.val_mul, ← hm, hm']
  congr 1
  rw [← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_neg, ← _root_.zpow_add]
  congr 1
  push_cast [hq1]
  ring

include h in
theorem exists_conj_unitary (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1)
    (X Y : ClassicalGroups.UnitaryFlag.unitarySU p f K 4)
    (hX : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = -1)
    (hY : ((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = -1) :
    ∃ g : ClassicalGroups.UnitaryFlag.unitarySU p f K 4, g * X = Y * g := by
  classical
  have : Finite K := h.finite
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨l, hl⟩ : ∃ l : K, l ^ 2 = -1 := by
    have hcK : Fintype.card K % 4 = 1 := by
      rw [Fintype.card_eq_nat_card, h.card, pow_mul, Nat.pow_mod]
      rw [show p ^ 2 % 4 = 1 by
        have := h.prime.eq_one_or_self_of_dvd 2
        rcases Nat.even_or_odd p with he | ho
        · exfalso
          exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two h.prime).1
            (even_iff_two_dvd.1 he)).symm
        · obtain ⟨t, rfl⟩ := ho
          ring_nf
          omega]
      simp
    obtain ⟨r, hr⟩ := (FiniteField.isSquare_neg_one_iff (F := K)).2 (by omega)
    exact ⟨r, by rw [sq, ← hr]⟩
  obtain ⟨P, hP, hXP⟩ := exists_hyperbolic_basis h hp2 hq X hX hl
  obtain ⟨Q, hQ, hYQ⟩ := exists_hyperbolic_basis h hp2 hq Y hY hl
  set MX := ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hMX
  set MY := ((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hMY
  have hdetStar : ∀ M : Matrix (Fin 4) (Fin 4) K, (uStar h M).det = h.bar M.det := by
    intro M
    rw [uStar, det_transpose, RingHom.map_det]
    rfl
  have hGdet : (stdG : Matrix (Fin 4) (Fin 4) K).det = 1 := det_stdG
  have hdet0 : ∀ M : Matrix (Fin 4) (Fin 4) K, uStar h M * M = stdG → M.det ≠ 0 := by
    intro M hM h0
    have := congrArg Matrix.det hM
    rw [det_mul, h0, mul_zero, hGdet] at this
    exact zero_ne_one this
  have hPd := hdet0 P hP
  have hQd := hdet0 Q hQ
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.2 hPd
  have hQu : IsUnit Q.det := isUnit_iff_ne_zero.2 hQd
  have hPX : P⁻¹ * MX = stdDl l * P⁻¹ := by
    calc P⁻¹ * MX = P⁻¹ * MX * (P * P⁻¹) := by rw [Matrix.mul_nonsing_inv _ hPu, Matrix.mul_one]
      _ = P⁻¹ * (MX * P) * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = P⁻¹ * (P * stdDl l) * P⁻¹ := by rw [hXP]
      _ = stdDl l * P⁻¹ := by
          rw [← Matrix.mul_assoc P⁻¹, Matrix.nonsing_inv_mul _ hPu, Matrix.one_mul]
  have hPinvG : uStar h P⁻¹ * stdG * P⁻¹ = 1 := by
    calc uStar h P⁻¹ * stdG * P⁻¹ = uStar h P⁻¹ * (uStar h P * P) * P⁻¹ := by rw [hP]
      _ = (uStar h P⁻¹ * uStar h P) * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [← uStar_mul, Matrix.mul_nonsing_inv _ hPu, uStar_one, Matrix.one_mul]
  set g₀ := Q * P⁻¹ with hg₀
  have hg₀X : g₀ * MX = MY * g₀ := by
    rw [hg₀, Matrix.mul_assoc, hPX, ← Matrix.mul_assoc, ← hYQ, Matrix.mul_assoc]
  have hg₀U : uStar h g₀ * g₀ = 1 := by
    rw [hg₀, uStar_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (uStar h Q), hQ,
      ← Matrix.mul_assoc]
    exact hPinvG
  have hg₀d : g₀.det ≠ 0 := by
    rw [hg₀, det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero hQd (inv_ne_zero hPd)
  have hu1 : g₀.det ^ (p ^ f + 1) = 1 := by
    have := congrArg Matrix.det hg₀U
    rw [det_mul, hdetStar, det_one, UnitaryFieldData.bar_apply, ← pow_succ] at this
    exact this
  obtain ⟨μ, hμ⟩ := exists_mul_inv_bar_eq h (Units.mk0 g₀.det hg₀d)⁻¹ (by
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, hu1, inv_one])
  set c := P * stdE h μ * P⁻¹ with hc
  have hE : stdE h μ * stdDl l = stdDl l * stdE h μ := by
    rw [stdE, stdDl, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hcX : c * MX = MX * c := by
    calc P * stdE h μ * P⁻¹ * MX = P * stdE h μ * stdDl l * P⁻¹ := by
          rw [Matrix.mul_assoc (P * stdE h μ), hPX, ← Matrix.mul_assoc]
      _ = P * stdDl l * stdE h μ * P⁻¹ := by rw [Matrix.mul_assoc P, hE, ← Matrix.mul_assoc]
      _ = MX * (P * stdE h μ * P⁻¹) := by rw [← hXP]; simp only [Matrix.mul_assoc]
  have hcU : uStar h c * c = 1 := by
    rw [hc, uStar_mul, uStar_mul]
    calc uStar h P⁻¹ * (uStar h (stdE h μ) * uStar h P) * (P * stdE h μ * P⁻¹)
        = uStar h P⁻¹ * (uStar h (stdE h μ) * (uStar h P * P) * stdE h μ) * P⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = uStar h P⁻¹ * stdG * P⁻¹ := by rw [hP, uStar_stdE_mul h μ μ.ne_zero]
      _ = 1 := hPinvG
  have hcd : c.det = (μ : K) * (h.bar μ)⁻¹ := by
    rw [hc, det_mul, det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', stdE,
      det_diagonal]
    simp [Fin.prod_univ_four]
    field_simp
  set M := g₀ * c with hM
  have hMd : M.det = 1 := by
    rw [hM, det_mul, hcd, hμ, Units.val_inv_eq_inv_val, Units.val_mk0, mul_inv_cancel₀ hg₀d]
  have hMu : IsUnit M.det := by rw [hMd]; exact isUnit_one
  let gGL : GL (Fin 4) K := ⟨M, M⁻¹, Matrix.mul_nonsing_inv _ hMu, Matrix.nonsing_inv_mul _ hMu⟩
  have hgmem : gGL ∈ ClassicalGroups.UnitaryFlag.unitarySU p f K 4 := by
    rw [ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h]
    refine ⟨hMd, ?_⟩
    change uStar h M * M = 1
    rw [hM, uStar_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (uStar h g₀), hg₀U, Matrix.one_mul,
      hcU]
  refine ⟨⟨gGL, hgmem⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  change M * MX = MY * M
  rw [hM, Matrix.mul_assoc, hcX, ← Matrix.mul_assoc, hg₀X, Matrix.mul_assoc]

end UnitaryConj

end CFSG.ComponentClassification.CatFactsL4U4
