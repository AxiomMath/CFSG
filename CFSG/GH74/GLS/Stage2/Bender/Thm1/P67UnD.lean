module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UnMain
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UnDCore

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Un

open Matrix CFSG CFSG.Blueprint CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.GH74.GLS.Stage2.Bender.Thm1


section Lift

variable {K : Type} [Field K] (h : UnitaryFieldData 3 1 K) {r ε : ℕ}

theorem un_exists_lift_coprime (hr : 1 ≤ r) (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε) {s : ℕ}
    (hs2 : ¬ 2 ∣ s) {z : MulAut (hypPSU h r ε)} (hz : z ^ s = 1) :
    ∃ B : hypSU h r ε, B ^ s = 1 ∧ MulAut.conj (hypProj h r ε B) = z := by
  classical
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hpp : (3 : ℕ).Prime := Nat.prime_three
  have : Nonempty (HypIndex r ε) := ⟨Sum.inl ⟨0, hr⟩⟩
  have : Finite K := h.finite
  have hKcard : Nat.card K = 3 ^ 2 := by rw [h.card]
  have hcop2 : Nat.Coprime s 2 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hs2).symm
  obtain ⟨x, hx⟩ := semilinearAutHom_surjective h hr hε hp2 hn z
  have hσs : (x : SemiGL (HypIndex r ε) K).right ^ s = 1 := by
    have h1 : unSigma h hr hε hn hp2 (semilinearAutHom h hr hε x) ^ s = 1 := by
      rw [← map_pow, hx, hz, map_one]
    rwa [unSigma_apply] at h1
  have hσ2 : (x : SemiGL (HypIndex r ε) K).right ^ 2 = 1 := by
    have hc := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hpp K hKcard).1
    have h2 := pow_card_eq_one' (G := RingAut K) (x := (x : SemiGL (HypIndex r ε) K).right)
    rwa [hc] at h2
  have hxr : (x : SemiGL (HypIndex r ε) K).right = 1 := by
    have h13 : (x : SemiGL (HypIndex r ε) K).right ^ Nat.gcd s 2 = 1 :=
      pow_gcd_eq_one.mpr ⟨hσs, hσ2⟩
    rwa [hcop2, pow_one] at h13
  set A : GL (HypIndex r ε) K := (x : SemiGL (HypIndex r ε) K).left with hA
  have hxinl : (x : SemiGL (HypIndex r ε) K) = SemidirectProduct.inl A :=
    SemidirectProduct.ext (by simp [hA]) (by simpa using hxr)
  have hxp : semilinearAutHom h hr hε (x ^ s) = 1 := by
    rw [map_pow, hx, hz]
  obtain ⟨-, c, hc⟩ := (semilinearAutHom_eq_one_iff h hr hε hn _).mp hxp
  have hAp : A ^ s = GeneralLinearGroup.scalar _ c := by
    have h1 : (((x ^ s : semilinearSimilitudes h r ε)) : SemiGL (HypIndex r ε) K) =
        SemidirectProduct.inl (A ^ s) := by
      rw [Subgroup.coe_pow, hxinl, map_pow]
    rw [h1, SemidirectProduct.left_inl] at hc
    exact hc
  have hcu : Nat.card Kˣ = 8 := by
    have : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hKcard]
    norm_num
  have hcop8 : Nat.Coprime (Nat.card Kˣ) s := by
    rw [hcu]
    have : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [this]
    exact Nat.Coprime.pow_left 3 hcop2.symm
  obtain ⟨lu, hlu⟩ := (powCoprime hcop8).surjective c
  rw [powCoprime_apply] at hlu
  set B : GL (HypIndex r ε) K := GeneralLinearGroup.scalar _ lu⁻¹ * A with hB
  have hBs : B ^ s = 1 := by
    have hcomm : Commute (GeneralLinearGroup.scalar (HypIndex r ε) lu⁻¹) A :=
      (commute_scalar lu⁻¹ A).symm
    rw [hB, hcomm.mul_pow, hAp, ← map_pow, ← map_mul, inv_pow, hlu, inv_mul_cancel, map_one]
  obtain ⟨μ, hμ0, hμbar, hμ⟩ := x.2
  have hAμ : (((A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ * hypGram r ε K *
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) = μ • hypGram r ε K := hμ
  have hBmat : (B : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      ((lu⁻¹ : Kˣ) : K) • (A : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
    rw [hB, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul]
  set μ' : K := h.bar ((lu⁻¹ : Kˣ) : K) * ((lu⁻¹ : Kˣ) : K) * μ with hμ'
  have hBμ : (((B : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ * hypGram r ε K *
      (B : Matrix (HypIndex r ε) (HypIndex r ε) K)) = μ' • hypGram r ε K := by
    rw [hBmat, Matrix.map_smul' _ _ _ (map_mul h.bar), Matrix.transpose_smul]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
    rw [hAμ, smul_smul, smul_smul, hμ']
    congr 1
    ring
  have hpow : ∀ k : ℕ,
      ((((B ^ k : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ *
        hypGram r ε K * ((B ^ k : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K)) = μ' ^ k • hypGram r ε K := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Units.val_mul, conjTranspose_mul_mul h, ih, Matrix.mul_smul, Matrix.smul_mul,
        hBμ, smul_smul, pow_succ]
  have hJ0 : hypGram r ε K ≠ 0 := by
    intro h0
    apply det_hypGram_ne_zero (r := r) (ε := ε) (K := K)
    rw [h0]
    exact Matrix.det_zero
  have hμ'bar : h.bar μ' = μ' := by
    rw [hμ', map_mul, map_mul, h.bar_bar, hμbar]
    ring
  have hμ'0 : μ' ≠ 0 := by
    intro h0
    have h1 := hBμ
    rw [h0, zero_smul] at h1
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_zero] at h2
    have hdJ := det_hypGram_ne_zero (r := r) (ε := ε) (K := K)
    have hBu : IsUnit (B : Matrix (HypIndex r ε) (HypIndex r ε) K).det :=
      (Matrix.isUnits_det_units B)
    rcases mul_eq_zero.mp h2 with h3 | h3
    · rcases mul_eq_zero.mp h3 with h4 | h4
      · rw [Matrix.det_transpose] at h4
        have h5 : h.bar (B : Matrix (HypIndex r ε) (HypIndex r ε) K).det = 0 := by
          rw [RingHom.map_det]
          exact h4
        exact hBu.ne_zero ((UnitaryFieldData.bar_eq_zero_iff h).mp h5)
      · exact hdJ h4
    · exact hBu.ne_zero h3
  have hμ'1 : μ' = 1 := by
    have h1 := hpow s
    rw [hBs, Units.val_one] at h1
    simp only [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), Matrix.transpose_one,
      Matrix.one_mul, Matrix.mul_one] at h1
    have h2 : (μ' ^ s - 1) • hypGram r ε K = 0 := by
      rw [sub_smul, one_smul, ← h1, sub_self]
    have h3 : μ' ^ s = 1 := by
      rcases smul_eq_zero.mp h2 with h3 | h3
      · exact sub_eq_zero.mp h3
      · exact absurd h3 hJ0
    have h4 : μ' ^ 2 = 1 := by
      have h5 : μ' ^ 3 = μ' := by
        have := h.bar_apply μ'
        rw [hμ'bar] at this
        simpa using this.symm
      have : μ' ^ 2 * μ' = 1 * μ' := by rw [one_mul, ← pow_succ]; exact h5
      exact mul_right_cancel₀ hμ'0 this
    have h13 : μ' ^ Nat.gcd s 2 = 1 := pow_gcd_eq_one.mpr ⟨h3, h4⟩
    rwa [hcop2, pow_one] at h13
  have hdet : (B : Matrix (HypIndex r ε) (HypIndex r ε) K).det = 1 := by
    set d := (B : Matrix (HypIndex r ε) (HypIndex r ε) K).det with hd
    have hds : d ^ s = 1 := by
      rw [hd, ← Matrix.det_pow, ← Units.val_pow_eq_pow_val, hBs, Units.val_one, Matrix.det_one]
    have h1 := congrArg Matrix.det hBμ
    rw [hμ'1, one_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
    have h2 : (((B : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)).det = h.bar d := by
      rw [hd, RingHom.map_det]
      rfl
    rw [h2] at h1
    have hdJ := det_hypGram_ne_zero (r := r) (ε := ε) (K := K)
    have h3 : h.bar d * d = 1 := by
      have : (h.bar d * d - 1) * (hypGram r ε K).det = 0 := by linear_combination h1
      rcases mul_eq_zero.mp this with h4 | h4
      · exact sub_eq_zero.mp h4
      · exact absurd h4 hdJ
    have h4 : d ^ 4 = 1 := by
      have hb : h.bar d = d ^ 3 := by simpa using h.bar_apply d
      rw [hb] at h3
      calc d ^ 4 = d ^ 3 * d := by ring
        _ = 1 := h3
    have hcop4 : Nat.Coprime s 4 := by
      have : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [this]
      exact Nat.Coprime.pow_right 2 hcop2
    have h13 : d ^ Nat.gcd s 4 = 1 := pow_gcd_eq_one.mpr ⟨hds, h4⟩
    rwa [hcop4, pow_one] at h13
  have hBmem : B ∈ hypSU h r ε := by
    refine mem_hypSU.mpr ⟨?_, hdet⟩
    rw [hBμ, hμ'1, one_smul]
  refine ⟨⟨B, hBmem⟩, Subtype.ext (by simpa using hBs), ?_⟩
  rw [← hx]
  ext y
  obtain ⟨g', rfl⟩ := hypProj_surjective h r ε y
  rw [semilinearAutHom_apply h hr hε x g', MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  apply Subtype.ext
  have hsc : ∀ y : GL (HypIndex r ε) K,
      GeneralLinearGroup.scalar (HypIndex r ε) lu⁻¹ * y *
        (GeneralLinearGroup.scalar (HypIndex r ε) lu⁻¹)⁻¹ = y := fun y => by
    rw [← (commute_scalar lu⁻¹ y).eq, mul_inv_cancel_right]
  change B * (g' : GL (HypIndex r ε) K) * B⁻¹ =
    A * glAut (x : SemiGL (HypIndex r ε) K).right g' * A⁻¹
  rw [hxr, map_one, MulAut.one_apply, hB, _root_.mul_inv_rev]
  calc GeneralLinearGroup.scalar (HypIndex r ε) lu⁻¹ * A * (g' : GL (HypIndex r ε) K) *
        (A⁻¹ * (GeneralLinearGroup.scalar (HypIndex r ε) lu⁻¹)⁻¹)
      = GeneralLinearGroup.scalar (HypIndex r ε) lu⁻¹ * (A * (g' : GL (HypIndex r ε) K) * A⁻¹) *
        (GeneralLinearGroup.scalar (HypIndex r ε) lu⁻¹)⁻¹ := by group
    _ = A * (g' : GL (HypIndex r ε) K) * A⁻¹ := hsc _

end Lift

section UD

variable {K : Type} [Field K] (h : UnitaryFieldData 3 1 K)

theorem noN2_U4_three (hcen : Subgroup.center (hypPSU h 2 0) = ⊥)
    {V Z : Subgroup (MulAut (hypPSU h 2 0))} (h2 : N2Cfg (hypPSU h 2 0) 3 V Z) : False := by
  classical
  have hpp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (3 : ℕ).Prime := ⟨hpp⟩
  have : Finite K := h.finite
  have : CharP K 3 := h.charP
  have hr : 1 ≤ 2 := by norm_num
  have hε : 0 ≤ 1 := by norm_num
  have hn : 3 ≤ 2 * 2 + 0 := by norm_num
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨-, -, hVe, hVc, -, hZodd, hZcop, hZbot, hVZ⟩ := h2
  obtain ⟨v, hvV, hv1, g, hg3, hgv⟩ := un_exists_inner_of_elem h hr hε hn hp2 hVe hVc
  have hg1 : g ≠ 1 := by
    rintro rfl
    apply hv1
    rw [← hgv, map_one, map_one]
  have hZfin : Finite ↥Z := Nat.finite_of_card_ne_zero (fun h0 => by
    rw [h0] at hZodd
    exact absurd hZodd (by decide))
  have hZnt : Nat.card ↥Z ≠ 1 := by
    intro h1
    apply hZbot
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have : Subsingleton ↥Z := (Nat.card_eq_one_iff_unique.mp h1).1
    exact congrArg Subtype.val (Subsingleton.elim (⟨z, hz⟩ : ↥Z) 1)
  obtain ⟨s, hsp, hsd⟩ := Nat.exists_prime_and_dvd hZnt
  have : Fact s.Prime := ⟨hsp⟩
  obtain ⟨z, hzs⟩ := exists_prime_orderOf_dvd_card' s hsd
  have hs2 : ¬ 2 ∣ s := by
    intro h2s
    exact (Nat.not_even_iff_odd.mpr hZodd) (even_iff_two_dvd.mpr (h2s.trans hsd))
  have hs3 : ¬ 3 ∣ s := by
    intro h3s
    have : s = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hsp).mp h3s).symm
    rw [this] at hsd
    have := Nat.Coprime.eq_one_of_dvd hZcop.symm hsd
    omega
  have hz1 : (z : MulAut (hypPSU h 2 0)) ≠ 1 := by
    intro h1
    have : orderOf z = 1 := by
      have : z = 1 := Subtype.ext h1
      rw [this, orderOf_one]
    rw [hzs] at this
    exact hsp.one_lt.ne' this
  have hzpow : (z : MulAut (hypPSU h 2 0)) ^ s = 1 := by
    have := pow_orderOf_eq_one z
    rw [hzs] at this
    simpa using congrArg Subtype.val this
  obtain ⟨B, hBs, hBz⟩ := un_exists_lift_coprime h hr hε hn hs2 hzpow
  have hB1 : B ≠ 1 := by
    rintro rfl
    apply hz1
    rw [← hBz, map_one, map_one]
  have hinj := mulAut_conj_injective_of_center_bot hcen
  have hcomm : hypProj h 2 0 g * hypProj h 2 0 B = hypProj h 2 0 B * hypProj h 2 0 g := by
    apply hinj
    have := hVZ v hvV z z.2
    rw [← hgv, ← hBz] at this
    rw [map_mul, map_mul]
    exact this
  have hgB : g * B = B * g := by
    have h1 : B * g * B⁻¹ = g := by
      refine eq_of_proj_eq_of_pow h (p := 3) ?_ hg3 ?_
      · rw [conj_pow, hg3, mul_one, mul_inv_cancel]
      · rw [map_mul, map_mul, map_inv, hcomm.symm, mul_inv_cancel_right]
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  exact hB1 (eq_one_of_commute_order_three h (hermGram_hyp h 2 0) (by simp) hg3 hg1 hgB hs2 hs3 hBs)

end UD

theorem cf67CoreDeriv_U4_three {Y : Type} [Group Y] [Finite Y] (hLie : LieModel Y .PSU 4 3 1) :
    CF67CoreDeriv Y 3 := by
  obtain ⟨-, K, _, _, h, ⟨e⟩⟩ := un_hyp_model 2 0 (by norm_num) (by norm_num) hLie
  refine CF67CoreDeriv.of_mulEquiv e ?_
  intro hs hn V Z h2 h3
  exact noN2_U4_three h (un_center_eq_bot_of_simple hs hn) h2

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Un
