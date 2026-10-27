module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OrdU2
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4StabL
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Blocks

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace StabU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
  CFSG.LinearGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] noncomputable def toSesqGU (A : GL (Fin 4) K)
    (hA : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1) :
    sesqUnitaryGroup (stdHermForm h 4) :=
  ⟨Matrix.GeneralLinearGroup.toLin A, fun x y => by
    change stdHermForm h 4 ((A : Matrix (Fin 4) (Fin 4) K) *ᵥ x)
      ((A : Matrix (Fin 4) (Fin 4) K) *ᵥ y) = stdHermForm h 4 x y
    rw [stdHermForm_eq_gramForm, gramForm_mulVec, Matrix.mul_one]
    change gramForm h (uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K))
      x y = _
    rw [hA]⟩

theorem toSesqGU_apply (A : GL (Fin 4) K)
    (hA : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    (x : Fin 4 → K) :
    unitaryOp (toSesqGU h A hA) x = (A : Matrix (Fin 4) (Fin 4) K) *ᵥ x :=
  rfl

theorem unitary_stdJ : uStar h (stdJ : Matrix (Fin 4) (Fin 4) K) * stdJ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uStar, stdJ, Matrix.mul_apply, Fin.sum_univ_four]

@[expose] noncomputable def stdJSU : unitarySU p f K 4 :=
  ⟨toGL stdJ StabL.det_stdJ, by
    rw [mem_unitarySU_iff h, coe_toGL]
    exact ⟨StabL.det_stdJ, unitary_stdJ h⟩⟩

include h in
theorem eq_smul_one_of_comm (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1) {B : Matrix (Fin 4) (Fin 4) K}
    (hB : ∀ g : unitarySU p f K 4,
      B * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * B) :
    ∃ c : K, B = c • 1 := by
  classical
  have : Finite K := h.finite
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  obtain ⟨l, hl⟩ : ∃ l : K, l ^ 2 = -1 := by
    let : Fintype K := Fintype.ofFinite K
    have hcK : Fintype.card K % 4 = 1 := by
      rw [Fintype.card_eq_nat_card, h.card, pow_mul, Nat.pow_mod]
      rw [show p ^ 2 % 4 = 1 by
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
  have hJJ : ((stdJSU h : unitarySU p f K 4) : GL (Fin 4) K) *
      ((stdJSU h : unitarySU p f K 4) : GL (Fin 4) K) = -1 := by
    apply Units.ext
    rw [Units.val_mul]
    change stdJ * stdJ = _
    rw [Blocks.stdJ_mul_stdJ, Units.val_neg, Units.val_one]
  obtain ⟨Pm, hPm, -⟩ := exists_hyperbolic_basis h hp2 hq (stdJSU h)
    (by rw [← Units.val_mul, hJJ, Units.val_neg, Units.val_one]) hl
  have hPdet : Pm.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hPm
    have hGd : (stdG : Matrix (Fin 4) (Fin 4) K).det = 1 := det_stdG
    rw [det_mul, h0, mul_zero, hGd] at this
    exact zero_ne_one this
  set P : GL (Fin 4) K := GeneralLinearGroup.mkOfDetNeZero Pm hPdet with hPdef
  have hPv : (P : Matrix (Fin 4) (Fin 4) K) = Pm := GeneralLinearGroup.val_mkOfDetNeZero _ _
  have hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG := by
    rw [hPv]
    exact hPm
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hμb := bar_ne_of_generator h hμ
  obtain ⟨W, hW⟩ : ∃ W : Matrix (Fin 4) (Fin 4) K,
      W = (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * B * P := ⟨_, rfl⟩
  have hPiP : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * P = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcomm : ∀ (U : Matrix (Fin 4) (Fin 4) K) (hU : uStar h U * stdG * U = stdG)
      (hd : U.det = 1), W * U = U * W := by
    intro U hU hd
    have e := hB (hypSU h P hP U hU hd)
    rw [val_hypSU] at e
    calc W * U = (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (B * ((P : Matrix (Fin 4) (Fin 4) K) * U *
          (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K))) * P := by
          rw [hW]
          simp only [Matrix.mul_assoc]
          rw [hPiP, Matrix.mul_one]
      _ = (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (((P : Matrix (Fin 4) (Fin 4) K) * U *
          (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) * B) * P := by rw [e]
      _ = U * W := by
          rw [hW]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) (P : Matrix (Fin 4) (Fin 4) K),
            hPiP, Matrix.one_mul]
  have hWd := eq_blk_diag_of_comm h hμb (hcomm _ (unitary_U12 h 1) (det_U12 h 1))
    (hcomm _ (unitary_U21 h 1) (det_U21 h 1)) (hcomm _ (unitary_U12 h μ) (det_U12 h μ))
  set β : K := μ - h.bar μ with hβdef
  have hβ0 : β ≠ 0 := sub_ne_zero.2 (Ne.symm hμb)
  have hββ : β + h.bar β = 0 := by
    rw [hβdef, map_sub, h.bar_bar]
    ring
  have hg := hcomm (gfix β 0) (unitary_gfix h hββ (by rw [map_zero, add_zero])) (det_gfix β 0)
  rw [hWd] at hg
  have hxy := eq_of_blk_comm_gfix hβ0 hg
  refine ⟨W 0 0, ?_⟩
  have hW1 : W = W 0 0 • 1 := by
    conv_lhs => rw [hWd]
    rw [← hxy]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk]
  have hPPi : (P : Matrix (Fin 4) (Fin 4) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc B = (P : Matrix (Fin 4) (Fin 4) K) * W * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
        rw [hW]
        simp only [← Matrix.mul_assoc]
        rw [hPPi, Matrix.one_mul, Matrix.mul_assoc, hPPi, Matrix.mul_one]
    _ = (P : Matrix (Fin 4) (Fin 4) K) * (W 0 0 • 1) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
        conv_lhs => rw [hW1]
    _ = W 0 0 • 1 := by
        rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPPi]

theorem false_of_card_le_centralizer {q a : ℕ} (hq5 : 5 ≤ q)
    (hcard : 2 * a = q ^ 4 * (q ^ 2 - 1) * (q ^ 4 - 1))
    (hle : a ≤ q ^ 2 * (q ^ 4 - 1) * (q - 1)) : False := by
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hineq : q ^ 4 * (q ^ 2 - 1) * (q ^ 4 - 1) ≤ 2 * (q ^ 2 * (q ^ 4 - 1) * (q - 1)) := by
    rw [← hcard]
    exact Nat.mul_le_mul_left 2 hle
  zify [h4, h2, (by omega : 1 ≤ q)] at hineq
  have hq5' : (5 : ℤ) ≤ q := by exact_mod_cast hq5
  have hA : (0 : ℤ) < (q : ℤ) ^ 4 - 1 := by nlinarith
  have hB : (0 : ℤ) < (q : ℤ) - 1 := by linarith
  have hC : (0 : ℤ) < (q : ℤ) ^ 2 := by positivity
  have hD : (0 : ℤ) < (q : ℤ) ^ 2 * ((q : ℤ) + 1) - 2 := by nlinarith
  have hP := mul_pos (mul_pos (mul_pos hC hA) hB) hD
  have key : (q : ℤ) ^ 4 * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 4 - 1) -
      2 * ((q : ℤ) ^ 2 * ((q : ℤ) ^ 4 - 1) * ((q : ℤ) - 1)) =
      (q : ℤ) ^ 2 * ((q : ℤ) ^ 4 - 1) * ((q : ℤ) - 1) * ((q : ℤ) ^ 2 * ((q : ℤ) + 1) - 2) := by
    ring
  linarith

theorem uStar_smul (c : K) (M : Matrix (Fin 4) (Fin 4) K) :
    uStar h (c • M) = h.bar c • uStar h M := by
  ext i j
  simp [uStar]

include h in
theorem false_of_inner_fixed (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1) {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    (hA2 : ∀ g : unitarySU p f K 4,
      (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) *
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K)))
    (hconj : ∀ g : unitarySU p f K 4, A * g * A⁻¹ ∈ unitarySU p f K 4)
    {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    (hα : ∀ g : unitarySU p f K 4, α (QuotientGroup.mk g) =
      QuotientGroup.mk (⟨A * g * A⁻¹, hconj g⟩ : unitarySU p f K 4))
    (hα1 : α ≠ 1) {M : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))} (hM : ∀ x ∈ M, α x = x)
    (hcard : 2 * Nat.card M = (p ^ f) ^ 4 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1))
    {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hsq : s ∣ (p ^ f) ^ 2 + 1)
    {y : StatedProj (StatedSU 4 (p ^ f) K)} (hyM : y ∈ M) (hy : orderOf y = s) : False := by
  classical
  have : Finite K := h.finite
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have := Fact.mk hs
  obtain ⟨c, hc⟩ := eq_smul_one_of_comm h hp2 hq
    (B := (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K)) hA2
  set A' := toSesqGU h A hAu with hA'
  have hA'op : ∀ v, unitaryOp A' v = (A : Matrix (Fin 4) (Fin 4) K) *ᵥ v := toSesqGU_apply h A hAu
  have hAA' : unitaryOp A' * unitaryOp A' = c • 1 := by
    refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, hA'op, hA'op, Matrix.mulVec_mulVec, hc, LinearMap.smul_apply,
      Module.End.one_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hcN : h.norm c = 1 := by
    have e : uStar h ((A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K)) *
        ((A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K)) = 1 := by
      rw [uStar_mul]
      calc uStar h (A : Matrix (Fin 4) (Fin 4) K) * uStar h (A : Matrix (Fin 4) (Fin 4) K) *
            ((A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K)) =
          uStar h (A : Matrix (Fin 4) (Fin 4) K) * (uStar h (A : Matrix (Fin 4) (Fin 4) K) *
            (A : Matrix (Fin 4) (Fin 4) K)) * (A : Matrix (Fin 4) (Fin 4) K) := by
              simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hAu, Matrix.mul_one, hAu]
    rw [hc, uStar_smul, uStar_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
      at e
    have := congrFun (congrFun e 0) 0
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
    rw [UnitaryFieldData.norm, mul_comm]
    exact this
  have hord : orderOf (QuotientGroup.mk A' : sesqProjUnitary h (stdHermForm h 4)) = 2 := by
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      refine ⟨c, hcN, ?_⟩
      rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, pow_two]
      exact hAA'
    · intro h1
      rw [QuotientGroup.eq_one_iff] at h1
      obtain ⟨d, -, hAd⟩ := h1
      have hAd' : (A : Matrix (Fin 4) (Fin 4) K) = d • 1 := by
        apply Matrix.toLin'.injective
        refine LinearMap.ext fun v => ?_
        have := congrArg (fun T : Module.End K (Fin 4 → K) => T v) hAd
        simp only [LinearMap.smul_apply, Module.End.one_apply] at this
        rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
        exact this
      apply hα1
      ext x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      rw [hα g, MulAut.one_apply]
      congr 1
      apply ext_val
      change ((A * g * A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = _
      have hcomm : (A : Matrix (Fin 4) (Fin 4) K) *
          ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) := by
        rw [hAd', Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
      rw [Units.val_mul, Units.val_mul, hcomm, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.mul_one]
  obtain ⟨l, hl0, hAA, hN, hP, hMm, hcompl, hsplit, hpair, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp2
      (by rw [Module.finrank_fin_fun]; norm_num) (stdHermForm_isSymm h 4)
      (stdHermForm_separatingLeft h 4) hord
  obtain ⟨Y₀, hY₀⟩ := QuotientGroup.mk_surjective y
  have hY₀s : Y₀ ^ s ∈ scal p f K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hY₀, ← hy, pow_orderOf_eq_one]
  have hsodd : Odd s := hs.odd_of_ne_two hs2
  obtain ⟨Y, hYy, hYs⟩ : ∃ Y : unitarySU p f K 4, QuotientGroup.mk Y = y ∧ Y ^ s = 1 := by
    have hsub : ∀ z ∈ scal p f K, z = 1 ∨ z = negOne h := by
      intro z hz
      have hz' : (z : GL (Fin 4) K) ∈ StatedScalars (Fin 4) K := hz
      obtain ⟨c', hc'⟩ := hz'
      have hcSU : GeneralLinearGroup.scalar (Fin 4) c' ∈ StatedSU 4 (p ^ f) K := by
        rw [hc']
        exact z.2
      rcases scalar_eq_one_or_neg_one_U4 h hq hcSU with rfl | rfl
      · left
        apply Subtype.ext
        rw [← hc', map_one]
        rfl
      · right
        apply Subtype.ext
        rw [← hc', scalar_neg_one_eq]
        rfl
    rcases hsub _ hY₀s with h1 | h1
    · exact ⟨Y₀, hY₀, h1⟩
    · refine ⟨negOne h * Y₀, ?_, ?_⟩
      · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (negOne_mem_scal h), one_mul, hY₀]
      · have hc := mem_center_of_mem_scal (negOne_mem_scal h)
        have hcomm : Commute (negOne h) Y₀ := (Subgroup.mem_center_iff.mp hc Y₀).symm
        have hn2 : negOne h ^ 2 = 1 := by
          apply Subtype.ext
          apply Units.ext
          simp [negOne, sq]
        obtain ⟨t, ht⟩ := hsodd
        rw [hcomm.mul_pow, h1, ← pow_succ, ht, show 2 * t + 1 + 1 = 2 * (t + 1) by ring,
          pow_mul, hn2, one_pow]
  have hAY : (A : Matrix (Fin 4) (Fin 4) K) * ((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * A := by
    set u : unitarySU p f K 4 := ⟨A * Y * A⁻¹, hconj Y⟩ with hu
    have h1 : (QuotientGroup.mk u : StatedProj (StatedSU 4 (p ^ f) K)) = QuotientGroup.mk Y := by
      rw [hu, ← hα, hYy, hM y hyM]
    rw [QuotientGroup.eq] at h1
    have hzc := mem_center_of_mem_scal h1
    have hus : u ^ s = 1 := by
      apply Subtype.ext
      change (A * Y * A⁻¹ : GL (Fin 4) K) ^ s = 1
      rw [conj_pow]
      have : ((Y ^ s : unitarySU p f K 4) : GL (Fin 4) K) = 1 := by rw [hYs]; rfl
      rw [← SubgroupClass.coe_pow, this, mul_one, mul_inv_cancel]
    have hzs : (u⁻¹ * Y) ^ s = 1 := by
      have hcomm : Commute u⁻¹ Y := by
        have e1 : Y * u⁻¹ = u⁻¹ * Y := by
          calc Y * u⁻¹ = u * (u⁻¹ * Y) * u⁻¹ := by group
            _ = (u⁻¹ * Y) * u * u⁻¹ := by rw [Subgroup.mem_center_iff.mp hzc u]
            _ = u⁻¹ * Y := by group
        exact e1.symm
      rw [hcomm.mul_pow, inv_pow, hus, inv_one, one_mul, hYs]
    have hz1 := eq_one_of_pow_odd hsodd hzs (pow_four_eq_one_of_mem_scal h h1)
    have huY : u = Y := inv_mul_eq_one.1 hz1
    have e := congrArg (fun g : unitarySU p f K 4 =>
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) huY
    simp only [hu, Units.val_mul] at e
    have hAi : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (A : Matrix (Fin 4) (Fin 4) K) * ((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (A : Matrix (Fin 4) (Fin 4) K) * ((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K)) := by
          rw [hAi, Matrix.mul_one]
      _ = ((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * A := by
          rw [← Matrix.mul_assoc, e]
  have hY1 : Y ≠ 1 := by
    intro h1
    rw [h1, QuotientGroup.mk_one] at hYy
    rw [← hYy, orderOf_one] at hy
    exact hs.one_lt.ne' hy.symm
  have hYC : toSesq h 4 Y ∈ Subgroup.centralizer {A'} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    apply Units.ext
    refine LinearMap.ext fun v => ?_
    change unitaryOp (toSesq h 4 Y) (unitaryOp A' v) = unitaryOp A' (unitaryOp (toSesq h 4 Y) v)
    rw [toSesq_apply, toSesq_apply, hA'op, hA'op, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hAY]
  set Y' : Subgroup.centralizer {A'} := ⟨toSesq h 4 Y, hYC⟩ with hY'
  have hY's : Y' ^ s = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, hY', ← map_pow, hYs, map_one]
    rfl
  have hY'1 : Y' ≠ 1 := by
    intro h1
    apply hY1
    apply toSesq_injective h 4
    rw [map_one]
    exact congrArg Subtype.val h1
  have hfin : Module.finrank K (Fin 4 → K) = 4 := Module.finrank_fin_fun K
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [hfin] at hsum
  rcases hN with hN1 | hN1
  ·
    obtain ⟨-, hsepP, hsepM, e₁, -⟩ := hsplit hN1
    have hdimP : 1 ≤ Module.finrank K (eigenPlus l (unitaryOp A')) := by
      rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
      exact hP
    have hdimM : 1 ≤ Module.finrank K (eigenMinus l (unitaryOp A')) := by
      rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
      exact hMm
    have : Finite (LinearMap.GeneralLinearGroup K (eigenPlus l (unitaryOp A'))) :=
      finite_generalLinearGroup'
    have : Finite (LinearMap.GeneralLinearGroup K (eigenMinus l (unitaryOp A'))) :=
      finite_generalLinearGroup'
    set u := e₁ Y' with hu
    have hu1 : u ^ s = 1 := by rw [hu, ← map_pow, hY's, map_one]
    have hP1 : u.1 = 1 := by
      apply eq_one_of_pow_eq_one_of_not_dvd hs
        (not_dvd_card_sesqUnitaryGroup h ((stdHermForm_isSymm h 4).domRestrict _) hsepP rfl
          hdimP (by omega) hs hs2 hsq)
      rw [← Prod.pow_fst, hu1]
      rfl
    have hM1 : u.2 = 1 := by
      apply eq_one_of_pow_eq_one_of_not_dvd hs
        (not_dvd_card_sesqUnitaryGroup h ((stdHermForm_isSymm h 4).domRestrict _) hsepM rfl
          hdimM (by omega) hs hs2 hsq)
      rw [← Prod.pow_snd, hu1]
      rfl
    exact hY'1 (e₁.injective (by rw [map_one, ← hu]; exact Prod.ext hP1 hM1))
  ·
    obtain ⟨-, -, hdeq, h2d, -⟩ := hpair hN1
    rw [hfin] at h2d
    have hdP : Module.finrank K (eigenPlus l (unitaryOp A')) = 2 := by omega
    have hdM : Module.finrank K (eigenMinus l (unitaryOp A')) = 2 := by omega
    have hdet : LinearMap.det (unitaryOp A') = l ^ 2 * (-l) ^ 2 := by
      rw [show l ^ 2 * (-l) ^ 2 = l ^ Module.finrank K (eigenPlus l (unitaryOp A')) *
        (-l) ^ Module.finrank K (eigenMinus l (unitaryOp A')) by rw [hdP, hdM]]
      refine det_eq_of_isCompl_smul hcompl (fun v hv => ?_) (fun v hv => ?_)
      · have hv' : (invSMulOp l (unitaryOp A') - 1) v = 0 := hv
        rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, invSMulOp,
          LinearMap.smul_apply] at hv'
        conv_rhs => rw [← hv']
        rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
      · have hv' : (invSMulOp l (unitaryOp A') + 1) v = 0 := hv
        rw [LinearMap.add_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg, invSMulOp,
          LinearMap.smul_apply] at hv'
        have : unitaryOp A' v = l • (l⁻¹ • unitaryOp A' v) := by
          rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
        rw [this, hv', smul_neg, neg_smul]
    have hdetA : (A : Matrix (Fin 4) (Fin 4) K).det = l ^ 4 := by
      have h1 : unitaryOp A' = Matrix.toLin' (A : Matrix (Fin 4) (Fin 4) K) := by
        refine LinearMap.ext fun v => ?_
        rw [Matrix.toLin'_apply]
        exact hA'op v
      rw [h1, LinearMap.det_toLin'] at hdet
      rw [hdet]
      ring
    have hcl : c = l ^ 2 := by
      have h1 := congrArg (fun T : Module.End K (Fin 4 → K) => T (Pi.single 0 1) 0)
        (hAA'.symm.trans hAA)
      simpa using h1
    obtain ⟨i, hi⟩ : ∃ i : K, i ^ 2 = -1 := by
      let : Fintype K := Fintype.ofFinite K
      have hcK : Fintype.card K % 4 = 1 := by
        rw [Fintype.card_eq_nat_card, h.card, pow_mul, Nat.pow_mod]
        rw [show p ^ 2 % 4 = 1 by
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
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hi
      exact one_ne_zero (by linear_combination hi : (1 : K) = 0)
    have hbi : h.bar i * i = -1 := by
      have := norm_eq_neg_one_of_sq h hq hi
      rw [UnitaryFieldData.norm, mul_comm] at this
      exact this
    have hbl : h.bar l * l = -1 := by
      have := hN1
      rw [UnitaryFieldData.norm, mul_comm] at this
      exact this
    set d : K := i * l⁻¹ with hd
    have hd0 : d ≠ 0 := mul_ne_zero hi0 (inv_ne_zero hl0)
    have hbl0 : h.bar l ≠ 0 := fun h0 => hl0 ((map_eq_zero h.bar).1 h0)
    have hdN : h.bar d * d = 1 := by
      rw [hd, map_mul, map_inv₀]
      field_simp
      linear_combination hbi - hbl
    set X'G : GL (Fin 4) K := GeneralLinearGroup.scalar (Fin 4) (Units.mk0 d hd0) * A with hX'G
    have hX'v : (X'G : Matrix (Fin 4) (Fin 4) K) = d • (A : Matrix (Fin 4) (Fin 4) K) := by
      rw [hX'G, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
      rfl
    have hX'SU : X'G ∈ unitarySU p f K 4 := by
      rw [mem_unitarySU_iff h, hX'v]
      refine ⟨?_, ?_⟩
      · rw [det_smul, Fintype.card_fin, hdetA, hd, mul_pow, inv_pow,
          show i ^ 4 = (i ^ 2) ^ 2 by ring, hi]
        field_simp
      · change uStar h (d • (A : Matrix (Fin 4) (Fin 4) K)) * (d • (A : Matrix (Fin 4) (Fin 4) K)) =
          1
        rw [uStar_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hAu, hdN, one_smul]
    set X' : unitarySU p f K 4 := ⟨X'G, hX'SU⟩ with hX'
    have hX'2 : ((X' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((X' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = -1 := by
      change (X'G : Matrix (Fin 4) (Fin 4) K) * (X'G : Matrix (Fin 4) (Fin 4) K) = -1
      rw [hX'v, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc, hcl, smul_smul, hd]
      have : i * l⁻¹ * (i * l⁻¹) * l ^ 2 = -1 := by
        field_simp
        linear_combination hi
      rw [this, neg_one_smul]
    have hscal : GeneralLinearGroup.scalar (Fin 4) (Units.mk0 d hd0) ∈
        Subgroup.center (GL (Fin 4) K) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨_, rfl⟩
    have hαX : ∀ x, α x = QuotientGroup.mk X' * x * (QuotientGroup.mk X')⁻¹ := by
      intro x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      rw [hα g, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      change A * g * A⁻¹ = X'G * g * X'G⁻¹
      set sc := GeneralLinearGroup.scalar (Fin 4) (Units.mk0 d hd0)
      have hs' : ∀ W : GL (Fin 4) K, sc * W = W * sc := fun W =>
        (Subgroup.mem_center_iff.mp hscal W).symm
      rw [hX'G]
      calc A * (g : GL (Fin 4) K) * A⁻¹ = sc * (A * (g : GL (Fin 4) K) * A⁻¹) * sc⁻¹ := by
            rw [hs' (A * (g : GL (Fin 4) K) * A⁻¹)]
            group
        _ = sc * A * (g : GL (Fin 4) K) * (sc * A)⁻¹ := by group
    obtain ⟨Pm, hPm, hXP⟩ := exists_hyperbolic_basis h hp2 hq X' hX'2 hi
    have hPdet : Pm.det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hPm
      have hGd : (stdG : Matrix (Fin 4) (Fin 4) K).det = 1 := det_stdG
      rw [det_mul, h0, mul_zero, hGd] at this
      exact zero_ne_one this
    set P : GL (Fin 4) K := GeneralLinearGroup.mkOfDetNeZero Pm hPdet with hPdef
    have hPv : (P : Matrix (Fin 4) (Fin 4) K) = Pm := GeneralLinearGroup.val_mkOfDetNeZero _ _
    have hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG := by
      rw [hPv]
      exact hPm
    have hXeq : X' = hypSU h P hP (X1 i) (unitary_X1 h hbi) (det_X1 hi) := by
      apply eq_of_cP_eq P
      rw [cP_hypSU, cP, Matrix.mul_assoc, hPv, hXP, ← Matrix.mul_assoc, ← hPv, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, Matrix.one_mul, X1_eq_stdDl]
    have hcardC := card_centralizer_le_U4 h hp2 hq P hP hi hbi
    rw [← hXeq] at hcardC
    have hMle : M ≤ Subgroup.centralizer
        {(QuotientGroup.mk X' : StatedProj (StatedSU 4 (p ^ f) K))} := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hM x hx
      rw [hαX] at h1
      calc x * QuotientGroup.mk X' =
          QuotientGroup.mk X' * x * (QuotientGroup.mk X')⁻¹ * QuotientGroup.mk X' := by rw [h1]
        _ = QuotientGroup.mk X' * x := by group
    have hcardM := (Subgroup.card_le_of_le hMle).trans hcardC
    have hq5 : 5 ≤ p ^ f := by
      have hp3 : 3 ≤ p := by have := h.prime.two_le; omega
      have : p ≤ p ^ f := Nat.le_self_pow (by have := h.one_le; omega) p
      omega
    obtain ⟨a, ha⟩ : ∃ a, a = Nat.card M := ⟨_, rfl⟩
    rw [← ha] at hcard hcardM
    generalize p ^ f = q at hcard hcardM hq5
    exact false_of_card_le_centralizer hq5 hcard hcardM

end StabU

end CFSG.ComponentClassification.CatFactsL4U4
