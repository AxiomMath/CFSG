module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6One5

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open Matrix CFSG CFSG.Open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6One
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.ClassicalEA
open CFSG.Blueprint.Chevalley CFSG.LinearGroups CFSG.SeitzReduction
  CFSG.SeitzReduction.TwistedE6Pilot
open CFSG.LieType.Chevalley

variable {f p : ℕ} {K : Type} [Field K] [Finite K]

private theorem trace_diag3_zeta (h2 : (2 : K) = 0) (ζ : Kˣ) :
    Matrix.trace ((diag3 ζ 1 1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      (ζ : K) + ((ζ⁻¹ : Kˣ) : K) := by
  rw [coe_diag3, Matrix.trace_diagonal, Fin.sum_univ_six]
  simp
  have h4 : (1 : K) + 1 + 1 + 1 = 0 := by
    have h : ((4 : ℕ) : K) = 0 := by
      have h2' : ((2 : ℕ) : K) = 0 := by simpa using h2
      rw [show (4 : ℕ) = 2 * 2 by norm_num, Nat.cast_mul, h2', zero_mul]
    rw [show (1 : K) + 1 + 1 + 1 = ((4 : ℕ) : K) by norm_num, h]
  linear_combination h4

private theorem trace_scalar_mul_diag3 (h2 : (2 : K) = 0) (c ζ : Kˣ) :
    Matrix.trace (((GeneralLinearGroup.scalar (Fin 6) c : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) *
      ((diag3 ζ 1 1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) =
      (c : K) * ((ζ : K) + ((ζ⁻¹ : Kˣ) : K)) := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
    Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul, trace_diag3_zeta h2]

private theorem add_inv_ne_zero (h2 : (2 : K) = 0) (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Kˣ}
    (hζ : orderOf ζ = p) : (ζ : K) + ((ζ⁻¹ : Kˣ) : K) ≠ 0 := by
  intro h0
  have h1 : (ζ : K) * (ζ : K) = 1 := by
    have h := congrArg (fun t : K => t * (ζ : K)) h0
    simp only [add_mul, zero_mul] at h
    have hζinv : ((ζ⁻¹ : Kˣ) : K) * (ζ : K) = 1 := by simp
    rw [hζinv] at h
    linear_combination h - (1 : K) * h2
  have hpow : ζ ^ 2 = 1 := Units.ext (by simpa [sq] using h1)
  have hdvd : orderOf ζ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hpow
  rw [hζ] at hdvd
  have hpeq : 2 = p := (Nat.Prime.dvd_iff_eq Nat.prime_two hp.ne_one).mp hdvd
  omega

private theorem commute_zSU_of_mem_centralizer (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p) (hζbar : h.bar (ζ : K) = ζ)
    {G : ↥(gramSU h (C6 K))}
    (hG : QuotientGroup.mk' (N6 h) G ∈
      Subgroup.centralizer ({zbar h p ζ hζ hζbar} : Set (primeFormP h (C6 K)))) :
    G * zSU h p ζ hζ hζbar = zSU h p ζ hζ hζbar * G := by
  have h2 : (2 : K) = 0 := by
    haveI := h.charP
    exact CharP.cast_eq_zero K 2
  set Z : ↥(gramSU h (C6 K)) := zSU h p ζ hζ hζbar with hZdef
  have hZ : (Z : GL (Fin 6) K) = diag3 ζ 1 1 := zSU_eq_diag3 h p hp ζ hζ hζbar
  have hcomm : QuotientGroup.mk' (N6 h) G * QuotientGroup.mk' (N6 h) Z =
      QuotientGroup.mk' (N6 h) Z * QuotientGroup.mk' (N6 h) G := by
    simpa [hZdef, zbar_eq_mk_zSU] using
      Subgroup.mem_centralizer_singleton_iff.mp hG
  have h1 : QuotientGroup.mk' (N6 h) (G * Z * G⁻¹ * Z⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  obtain ⟨c, -, -, hg⟩ := (mem_normOneScalars).mp ((QuotientGroup.eq_one_iff _).mp h1)
  have hco : ((G * Z * G⁻¹ * Z⁻¹ : ↥(gramSU h (C6 K))) : GL (Fin 6) K) =
      (G : GL (Fin 6) K) * (Z : GL (Fin 6) K) * (G : GL (Fin 6) K)⁻¹ *
        (Z : GL (Fin 6) K)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hco] at hg
  have hmat : (G : GL (Fin 6) K) * (Z : GL (Fin 6) K) * (G : GL (Fin 6) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin 6) c * (Z : GL (Fin 6) K) := by
    calc (G : GL (Fin 6) K) * (Z : GL (Fin 6) K) * (G : GL (Fin 6) K)⁻¹ =
        ((G : GL (Fin 6) K) * (Z : GL (Fin 6) K) * (G : GL (Fin 6) K)⁻¹ *
          (Z : GL (Fin 6) K)⁻¹) * (Z : GL (Fin 6) K) := by group
      _ = GeneralLinearGroup.scalar (Fin 6) c * (Z : GL (Fin 6) K) := by rw [hg]
  have htr := congrArg (fun g : GL (Fin 6) K => Matrix.trace
    ((g : Matrix (Fin 6) (Fin 6) K))) hmat
  simp only [Units.val_mul, Units.val_inv_eq_inv_val] at htr
  rw [hZ] at htr
  rw [Matrix.trace_units_conj (G : GL (Fin 6) K) ((diag3 ζ 1 1 :
      GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K), trace_diag3_zeta h2 ζ,
    trace_scalar_mul_diag3 h2 c ζ] at htr
  have hc1 : (c : K) = 1 := by
    have hne : (ζ : K) + ((ζ⁻¹ : Kˣ) : K) ≠ 0 := add_inv_ne_zero h2 hp hp2 hζ
    have : (1 : K) * ((ζ : K) + ((ζ⁻¹ : Kˣ) : K)) =
        (c : K) * ((ζ : K) + ((ζ⁻¹ : Kˣ) : K)) := by rw [one_mul]; exact htr
    exact mul_right_cancel₀ hne this.symm
  have hc1' : c = 1 := Units.ext hc1
  rw [hc1'] at hmat
  simp only [map_one, one_mul] at hmat
  apply Subtype.ext
  calc (G : GL (Fin 6) K) * (Z : GL (Fin 6) K) =
      ((G : GL (Fin 6) K) * (Z : GL (Fin 6) K) * (G : GL (Fin 6) K)⁻¹) *
        (G : GL (Fin 6) K) := by group
    _ = (Z : GL (Fin 6) K) * (G : GL (Fin 6) K) := by rw [hmat]

private theorem maps_U2_of_commute_diag3 (h2 : (2 : K) = 0) {G : GL (Fin 6) K} {a : Kˣ}
    (ha1 : (a : K) ≠ 1) (hainv1 : ((a⁻¹ : Kˣ) : K) ≠ 1)
    (hG : G * diag3 a 1 1 = diag3 a 1 1 * G) {v : Fin 6 → K} (hv : v ∈ U2 K) :
    toLinLE K G v ∈ U2 K := by
  classical
  obtain ⟨x, y, rfl⟩ := (Submodule.mem_span_pair).mp hv
  have hmat : (G : Matrix (Fin 6) (Fin 6) K) *
      ((diag3 a 1 1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      ((diag3 a 1 1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        (G : Matrix (Fin 6) (Fin 6) K) := by
    simpa using congrArg (fun M : GL (Fin 6) K => (M : Matrix (Fin 6) (Fin 6) K)) hG
  have hentry : ∀ i j : Fin 6, (G : Matrix (Fin 6) (Fin 6) K) i j *
      (![(a : K), 1, 1, 1, 1, ((a⁻¹ : Kˣ) : K)] : Fin 6 → K) j =
      (![(a : K), 1, 1, 1, 1, ((a⁻¹ : Kˣ) : K)] : Fin 6 → K) i *
        (G : Matrix (Fin 6) (Fin 6) K) i j := by
    intro i j
    have h := congrFun (congrFun hmat i) j
    simpa [Matrix.mul_apply, Matrix.diagonal, coe_diag3, Fin.sum_univ_six] using h
  have hcoe : ∀ i : Fin 6, i ≠ 0 → i ≠ 5 → (G : Matrix (Fin 6) (Fin 6) K) i 0 = 0 ∧
      (G : Matrix (Fin 6) (Fin 6) K) i 5 = 0 := by
    intro i hi0 hi5
    have hi1 : (![(a : K), 1, 1, 1, 1, ((a⁻¹ : Kˣ) : K)] : Fin 6 → K) i = 1 := by
      fin_cases i <;> simp_all
    constructor
    · have h := hentry i 0
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hi1] at h
      have h' : (G : Matrix (Fin 6) (Fin 6) K) i 0 * ((a : K) - 1) = 0 := by
        linear_combination h
      exact (mul_eq_zero.mp h').resolve_right (sub_ne_zero.mpr ha1)
    · have h := hentry i 5
      have hi5' : (![(a : K), 1, 1, 1, 1, ((a⁻¹ : Kˣ) : K)] : Fin 6 → K) 5 =
          ((a⁻¹ : Kˣ) : K) := by simp
      simp only [hi1, hi5'] at h
      have h' : (G : Matrix (Fin 6) (Fin 6) K) i 5 * (((a⁻¹ : Kˣ) : K) - 1) = 0 := by
        linear_combination h
      exact (mul_eq_zero.mp h').resolve_right (sub_ne_zero.mpr hainv1)
  have hzero : ∀ i : Fin 6, i ≠ 0 → i ≠ 5 →
      toLinLE K G (x • e0 K + y • e5 K) i = 0 := by
    intro i hi0 hi5
    have hc := hcoe i hi0 hi5
    rw [toLinLE_apply, Matrix.mulVec, dotProduct]
    have hsum : ∑ j : Fin 6, (G : Matrix (Fin 6) (Fin 6) K) i j *
        (x • e0 K + y • e5 K) j =
        (G : Matrix (Fin 6) (Fin 6) K) i 0 * x +
          (G : Matrix (Fin 6) (Fin 6) K) i 5 * y := by
      rw [Fin.sum_univ_six]
      simp [e0, e5, Pi.single, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_six]
    rw [hsum, hc.1, hc.2, zero_mul, zero_mul, add_zero]
  have hsum2 : toLinLE K G (x • e0 K + y • e5 K) =
      (toLinLE K G (x • e0 K + y • e5 K)) 0 • e0 K +
        (toLinLE K G (x • e0 K + y • e5 K)) 5 • e5 K := by
    ext i
    by_cases hi0 : i = 0
    · subst hi0; simp [e0, e5, Pi.single]
    · by_cases hi5 : i = 5
      · subst hi5; simp [e0, e5, Pi.single]
      · rw [hzero i hi0 hi5]
        simp [e0, e5, Pi.single, hi0, hi5]
  rw [hsum2]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem QSU_conj_mem (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p] (hp : p.Prime)
    (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p) (hζbar : h.bar (ζ : K) = ζ)
    {G : ↥(gramSU h (C6 K))}
    (hG : QuotientGroup.mk' (N6 h) G ∈
      Subgroup.centralizer ({zbar h p ζ hζ hζbar} : Set (primeFormP h (C6 K))))
    {x : ↥(gramSU h (C6 K))} (hx : x ∈ QSU h) :
    G * x * G⁻¹ ∈ QSU h := by
  have h2 : (2 : K) = 0 := by
    haveI := h.charP
    exact CharP.cast_eq_zero K 2
  have hcomm : G * zSU h p ζ hζ hζbar = zSU h p ζ hζ hζbar * G :=
    commute_zSU_of_mem_centralizer h p hp hp2 ζ hζ hζbar hG
  have hmat : (G : GL (Fin 6) K) * diag3 ζ 1 1 = diag3 ζ 1 1 * (G : GL (Fin 6) K) := by
    have h' := congrArg (fun y : ↥(gramSU h (C6 K)) => (y : GL (Fin 6) K)) hcomm
    simpa [zSU_eq_diag3 h p hp ζ hζ hζbar] using h'
  have hζu : ζ ≠ 1 := by
    intro h1
    refine hp.ne_one ?_
    rw [← hζ]
    exact orderOf_eq_one_iff.mpr h1
  have hζ1 : (ζ : K) ≠ 1 := fun h1 => hζu (Units.ext h1)
  have hζinv1 : ((ζ⁻¹ : Kˣ) : K) ≠ 1 := by
    intro h1
    exact (inv_ne_one.mpr hζu) (Units.ext h1)
  have hGU : ∀ v ∈ U2 K, toLinLE K (G : GL (Fin 6) K) v ∈ U2 K :=
    fun v hv => maps_U2_of_commute_diag3 h2 hζ1 hζinv1 hmat hv
  have hmatinv : (G : GL (Fin 6) K)⁻¹ * diag3 ζ 1 1 =
      diag3 ζ 1 1 * (G : GL (Fin 6) K)⁻¹ := by
    have h1 : (G : GL (Fin 6) K)⁻¹ * diag3 ζ 1 1 * (G : GL (Fin 6) K) = diag3 ζ 1 1 := by
      rw [mul_assoc, ← hmat, ← mul_assoc, inv_mul_cancel, one_mul]
    have h2' := congrArg (fun M => M * (G : GL (Fin 6) K)⁻¹) h1
    simpa [mul_assoc] using h2'
  have hGiU : ∀ v ∈ U2 K, ((toLinLE K (G : GL (Fin 6) K))⁻¹) v ∈ U2 K := by
    intro v hv
    have h' := maps_U2_of_commute_diag3 h2 hζ1 hζinv1 hmatinv hv
    simpa using h'
  intro v hv
  have hcoe : ((G * x * G⁻¹ : ↥(gramSU h (C6 K))) : GL (Fin 6) K) =
      (G : GL (Fin 6) K) * (x : GL (Fin 6) K) * (G : GL (Fin 6) K)⁻¹ := by
    simp
  rw [hcoe, map_mul, map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    hx _ (hGiU v hv)]
  rw [← LinearEquiv.mul_apply, mul_inv_cancel]
  rfl

theorem Qbar_conj_mem (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p] (hp : p.Prime)
    (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p) (hζbar : h.bar (ζ : K) = ζ)
    {g x : primeFormP h (C6 K)}
    (hg : g ∈ Subgroup.centralizer ({zbar h p ζ hζ hζbar} : Set (primeFormP h (C6 K))))
    (hx : x ∈ Qbar h p hp hp2 ζ hζ hζbar) :
    g * x * g⁻¹ ∈ Qbar h p hp hp2 ζ hζ hζbar := by
  obtain ⟨x', rfl⟩ := hx
  obtain ⟨G, rfl⟩ := QuotientGroup.mk'_surjective (N6 h) g
  have hG : QuotientGroup.mk' (N6 h) G ∈
      Subgroup.centralizer ({zbar h p ζ hζ hζbar} : Set (primeFormP h (C6 K))) := hg
  refine ⟨⟨G * (x' : ↥(gramSU h (C6 K))) * G⁻¹, ?_⟩, ?_⟩
  · exact QSU_conj_mem h p hp hp2 ζ hζ hζbar hG x'.2
  · change (QuotientGroup.mk' (N6 h)) (G * (x' : ↥(gramSU h (C6 K))) * G⁻¹) =
      (QuotientGroup.mk' (N6 h)) G * (QuotientGroup.mk' (N6 h)) (x' : ↥(gramSU h (C6 K))) *
        ((QuotientGroup.mk' (N6 h)) G)⁻¹
    rw [map_mul, map_mul, map_inv]

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
