module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4HBlocks

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace StabU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] noncomputable def toGL (M : Matrix (Fin 4) (Fin 4) K) (hd : M.det = 1) : GL (Fin 4) K :=
  GeneralLinearGroup.mkOfDetNeZero M (by rw [hd]; exact one_ne_zero)

theorem coe_toGL (M : Matrix (Fin 4) (Fin 4) K) (hd : M.det = 1) :
    (toGL M hd : Matrix (Fin 4) (Fin 4) K) = M :=
  GeneralLinearGroup.val_mkOfDetNeZero M _

theorem unitary_mul {M N : Matrix (Fin 4) (Fin 4) K} (hM : uStar h M * stdG * M = stdG)
    (hN : uStar h N * stdG * N = stdG) : uStar h (M * N) * stdG * (M * N) = stdG := by
  rw [uStar_mul]
  calc uStar h N * uStar h M * stdG * (M * N) = uStar h N * (uStar h M * stdG * M) * N := by
        simp only [Matrix.mul_assoc]
    _ = stdG := by rw [hM, hN]

theorem uStar_inv_mul (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG) :
    uStar h (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * stdG * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
  have hPi : uStar h (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *
      uStar h (P : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← uStar_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, uStar_one]
  rw [← hP, ← Matrix.mul_assoc, hPi, Matrix.one_mul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one]

theorem conj_mem_unitarySU (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
      stdG) {M : GL (Fin 4) K}
    (hM : uStar h (M : Matrix (Fin 4) (Fin 4) K) * stdG * (M : Matrix (Fin 4) (Fin 4) K) = stdG)
    (hd : (M : Matrix (Fin 4) (Fin 4) K).det = 1) : P * M * P⁻¹ ∈ unitarySU p f K 4 := by
  rw [mem_unitarySU_iff h]
  constructor
  · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hd, mul_one, ← det_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, det_one]
  · change uStar h _ * _ = 1
    rw [Units.val_mul, Units.val_mul, uStar_mul, uStar_mul]
    calc uStar h (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *
          (uStar h (M : Matrix (Fin 4) (Fin 4) K) * uStar h (P : Matrix (Fin 4) (Fin 4) K)) *
          ((P : Matrix (Fin 4) (Fin 4) K) * M * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) =
        uStar h (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *
          (uStar h (M : Matrix (Fin 4) (Fin 4) K) * (uStar h (P : Matrix (Fin 4) (Fin 4) K) * P) *
            M) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hP, hM, uStar_inv_mul h P hP]

@[expose] noncomputable def hypSU (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
      stdG) (M : Matrix (Fin 4) (Fin 4) K)
    (hM : uStar h M * stdG * M = stdG) (hd : M.det = 1) : unitarySU p f K 4 :=
  ⟨P * toGL M hd * P⁻¹, conj_mem_unitarySU h P hP (by rw [coe_toGL]; exact hM) (by
    rw [coe_toGL]; exact hd)⟩

theorem val_hypSU (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
      stdG)
    (M : Matrix (Fin 4) (Fin 4) K) (hM : uStar h M * stdG * M = stdG) (hd : M.det = 1) :
    (((hypSU h P hP M hM hd : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (P : Matrix (Fin 4) (Fin 4) K) * M * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
  change ((P * toGL M hd * P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = _
  rw [Units.val_mul, Units.val_mul, coe_toGL]

theorem ext_val {g g' : unitarySU p f K 4}
    (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = ((g' : GL (Fin 4) K) : Matrix _ _ K)) :
    g = g' :=
  Subtype.ext (Units.ext hg)

theorem inv_mul_val_mul (P : GL (Fin 4) K) (M : Matrix (Fin 4) (Fin 4) K) :
    (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *
        ((P : Matrix (Fin 4) (Fin 4) K) * M * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) * P = M := by
  have h1 : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * P = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *
        ((P : Matrix (Fin 4) (Fin 4) K) * M * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) * P =
      ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * P) * M *
        ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * P) := by simp only [Matrix.mul_assoc]
    _ = M := by rw [h1, Matrix.one_mul, Matrix.mul_one]

abbrev scal (p f : ℕ) (K : Type) [Field K] : Subgroup (unitarySU p f K 4) :=
  (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (p ^ f) K)

theorem val_of_mem_scal {z : unitarySU p f K 4} (hz : z ∈ scal p f K) :
    ∃ c : Kˣ, ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (c : K) • 1 := by
  have hz' : (z : GL (Fin 4) K) ∈ StatedScalars (Fin 4) K := hz
  obtain ⟨c, hc⟩ := hz'
  refine ⟨c, ?_⟩
  rw [← hc, GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]
  rfl

theorem mem_center_of_mem_scal {z : unitarySU p f K 4} (hz : z ∈ scal p f K) :
    z ∈ Subgroup.center (unitarySU p f K 4) := by
  have hz' : (z : GL (Fin 4) K) ∈ StatedScalars (Fin 4) K := hz
  obtain ⟨c, hc⟩ := hz'
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc]
  have hcen : GeneralLinearGroup.scalar (Fin 4) c ∈ Subgroup.center (GL (Fin 4) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  exact Subgroup.mem_center_iff.mp hcen _

include h in
theorem pow_four_eq_one_of_mem_scal {z : unitarySU p f K 4} (hz : z ∈ scal p f K) : z ^ 4 = 1 := by
  obtain ⟨c, hc⟩ := val_of_mem_scal hz
  have hdet := ((mem_unitarySU_iff h).1 z.2).1
  rw [hc, det_smul, det_one, mul_one, Fintype.card_fin] at hdet
  apply ext_val
  rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hc, smul_pow, one_pow, hdet, one_smul]
  rfl

theorem eq_one_of_pow_odd {G : Type*} [Monoid G] {z : G} {n : ℕ} (hn : Odd n) (h1 : z ^ n = 1)
    (h4 : z ^ 4 = 1) : z = 1 := by
  have hg : Nat.gcd n 4 = 1 := by
    obtain ⟨t, rfl⟩ := hn
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right 2 (by rw [Nat.coprime_two_right]; exact odd_two_mul_add_one t)
  have := pow_gcd_eq_one.2 ⟨h1, h4⟩
  rwa [hg, pow_one] at this

theorem pow_eq_one_of_conj_eq {G : Type*} [Group G] {x y z : G} (hz : z ∈ Subgroup.center G)
    (hxy : x * y * x⁻¹ = z * y) {n : ℕ} (hy : y ^ n = 1) : z ^ n = 1 := by
  have hcomm : Commute z y := ((Subgroup.mem_center_iff.mp hz) y).symm
  have h1 : (x * y * x⁻¹) ^ n = 1 := by rw [conj_pow, hy, mul_one, mul_inv_cancel]
  rwa [hxy, hcomm.mul_pow, hy, mul_one] at h1

theorem pow_eq_one_of_conj_eq' {G : Type*} [Group G] {u Y z : G} (hz : z ∈ Subgroup.center G)
    (huY : u * Y * u⁻¹ = z * Y) {n : ℕ} (hu : u ^ n = 1) : z ^ n = 1 := by
  have hk : ∀ k : ℕ, u ^ k * Y * (u ^ k)⁻¹ = z ^ k * Y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc u ^ (k + 1) * Y * (u ^ (k + 1))⁻¹ = u * (u ^ k * Y * (u ^ k)⁻¹) * u⁻¹ := by group
        _ = u * (z ^ k * Y) * u⁻¹ := by rw [ih]
        _ = z ^ k * (u * Y * u⁻¹) := by
            have : Commute (z ^ k) u := (((Subgroup.mem_center_iff.mp
              (Subgroup.pow_mem _ hz k)) u)).symm
            calc u * (z ^ k * Y) * u⁻¹ = (u * z ^ k) * Y * u⁻¹ := by group
              _ = (z ^ k * u) * Y * u⁻¹ := by rw [this.eq]
              _ = z ^ k * (u * Y * u⁻¹) := by group
        _ = z ^ (k + 1) * Y := by rw [huY, pow_succ]; group
  have := hk n
  rw [hu, one_mul, inv_one, mul_one] at this
  exact (mul_eq_right.1 this.symm)

@[expose] noncomputable def uU (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
      stdG) (c : K) : unitarySU p f K 4 :=
  hypSU h P hP (U12 h c) (unitary_U12 h c) (det_U12 h c)

@[expose] noncomputable def uL (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
      stdG) (c : K) : unitarySU p f K 4 :=
  hypSU h P hP (U21 h c) (unitary_U21 h c) (det_U21 h c)

@[expose] def HasUnipU (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG) (μ : K)
    (J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))) : Prop :=
  (QuotientGroup.mk (uU h P hP 1) : StatedProj (StatedSU 4 (p ^ f) K)) ∈ J' ∧
    (QuotientGroup.mk (uL h P hP 1) : StatedProj (StatedSU 4 (p ^ f) K)) ∈ J' ∧
    (QuotientGroup.mk (uU h P hP μ) : StatedProj (StatedSU 4 (p ^ f) K)) ∈ J'

theorem trace_conj (P : GL (Fin 4) K) (M : Matrix (Fin 4) (Fin 4) K) :
    ((P : Matrix (Fin 4) (Fin 4) K) * M * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)).trace = M.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul]

include h in
theorem uU_pow_char (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
      stdG) (c : K) : uU h P hP c ^ p = 1 := by
  have : CharP K p := h.charP
  have hT : toGL (U12 h c) (det_U12 h c) ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, coe_toGL, U12_pow, CharP.cast_eq_zero, zero_mul, U12_zero,
      Units.val_one]
  apply Subtype.ext
  change (P * toGL (U12 h c) (det_U12 h c) * P⁻¹) ^ p = 1
  rw [conj_pow, hT, mul_one, mul_inv_cancel]

include h in
theorem uL_pow_char (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
      stdG) (c : K) : uL h P hP c ^ p = 1 := by
  have : CharP K p := h.charP
  have hT : toGL (U21 h c) (det_U21 h c) ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, coe_toGL, U21_pow, CharP.cast_eq_zero, zero_mul, U21_zero,
      Units.val_one]
  apply Subtype.ext
  change (P * toGL (U21 h c) (det_U21 h c) * P⁻¹) ^ p = 1
  rw [conj_pow, hT, mul_one, mul_inv_cancel]

theorem eq_of_eq_on_generator {μ : Kˣ} (hμ : ∀ x : Kˣ, x ∈ Subgroup.zpowers μ) (φ ψ : K →+* K)
    (h1 : φ μ = ψ μ) (c : K) : φ c = ψ c := by
  by_cases hc : c = 0
  · rw [hc, map_zero, map_zero]
  · have h2 := (MonoidHom.eq_iff_eq_on_generator hμ (Units.map (φ : K →* K))
      (Units.map (ψ : K →* K))).2 (Units.ext h1)
    have h3 := congrArg (fun F : Kˣ →* Kˣ => ((F (Units.mk0 c hc) : Kˣ) : K)) h2
    simpa using h3

theorem bar_ne_of_generator {μ : Kˣ} (hμ : ∀ x : Kˣ, x ∈ Subgroup.zpowers μ) :
    h.bar (μ : K) ≠ μ := by
  intro h1
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  exact hc (eq_of_eq_on_generator hμ h.bar (RingHom.id K) h1 c)

theorem conj_eq_of_fix (h4 : (4 : K) ≠ 0) {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    {A : GL (Fin 4) K} {φ : K ≃+* K}
    {hA : ∀ g : unitarySU p f K 4, A * glAut φ (g : GL (Fin 4) K) * A⁻¹ ∈ unitarySU p f K 4}
    (hlift : ∀ g : unitarySU p f K 4,
      (QuotientGroup.mk (ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom A φ hA g) :
        StatedProj (StatedSU 4 (p ^ f) K)) = α (QuotientGroup.mk g))
    {g : unitarySU p f K 4} (hg : α (QuotientGroup.mk g) = QuotientGroup.mk g)
    (htr : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace = 4) :
    A * glAut φ (g : GL (Fin 4) K) * A⁻¹ = g := by
  set u := ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom A φ hA g with hu
  have h1 : (QuotientGroup.mk u : StatedProj (StatedSU 4 (p ^ f) K)) = QuotientGroup.mk g := by
    rw [hlift, hg]
  rw [QuotientGroup.eq] at h1
  obtain ⟨c, hc⟩ := val_of_mem_scal h1
  have hu' : ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((A * glAut φ (g : GL (Fin 4) K) * A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [hu, ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom]
  have hgm : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((A * glAut φ (g : GL (Fin 4) K) * A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((c : K) • 1) := by
    rw [← hu', ← hc, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel_left]
  have htr' : ((A * glAut φ (g : GL (Fin 4) K) * A⁻¹ : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K).trace = 4 := by
    rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mul, coe_glAut]
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply]
    rw [← map_sum]
    change φ (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace) = 4
    rw [htr, map_ofNat]
  have hc1 : (c : K) = 1 := by
    have := congrArg Matrix.trace hgm
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, htr', htr, smul_eq_mul] at this
    have h5 : (4 : K) * (1 - c) = 0 := by linear_combination this
    rcases mul_eq_zero.1 h5 with h6 | h6
    · exact absurd h6 h4
    · linear_combination -h6
  rw [hc1, one_smul, Matrix.mul_one] at hgm
  exact (Units.ext hgm).symm

@[expose] noncomputable def cP (P : GL (Fin 4) K) (g : unitarySU p f K 4) :
    Matrix (Fin 4) (Fin 4) K :=
  (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * P

theorem cP_mul (P : GL (Fin 4) K) (g g' : unitarySU p f K 4) :
    cP P (g * g') = cP P g * cP P g' := by
  have h1 : (P : Matrix (Fin 4) (Fin 4) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [cP, cP, cP, Subgroup.coe_mul, Units.val_mul]
  calc (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((g' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) * P =
      (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((P : Matrix (Fin 4) (Fin 4) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) *
        ((g' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * P := by
        rw [h1, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem cP_hypSU (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    (M : Matrix (Fin 4) (Fin 4) K) (hM : uStar h M * stdG * M = stdG) (hd : M.det = 1) :
    cP P (hypSU h P hP M hM hd) = M := by
  rw [cP, val_hypSU, inv_mul_val_mul]

theorem eq_of_cP_eq (P : GL (Fin 4) K) {g g' : unitarySU p f K 4} (hg : cP P g = cP P g') :
    g = g' := by
  apply ext_val
  have h1 : (P : Matrix (Fin 4) (Fin 4) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e := congrArg
    (fun M => (P : Matrix (Fin 4) (Fin 4) K) * M * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) hg
  simp only [cP, ← Matrix.mul_assoc, h1, Matrix.one_mul] at e
  simpa only [Matrix.mul_assoc, h1, Matrix.mul_one] using e

theorem unitary_cP (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    (g : unitarySU p f K 4) : uStar h (cP P g) * stdG * cP P g = stdG := by
  have hg : uStar h ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := ((mem_unitarySU_iff h).1 g.2).2
  have hPi := uStar_inv_mul h P hP
  rw [cP, uStar_mul, uStar_mul]
  calc uStar h (P : Matrix (Fin 4) (Fin 4) K) *
        (uStar h ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          uStar h (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) * stdG *
        ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (P : Matrix (Fin 4) (Fin 4) K)) =
      uStar h (P : Matrix (Fin 4) (Fin 4) K) *
        (uStar h ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (uStar h (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * stdG * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) *
          ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) * (P : Matrix (Fin 4) (Fin 4) K) := by
          simp only [Matrix.mul_assoc]
    _ = stdG := by rw [hPi, Matrix.mul_one, hg, Matrix.mul_one, hP]

include h in
theorem comm_of_mk_comm (hp2 : p ≠ 2) {g u : unitarySU p f K 4} (hup : u ^ p = 1)
    (hc : (QuotientGroup.mk g : StatedProj (StatedSU 4 (p ^ f) K)) * QuotientGroup.mk u =
      QuotientGroup.mk u * QuotientGroup.mk g) : g * u = u * g := by
  have h1 : (QuotientGroup.mk (g * u) : StatedProj (StatedSU 4 (p ^ f) K)) =
      QuotientGroup.mk (u * g) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hc]
  rw [QuotientGroup.eq] at h1
  have hzc := mem_center_of_mem_scal h1
  have hconj : g⁻¹ * u * g⁻¹⁻¹ = ((g * u)⁻¹ * (u * g)) * u := by
    have hc' : ((g * u)⁻¹ * (u * g)) * u = u * ((g * u)⁻¹ * (u * g)) :=
      (Subgroup.mem_center_iff.mp hzc u).symm
    rw [hc', inv_inv]
    group
  have hzp := pow_eq_one_of_conj_eq hzc hconj hup
  have hz1 := eq_one_of_pow_odd (h.prime.odd_of_ne_two hp2) hzp (pow_four_eq_one_of_mem_scal h h1)
  exact inv_mul_eq_one.1 hz1

include h in
theorem comm_of_mk_comm' (hp2 : p ≠ 2) {u Y : unitarySU p f K 4} (hup : u ^ p = 1)
    (hc : (QuotientGroup.mk u : StatedProj (StatedSU 4 (p ^ f) K)) * QuotientGroup.mk Y =
      QuotientGroup.mk Y * QuotientGroup.mk u) : u * Y = Y * u := by
  have h1 : (QuotientGroup.mk (u * Y) : StatedProj (StatedSU 4 (p ^ f) K)) =
      QuotientGroup.mk (Y * u) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hc]
  rw [QuotientGroup.eq] at h1
  have hzc := mem_center_of_mem_scal h1
  have hconj : u⁻¹ * Y * u⁻¹⁻¹ = ((u * Y)⁻¹ * (Y * u)) * Y := by
    have hc' : ((u * Y)⁻¹ * (Y * u)) * Y = Y * ((u * Y)⁻¹ * (Y * u)) :=
      (Subgroup.mem_center_iff.mp hzc Y).symm
    rw [hc', inv_inv]
    group
  have hzp := pow_eq_one_of_conj_eq' hzc hconj (by rw [inv_pow, hup, inv_one])
  have hz1 := eq_one_of_pow_odd (h.prime.odd_of_ne_two hp2) hzp (pow_four_eq_one_of_mem_scal h h1)
  exact inv_mul_eq_one.1 hz1

theorem comm_bar (φ : K →+* K) (c : K) : φ (h.bar c) = h.bar (φ c) := by
  rw [UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply, map_pow]

theorem map_U12_equiv (φ : K ≃+* K) (c : K) : (U12 h c).map φ = U12 h (φ c) :=
  map_U12 h (φ : K →+* K) (comm_bar h _) c

theorem map_U21_equiv (φ : K ≃+* K) (c : K) : (U21 h c).map φ = U21 h (φ c) :=
  map_U21 h (φ : K →+* K) (comm_bar h _) c

theorem uStar_map_equiv (φ : K ≃+* K) (M : Matrix (Fin 4) (Fin 4) K) :
    uStar h (M.map φ) = (uStar h M).map φ :=
  uStar_map h (φ : K →+* K) (comm_bar h _) M

include h in
theorem inner_or_fixed (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {μ : Kˣ} (hμ : ∀ x : Kˣ, x ∈ Subgroup.zpowers μ)
    (α : MulAut (StatedProj (StatedSU 4 (p ^ f) K)))
    (h1 : α (QuotientGroup.mk (uU h P hP 1)) = QuotientGroup.mk (uU h P hP 1))
    (h2 : α (QuotientGroup.mk (uL h P hP 1)) = QuotientGroup.mk (uL h P hP 1))
    (h3 : α (QuotientGroup.mk (uU h P hP μ)) = QuotientGroup.mk (uU h P hP μ)) :
    (∃ z, α = MulAut.conj z) ∨
      ∃ g : unitarySU p f K 4, α (QuotientGroup.mk g) = QuotientGroup.mk g ∧
        ∃ β γ : K, β ≠ 0 ∧ cP P g = gfix β γ := by
  classical
  have : Finite K := h.finite
  set θ : unitarySU p f K 4 →* StatedProj (StatedSU 4 (p ^ f) K) :=
    QuotientGroup.mk' (scal p f K) with hθdef
  have hθ : Function.Surjective θ := QuotientGroup.mk'_surjective _
  have hker : θ.ker ≤ Subgroup.center (unitarySU p f K 4) := by
    rw [hθdef, QuotientGroup.ker_mk']
    intro z hz
    exact mem_center_of_mem_scal hz
  have hq5 : 5 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by have := h.prime.two_le; omega
    have : p ≤ p ^ f := Nat.le_self_pow (by have := h.one_le; omega) p
    omega
  obtain ⟨A, φ, hA, hAu, hlift, -⟩ :=
    ClassicalInvolution.ModelFacts.UnitaryAut.exists_lift_unitarySU h hp2 hq5 (d := 4)
      (by norm_num) θ hθ hker α
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2K h2K
  have hlift' : ∀ g : unitarySU p f K 4,
      (QuotientGroup.mk (ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom A φ hA g) :
        StatedProj (StatedSU 4 (p ^ f) K)) = α (QuotientGroup.mk g) := hlift
  obtain ⟨A', hA'⟩ : ∃ X : GL (Fin 4) K, X = P⁻¹ * A * glAut φ P := ⟨_, rfl⟩
  have key : ∀ (U : Matrix (Fin 4) (Fin 4) K) (hU : uStar h U * stdG * U = stdG)
      (hd : U.det = 1), U.trace = 4 → α (QuotientGroup.mk (hypSU h P hP U hU hd)) =
        QuotientGroup.mk (hypSU h P hP U hU hd) →
      (A' : Matrix (Fin 4) (Fin 4) K) * U.map φ = U * A' := by
    intro U hU hd htr hfx
    have e1 := conj_eq_of_fix h4 hlift' hfx (by rw [val_hypSU, trace_conj]; exact htr)
    have e3 : ((hypSU h P hP U hU hd : unitarySU p f K 4) : GL (Fin 4) K) =
        P * toGL U hd * P⁻¹ := rfl
    rw [e3, map_mul, map_mul, map_inv] at e1
    have e2 : A' * glAut φ (toGL U hd) * A'⁻¹ = toGL U hd := by
      rw [hA']
      calc P⁻¹ * A * glAut φ P * glAut φ (toGL U hd) * (P⁻¹ * A * glAut φ P)⁻¹ =
          P⁻¹ * (A * (glAut φ P * glAut φ (toGL U hd) * (glAut φ P)⁻¹) * A⁻¹) * P := by group
        _ = P⁻¹ * (P * toGL U hd * P⁻¹) * P := by rw [e1]
        _ = toGL U hd := by group
    have e4 : A' * glAut φ (toGL U hd) = toGL U hd * A' := by
      calc A' * glAut φ (toGL U hd) = (A' * glAut φ (toGL U hd) * A'⁻¹) * A' := by group
        _ = toGL U hd * A' := by rw [e2]
    have e5 := congrArg (fun X : GL (Fin 4) K => (X : Matrix (Fin 4) (Fin 4) K)) e4
    simp only [Units.val_mul, coe_glAut, coe_toGL] at e5
    exact e5
  have hE1 := key (U12 h 1) (unitary_U12 h 1) (det_U12 h 1) (trace_U12 h 1) h1
  have hE2 := key (U21 h 1) (unitary_U21 h 1) (det_U21 h 1) (trace_U21 h 1) h2
  have hE3 := key (U12 h μ) (unitary_U12 h μ) (det_U12 h μ) (trace_U12 h μ) h3
  rw [map_U12_equiv, map_one] at hE1
  rw [map_U21_equiv, map_one] at hE2
  rw [map_U12_equiv] at hE3
  obtain ⟨M, hM⟩ : ∃ X : Matrix (Fin 4) (Fin 4) K, X = (A' : Matrix (Fin 4) (Fin 4) K) :=
    ⟨_, rfl⟩
  rw [← hM] at hE1 hE2 hE3
  have hblk := eq_blk_of_comm h hE1 hE2
  rw [hblk] at hE3
  obtain ⟨r1, r2, r3, r4⟩ := blk_rel h hE3
  have hMu : uStar h M * stdG * M = stdG := by
    have hAu' : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 := hAu
    have hPi := uStar_inv_mul h P hP
    rw [hM, hA', Units.val_mul, Units.val_mul, coe_glAut, uStar_mul, uStar_mul]
    calc uStar h ((P : Matrix (Fin 4) (Fin 4) K).map φ) *
          (uStar h (A : Matrix (Fin 4) (Fin 4) K) * uStar h (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) *
          stdG * ((↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) *
            (P : Matrix (Fin 4) (Fin 4) K).map φ) =
        uStar h ((P : Matrix (Fin 4) (Fin 4) K).map φ) *
          (uStar h (A : Matrix (Fin 4) (Fin 4) K) * ((uStar h (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *
            stdG * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) * (A : Matrix (Fin 4) (Fin 4) K))) *
          (P : Matrix (Fin 4) (Fin 4) K).map φ := by simp only [Matrix.mul_assoc]
      _ = uStar h ((P : Matrix (Fin 4) (Fin 4) K).map φ) *
          (P : Matrix (Fin 4) (Fin 4) K).map φ := by
          rw [hPi, Matrix.one_mul, hAu', Matrix.mul_one]
      _ = stdG := by
          rw [uStar_map_equiv, ← Matrix.map_mul, hP]
          exact stdG_map (φ : K →+* K)
  rw [hblk] at hMu
  have hun := blk_unitary h hMu
  have hμb := bar_ne_of_generator h hμ
  by_cases hφμ : φ (μ : K) = μ
  ·
    left
    have hφ1 : φ = RingEquiv.refl K := RingEquiv.ext fun c =>
      eq_of_eq_on_generator hμ (φ : K →+* K) (RingHom.id K) hφμ c
    have hb : M 0 3 = 0 := by
      rw [hφμ] at r2
      rcases mul_eq_zero.1 r2 with h0 | h0
      · exact h0
      · exact absurd (sub_eq_zero.1 h0) hμb
    have hf : M 2 1 = 0 := by
      rw [hφμ] at r3
      rcases mul_eq_zero.1 r3 with h0 | h0
      · exact h0
      · exact absurd (sub_eq_zero.1 h0).symm hμb
    rw [hb, hf, zero_mul, zero_add] at hun
    have hdetM : M.det = M 0 0 ^ 2 * M 2 2 ^ 2 := by
      conv_lhs => rw [hblk, hb, hf]
      exact det_blk _ _
    subst hφ1
    have hgl1 : ∀ X : GL (Fin 4) K, glAut (RingEquiv.refl K) X = X := fun X => by
      change glAut 1 X = X
      rw [map_one]
      rfl
    have hdetA : GeneralLinearGroup.det A' = GeneralLinearGroup.det A := by
      rw [hA', hgl1, map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
    have hq1 : p ^ f + 1 = 2 * ((p ^ f + 1) / 2) := by omega
    set m := (p ^ f + 1) / 2 with hm
    have hmodd : Odd m := ⟨(p ^ f - 1) / 4, by omega⟩
    set z := GeneralLinearGroup.det A with hz
    have hzval : (z : K) = M 0 0 ^ 2 * M 2 2 ^ 2 := by
      rw [← hdetM, hM, ← GeneralLinearGroup.val_det_apply, hdetA]
    have hun' : M 0 0 * h.bar (M 2 2) = 1 := by
      have := congrArg h.bar hun
      rwa [map_mul, h.bar_bar, map_one] at this
    have hz1 : z ^ m = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hzval, Units.val_one]
      have e : (M 0 0 ^ 2 * M 2 2 ^ 2) ^ m = (M 0 0 * M 2 2) * (M 0 0 * M 2 2) ^ p ^ f := by
        rw [← pow_succ', hq1, pow_mul]
        ring
      rw [e, ← h.bar_apply, map_mul]
      linear_combination (M 0 0 * h.bar (M 2 2)) * hun + hun'
    obtain ⟨k, hk⟩ := exists_pow_pow_four_eq_of_pow_odd_eq_one hmodd hz1
    set y := z ^ k with hy
    have hyN' : y ^ (p ^ f + 1) = 1 := by
      rw [hy, ← pow_mul, mul_comm, pow_mul, hq1, pow_mul', hz1, one_pow, one_pow]
    have hyN : (y : K) ^ (p ^ f + 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val, hyN', Units.val_one]
    set s := GeneralLinearGroup.scalar (Fin 4) y with hs
    have hsc : s ∈ Subgroup.center (GL (Fin 4) K) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨y, rfl⟩
    have hsU : s ∈ uMat h 4 := by
      rw [mem_uMat, hs, GeneralLinearGroup.coe_scalar]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.scalar_apply, UnitaryFieldData.bar_apply, ← pow_succ, hyN]
      · simp [Matrix.scalar_apply, Matrix.one_apply_ne hij, Matrix.mul_apply,
          Matrix.diagonal_apply, hij]
    have hAU : A ∈ uMat h 4 := (mem_uMat h).2 hAu
    set S := s⁻¹ * A with hSdef
    have hSdet : GeneralLinearGroup.det S = 1 := by
      rw [hSdef, map_mul, map_inv, ← hz, hk]
      have : GeneralLinearGroup.det s = (z ^ k) ^ 4 := by
        apply Units.ext
        simp [hs, hy]
        ring
      rw [this, inv_mul_cancel]
    have hSU : S ∈ uMat h 4 := mul_mem (inv_mem hsU) hAU
    have hSmem : S ∈ unitarySU p f K 4 := by
      rw [mem_unitarySU_iff h]
      refine ⟨?_, (mem_uMat h).1 hSU⟩
      have := congrArg Units.val hSdet
      rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at this
    refine ⟨θ ⟨S, hSmem⟩, ?_⟩
    ext w
    obtain ⟨g, rfl⟩ := hθ w
    rw [MulAut.conj_apply, ← hlift g, ← map_mul, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom, hgl1, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv]
    change A * (g : GL (Fin 4) K) * A⁻¹ = S * g * S⁻¹
    rw [hSdef, _root_.mul_inv_rev, inv_inv]
    have hs' : ∀ W : GL (Fin 4) K, s⁻¹ * W = W * s⁻¹ := fun W =>
      (Subgroup.mem_center_iff.mp (inv_mem hsc) W).symm
    calc A * (g : GL (Fin 4) K) * A⁻¹ = A * (g : GL (Fin 4) K) * A⁻¹ * s⁻¹ * s := by group
      _ = s⁻¹ * (A * (g : GL (Fin 4) K) * A⁻¹) * s := by rw [hs' (A * (g : GL (Fin 4) K) * A⁻¹)]
      _ = s⁻¹ * A * (g : GL (Fin 4) K) * (A⁻¹ * s) := by group
  ·
    right
    have hx : M 0 0 = 0 := by
      rcases mul_eq_zero.1 r1 with h0 | h0
      · exact h0
      · exact absurd (sub_eq_zero.1 h0) hφμ
    have hy : M 2 2 = 0 := by
      rcases mul_eq_zero.1 r4 with h0 | h0
      · exact h0
      · exfalso
        apply hφμ
        have e := congrArg h.bar (sub_eq_zero.1 h0)
        rwa [h.bar_bar, h.bar_bar] at e
    rw [hx, hy, map_zero, zero_mul, add_zero] at hun
    have hf0 : M 2 1 ≠ 0 := by
      intro h0
      rw [h0, map_zero, mul_zero] at hun
      exact zero_ne_one hun
    have hφμb : φ (μ : K) = h.bar μ := by
      rcases mul_eq_zero.1 r3 with h0 | h0
      · exact absurd h0 hf0
      · exact sub_eq_zero.1 h0
    have hφb : ∀ c, φ c = h.bar c := eq_of_eq_on_generator hμ (φ : K →+* K) h.bar hφμb
    set β : K := μ - h.bar μ with hβdef
    set γ : K := -(β * M 2 1 * h.bar (M 2 1)) with hγdef
    have hβ0 : β ≠ 0 := sub_ne_zero.2 (Ne.symm hμb)
    have hββ : β + h.bar β = 0 := by
      rw [hβdef, map_sub, h.bar_bar]
      ring
    have hγγ : γ + h.bar γ = 0 := by
      rw [hγdef, map_neg, map_mul, map_mul, h.bar_bar]
      linear_combination (-(M 2 1 * h.bar (M 2 1))) * hββ
    have hc1 : M 0 3 * h.bar γ = β * M 2 1 := by
      rw [hγdef, map_neg, map_mul, map_mul, h.bar_bar]
      linear_combination (-(h.bar β * M 2 1)) * hun - M 2 1 * hββ
    have hc2 : M 0 3 * γ = h.bar β * M 2 1 := by
      rw [hγdef]
      linear_combination (-(β * M 2 1)) * hun - M 2 1 * hββ
    have hMb : M = blk 0 (M 0 3) (M 2 1) 0 := by
      conv_lhs => rw [hblk]
      rw [hx, hy]
    refine ⟨hypSU h P hP (gfix β γ) (unitary_gfix h hββ hγγ) (det_gfix β γ), ?_, β, γ, hβ0,
      cP_hypSU h P hP _ _ _⟩
    rw [← hlift']
    congr 1
    apply Subtype.ext
    rw [ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom]
    change A * glAut φ (P * toGL (gfix β γ) (det_gfix β γ) * P⁻¹) * A⁻¹ =
      P * toGL (gfix β γ) (det_gfix β γ) * P⁻¹
    obtain ⟨T, hT⟩ : ∃ X : GL (Fin 4) K, X = toGL (gfix β γ) (det_gfix β γ) := ⟨_, rfl⟩
    rw [← hT]
    have hAT : A' * glAut φ T = T * A' := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_glAut, hT, coe_toGL, ← hM]
      have e : (gfix β γ).map φ = gfix (h.bar β) (h.bar γ) := by
        rw [← hφb β, ← hφb γ]
        exact map_gfix' (φ : K →+* K) β γ
      rw [e, hMb]
      exact blk_mul_gfix h hc1 hc2
    have hAP : A * glAut φ P = P * A' := by
      rw [hA']
      group
    calc A * glAut φ (P * T * P⁻¹) * A⁻¹ =
        (A * glAut φ P) * glAut φ T * (A * glAut φ P)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
          group
      _ = P * A' * glAut φ T * (P * A')⁻¹ := by rw [hAP]
      _ = P * (A' * glAut φ T) * A'⁻¹ * P⁻¹ := by group
      _ = P * T * P⁻¹ := by
          rw [hAT]
          group

theorem cP_uU (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG) (c : K) :
    cP P (uU h P hP c) = U12 h c :=
  cP_hypSU h P hP _ _ _

theorem cP_uL (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG) (c : K) :
    cP P (uL h P hP c) = U21 h c :=
  cP_hypSU h P hP _ _ _

theorem eq_blk_diag_of_comm {μ : K} (hμb : h.bar μ ≠ μ) {W : Matrix (Fin 4) (Fin 4) K}
    (h1 : W * U12 h 1 = U12 h 1 * W) (h2 : W * U21 h 1 = U21 h 1 * W)
    (h3 : W * U12 h μ = U12 h μ * W) : W = blk (W 0 0) 0 0 (W 2 2) := by
  have hb := eq_blk_of_comm h h1 h2
  rw [hb] at h3
  obtain ⟨-, r2, r3, -⟩ := blk_rel h h3
  have e1 : W 0 3 = 0 := by
    rcases mul_eq_zero.1 r2 with h0 | h0
    · exact h0
    · exact absurd (sub_eq_zero.1 h0) hμb
  have e2 : W 2 1 = 0 := by
    rcases mul_eq_zero.1 r3 with h0 | h0
    · exact h0
    · exact absurd (sub_eq_zero.1 h0).symm hμb
  conv_lhs => rw [hb]
  rw [e1, e2]

include h in
theorem not_mem_normalizer (hp2 : p ≠ 2) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {l : K} (hl : l ^ 2 = -1) (hbl : h.bar l * l = -1) {μ : K} (hμb : h.bar μ ≠ μ)
    {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hJX : J' ≤ Subgroup.centralizer {(QuotientGroup.mk (hypSU h P hP (X1 l) (unitary_X1 h hbl)
      (det_X1 hl)) : StatedProj (StatedSU 4 (p ^ f) K))})
    (hU : HasUnipU h P hP μ J') {g : unitarySU p f K 4} {β γ : K} (hβ : β ≠ 0)
    (hg : cP P g = gfix β γ) :
    (QuotientGroup.mk g : StatedProj (StatedSU 4 (p ^ f) K)) ∉
      Subgroup.normalizer (J' : Set (StatedProj (StatedSU 4 (p ^ f) K))) := by
  intro hN
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hl
    exact one_ne_zero (by linear_combination hl : (1 : K) = 0)
  set X := hypSU h P hP (X1 l) (unitary_X1 h hbl) (det_X1 hl) with hX
  set Y := g * X * g⁻¹ with hY
  have hcomm : ∀ u : unitarySU p f K 4,
      (QuotientGroup.mk u : StatedProj (StatedSU 4 (p ^ f) K)) ∈ J' → u ^ p = 1 →
        cP P u * cP P Y = cP P Y * cP P u := by
    intro u hu hup
    have h1 : (QuotientGroup.mk g : StatedProj (StatedSU 4 (p ^ f) K))⁻¹ *
        QuotientGroup.mk u * (QuotientGroup.mk g)⁻¹⁻¹ ∈ J' :=
      (Subgroup.mem_normalizer_iff.mp (inv_mem hN) _).mp hu
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hJX h1)
    have h3 : (QuotientGroup.mk u : StatedProj (StatedSU 4 (p ^ f) K)) * QuotientGroup.mk Y =
        QuotientGroup.mk Y * QuotientGroup.mk u := by
      rw [hY, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [inv_inv] at h2
      calc (QuotientGroup.mk u : StatedProj (StatedSU 4 (p ^ f) K)) *
            (QuotientGroup.mk g * QuotientGroup.mk X * (QuotientGroup.mk g)⁻¹) =
          QuotientGroup.mk g * (((QuotientGroup.mk g)⁻¹ * QuotientGroup.mk u *
            QuotientGroup.mk g) * QuotientGroup.mk X) * (QuotientGroup.mk g)⁻¹ := by group
        _ = QuotientGroup.mk g * (QuotientGroup.mk X * ((QuotientGroup.mk g)⁻¹ *
            QuotientGroup.mk u * QuotientGroup.mk g)) * (QuotientGroup.mk g)⁻¹ := by rw [h2]
        _ = _ := by group
    have h4 := comm_of_mk_comm' h hp2 hup h3
    rw [← cP_mul, ← cP_mul, h4]
  obtain ⟨hu1, hu2, hu3⟩ := hU
  have m1 := hcomm _ hu1 (uU_pow_char h P hP 1)
  have m2 := hcomm _ hu2 (uL_pow_char h P hP 1)
  have m3 := hcomm _ hu3 (uU_pow_char h P hP μ)
  rw [cP_uU] at m1 m3
  rw [cP_uL] at m2
  have hW := eq_blk_diag_of_comm h hμb m1.symm m2.symm m3.symm
  have hYg : cP P Y * cP P g = cP P g * cP P X := by
    rw [← cP_mul, ← cP_mul, hY, inv_mul_cancel_right]
  rw [hg, hX, cP_hypSU, hW] at hYg
  exact hβ (eq_zero_of_blk_mul_gfix h2K hl0 hYg)

include h in
theorem isCyclic_centralizer (hp2 : p ≠ 2) (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {μ : K} (hμb : h.bar μ ≠ μ) {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hU : HasUnipU h P hP μ J') :
    IsCyclic (Subgroup.centralizer (J' : Set (StatedProj (StatedSU 4 (p ^ f) K)))) := by
  classical
  have : Finite K := h.finite
  obtain ⟨hu1, hu2, hu3⟩ := hU
  obtain ⟨D, hD⟩ : ∃ D : Subgroup (unitarySU p f K 4),
      D = Subgroup.centralizer {uU h P hP 1, uL h P hP 1, uU h P hP μ} := ⟨_, rfl⟩
  have hDform : ∀ g ∈ D, cP P g = blk (cP P g 0 0) 0 0 (cP P g 2 2) := by
    intro g hg
    rw [hD, Subgroup.mem_centralizer_iff] at hg
    have c1 := congrArg (cP P) (hg (uU h P hP 1) (Set.mem_insert _ _))
    have c2 := congrArg (cP P) (hg (uL h P hP 1) (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    have c3 := congrArg (cP P) (hg (uU h P hP μ)
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    rw [cP_mul, cP_mul, cP_uU] at c1 c3
    rw [cP_mul, cP_mul, cP_uL] at c2
    exact eq_blk_diag_of_comm h hμb c1.symm c2.symm c3.symm
  have hun : ∀ g ∈ D, h.bar (cP P g 0 0) * cP P g 2 2 = 1 := by
    intro g hg
    have hu := unitary_cP h P hP g
    rw [hDform g hg] at hu
    have := blk_unitary h hu
    rwa [map_zero, mul_zero, zero_add] at this
  have hx0 : ∀ g ∈ D, cP P g 0 0 ≠ 0 := by
    intro g hg h0
    have := hun g hg
    rw [h0, map_zero, zero_mul] at this
    exact zero_ne_one this
  let ψ : D →* Kˣ :=
    { toFun := fun g => Units.mk0 (cP P g.1 0 0) (hx0 g.1 g.2)
      map_one' := by
        apply Units.ext
        change cP P (1 : unitarySU p f K 4) 0 0 = 1
        rw [cP, OneMemClass.coe_one, Units.val_one, Matrix.mul_one, ← Units.val_mul,
          inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
      map_mul' := fun g g' => by
        apply Units.ext
        change cP P (g.1 * g'.1) 0 0 = cP P g.1 0 0 * cP P g'.1 0 0
        rw [cP_mul, hDform g.1 g.2, hDform g'.1 g'.2, blk_mul_blk]
        simp [blk] }
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have h1 : cP P g.1 0 0 = 1 := congrArg Units.val hg
    have h2 : cP P g.1 2 2 = 1 := by
      have := hun g.1 g.2
      rwa [h1, map_one, one_mul] at this
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply eq_of_cP_eq P
    rw [hDform g.1 g.2, h1, h2, blk_one, OneMemClass.coe_one, cP, OneMemClass.coe_one,
      Units.val_one, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hDc : IsCyclic D := isCyclic_of_injective ψ hψ
  set θ : unitarySU p f K 4 →* StatedProj (StatedSU 4 (p ^ f) K) :=
    QuotientGroup.mk' (scal p f K) with hθdef
  have hle : Subgroup.centralizer (J' : Set (StatedProj (StatedSU 4 (p ^ f) K))) ≤
      (θ.comp D.subtype).range := by
    intro w hw
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective w
    have hgD : g ∈ D := by
      rw [hD, Subgroup.mem_centralizer_iff]
      intro u hu
      have key : ∀ v : unitarySU p f K 4,
          (QuotientGroup.mk v : StatedProj (StatedSU 4 (p ^ f) K)) ∈ J' → v ^ p = 1 →
            v * g = g * v := by
        intro v hv hvp
        have := Subgroup.mem_centralizer_iff.mp hw _ hv
        exact (comm_of_mk_comm h hp2 hvp this.symm).symm
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl
      · exact key _ hu1 (uU_pow_char h P hP 1)
      · exact key _ hu2 (uL_pow_char h P hP 1)
      · exact key _ hu3 (uU_pow_char h P hP μ)
    exact ⟨⟨g, hgD⟩, rfl⟩
  have hrc : IsCyclic (θ.comp D.subtype).range :=
    isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  exact isCyclic_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

end StabU

end CFSG.ComponentClassification.CatFactsL4U4
