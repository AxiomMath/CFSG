module

public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Basic

public section

namespace CFSG.SectionRank.ClassicalEven

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix

variable {ι : Type} [DecidableEq ι] {K : Type} [Field K]

section Diag

variable [Fintype ι]

@[expose] def torusDiag : (ι → Kˣ) →* GL ι K where
  toFun d := ⟨diagonal fun i => (d i : K), diagonal fun i => ((d i)⁻¹ : Kˣ),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; simp,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; simp⟩
  map_one' := Units.ext (by simp)
  map_mul' a b := Units.ext (by simp [diagonal_mul_diagonal])

theorem coe_torusDiag (d : ι → Kˣ) :
    (torusDiag d : Matrix ι ι K) = diagonal fun i => (d i : K) :=
  rfl

theorem torusDiag_injective : Function.Injective (torusDiag : (ι → Kˣ) →* GL ι K) := by
  intro a b h
  funext i
  have h' := congrArg (fun A : GL ι K => (A : Matrix ι ι K) i i) h
  simp only [coe_torusDiag, diagonal_apply_eq] at h'
  exact Units.ext h'

theorem scalar_eq_torusDiag (c : Kˣ) :
    GeneralLinearGroup.scalar ι c = torusDiag fun _ => c :=
  Units.ext (by rw [GeneralLinearGroup.coe_scalar, scalar_apply, coe_torusDiag])

theorem det_torusDiag (d : ι → Kˣ) :
    (torusDiag d : Matrix ι ι K).det = ((∏ i, d i : Kˣ) : K) := by
  rw [coe_torusDiag, det_diagonal, Units.coe_prod]

theorem torusDiag_mem_SL {n : ℕ} {d : Fin n → Kˣ} (hd : ∏ i, d i = 1) :
    torusDiag d ∈ StatedSL n K :=
  Subgroup.subset_closure (show (torusDiag d : Matrix (Fin n) (Fin n) K).det = 1 by
    rw [det_torusDiag, hd, Units.val_one])

theorem torusDiag_mem_SU {n q : ℕ} (hq : q ≠ 0) {d : Fin n → Kˣ} (hd : ∏ i, d i = 1)
    (hdq : d ^ (q + 1) = 1) : torusDiag d ∈ StatedSU n q K := by
  refine Subgroup.subset_closure ⟨by rw [det_torusDiag, hd, Units.val_one], ?_⟩
  rw [coe_torusDiag, diagonal_map (f := fun x : K => x ^ q) (zero_pow hq), diagonal_transpose,
    diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rw [← pow_succ, ← Units.val_pow_eq_pow_val, ← Pi.pow_apply, hdq, Pi.one_apply, Units.val_one]

end Diag

@[expose] def torusVec (ζ : Kˣ) (j k : ι) : ι → Kˣ :=
  Pi.mulSingle j ζ / Pi.mulSingle k ζ

theorem torusVec_pow (ζ : Kˣ) (j k : ι) (m : ℕ) : torusVec ζ j k ^ m = torusVec (ζ ^ m) j k := by
  rw [torusVec, torusVec, div_pow, Pi.mulSingle_pow, Pi.mulSingle_pow]

theorem torusVec_one (j k : ι) : torusVec (1 : Kˣ) j k = 1 := by
  rw [torusVec, Pi.mulSingle_one, Pi.mulSingle_one, div_one]

theorem torusVec_apply_left (ζ : Kˣ) {j k : ι} (h : j ≠ k) : torusVec ζ j k j = ζ := by
  rw [torusVec, Pi.div_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne h, div_one]

theorem torusVec_apply_right (ζ : Kˣ) {j k : ι} (h : j ≠ k) : torusVec ζ j k k = ζ⁻¹ := by
  rw [torusVec, Pi.div_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne h.symm, one_div]

theorem torusVec_apply_of_ne (ζ : Kˣ) {i j k : ι} (hj : i ≠ j) (hk : i ≠ k) :
    torusVec ζ j k i = 1 := by
  rw [torusVec, Pi.div_apply, Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hk, div_one]

variable [Fintype ι]

theorem prod_torusVec (ζ : Kˣ) (j k : ι) : ∏ i, torusVec ζ j k i = 1 := by
  simp only [torusVec, Pi.div_apply, Finset.prod_div_distrib, Fintype.prod_pi_mulSingle',
    div_self']

theorem three_le_pRank_torus [Finite K] {H : Subgroup (GL ι K)} {r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) {ζ : Kˣ} (hζ : orderOf ζ = r) {i₀ i₁ i₂ i₃ : ι} (h01 : i₀ ≠ i₁)
    (h02 : i₀ ≠ i₂) (h03 : i₀ ≠ i₃) (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃)
    (hH : ∀ j, torusDiag (torusVec ζ j i₃) ∈ H) :
    3 ≤ pRank r (⊤ : Subgroup (StatedProj H)) := by
  have hr : r.Prime := Fact.out
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    exact hr.one_lt.ne hζ
  have hpow (j : ι) : torusDiag (torusVec ζ j i₃) ^ r = 1 := by
    rw [← map_pow, torusVec_pow, ← hζ, pow_orderOf_eq_one, torusVec_one, map_one]
  have hcomm (a b : ι → Kˣ) : Commute (torusDiag a) (torusDiag b) :=
    (Commute.all a b).map torusDiag
  have hent {d d' : ι → Kˣ} (h : torusDiag d = torusDiag d') (i : ι) : d i = d' i :=
    congrFun (torusDiag_injective h) i
  refine three_le_pRank_statedProj (hH i₀) (hH i₁) (hH i₂) (hpow i₀) (hpow i₁) (hpow i₂)
    (hcomm _ _) (hcomm _ _) (hcomm _ _) ?_ ?_ ?_
  · rintro ⟨c, hc⟩
    rw [scalar_eq_torusDiag] at hc
    have e0 := hent hc i₀
    have e1 := hent hc i₁
    rw [torusVec_apply_left ζ h03] at e0
    rw [torusVec_apply_of_ne ζ h01.symm h13] at e1
    exact hζ1 (e0.symm.trans e1)
  · rintro a _ ⟨c, rfl⟩ h
    rw [← map_pow, torusVec_pow, scalar_eq_torusDiag, ← map_mul] at h
    have e1 := hent h i₁
    have e2 := hent h i₂
    simp only [Pi.mul_apply, torusVec_apply_of_ne _ h01.symm h13, torusVec_apply_left _ h13,
      torusVec_apply_of_ne _ h02.symm h23, torusVec_apply_of_ne _ h12.symm h23, one_mul] at e1 e2
    exact hζ1 (e1.symm.trans e2)
  · rintro a b _ ⟨c, rfl⟩ h
    rw [← map_pow, ← map_pow, torusVec_pow, torusVec_pow, scalar_eq_torusDiag, ← map_mul,
      ← map_mul] at h
    have e0 := hent h i₀
    have e1 := hent h i₁
    have e2 := hent h i₂
    have e3 := hent h i₃
    simp only [Pi.mul_apply, torusVec_apply_left _ h03, torusVec_apply_left _ h13,
      torusVec_apply_left _ h23, torusVec_apply_right _ h03, torusVec_apply_right _ h13,
      torusVec_apply_right _ h23, torusVec_apply_of_ne _ h01 h03, torusVec_apply_of_ne _ h02 h03,
      torusVec_apply_of_ne _ h01.symm h13, torusVec_apply_of_ne _ h12 h13,
      torusVec_apply_of_ne _ h02.symm h23, torusVec_apply_of_ne _ h12.symm h23, one_mul,
      mul_one] at e0 e1 e2 e3
    rw [e2] at e0 e1 e3
    rw [eq_inv_of_mul_eq_one_left e0, eq_inv_of_mul_eq_one_left e1, inv_inv] at e3
    have h4 : ζ ^ 4 = 1 := by rw [pow_succ, pow_succ, pow_two, e3, inv_mul_cancel]
    have hdvd : r ∣ 2 ^ 2 := hζ ▸ orderOf_dvd_of_pow_eq_one h4
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hdvd))

theorem psl_torus_three_le_pRank {K : Type} [Field K] [Finite K] {f n : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hn : 4 ≤ n) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 3 ≤ pRank r (⊤ : Subgroup (StatedProj (StatedSL n K))) := by
  have h4 : 4 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right two_pos hf)
  have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have hr : (2 ^ f - 1).minFac.Prime := Nat.minFac_prime (by omega)
  have hr2 : (2 ^ f - 1).minFac ≠ 2 := fun h => by
    have h' := Nat.minFac_dvd (2 ^ f - 1)
    rw [h] at h'
    omega
  have := Fact.mk hr
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) (2 ^ f - 1).minFac
    (by rw [Nat.card_units, hK]; exact Nat.minFac_dvd _)
  exact ⟨_, hr, hr2, three_le_pRank_torus hr2 hζ (i₀ := ⟨0, by omega⟩) (i₁ := ⟨1, by omega⟩)
    (i₂ := ⟨2, by omega⟩) (i₃ := ⟨3, by omega⟩) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) fun j => torusDiag_mem_SL (prod_torusVec ζ j _)⟩

theorem psu_torus_three_le_pRank {K : Type} [Field K] [Finite K] {f n : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hn : 4 ≤ n) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧
      3 ≤ pRank r (⊤ : Subgroup (StatedProj (StatedSU n (2 ^ f) K))) := by
  have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have hq : 2 ^ f ≠ 0 := by positivity
  have hr : (2 ^ f + 1).minFac.Prime := Nat.minFac_prime (by omega)
  have hr2 : (2 ^ f + 1).minFac ≠ 2 := fun h => by
    have h' := Nat.minFac_dvd (2 ^ f + 1)
    rw [h] at h'
    omega
  have := Fact.mk hr
  have hcard : Nat.card Kˣ = (2 ^ f + 1) * (2 ^ f - 1) := by
    rw [Nat.card_units, hK, ← Nat.sq_sub_sq, one_pow]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) (2 ^ f + 1).minFac
    (by rw [hcard]; exact (Nat.minFac_dvd _).mul_right _)
  have hζq : ζ ^ (2 ^ f + 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (by rw [hζ]; exact Nat.minFac_dvd _)
  exact ⟨_, hr, hr2, three_le_pRank_torus hr2 hζ (i₀ := ⟨0, by omega⟩) (i₁ := ⟨1, by omega⟩)
    (i₂ := ⟨2, by omega⟩) (i₃ := ⟨3, by omega⟩) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) fun j => torusDiag_mem_SU hq (prod_torusVec ζ j _)
      (by rw [torusVec_pow, hζq, torusVec_one])⟩

end CFSG.SectionRank.ClassicalEven
