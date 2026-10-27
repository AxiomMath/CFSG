module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Inv
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Arith
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.OddStandard.GH71.S55

open Matrix CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Finite K]

namespace C5

omit [Finite K] in
theorem cube_eq_one_of_det {c : Kˣ}
    (h : ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      1) : c ^ 3 = 1 := by
  have h' : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) c) = 1 :=
    Units.ext (by rw [GeneralLinearGroup.val_det_apply, h, Units.val_one])
  rwa [GeneralLinearGroup.det_scalar, Fintype.card_fin] at h'

theorem conj_pow_eq {G : Type*} [Group G] {t s z : G} (hz : ∀ g : G, Commute z g)
    (h : t * s * t⁻¹ = z * s) (k : ℕ) : t ^ k * s * (t ^ k)⁻¹ = z ^ k * s := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc t ^ (k + 1) * s * (t ^ (k + 1))⁻¹ = t * (t ^ k * s * (t ^ k)⁻¹) * t⁻¹ := by group
      _ = t * (z ^ k * s) * t⁻¹ := by rw [ih]
      _ = z ^ k * (t * s * t⁻¹) := by
        rw [← mul_assoc t, ← ((hz t).pow_left k).eq]
        group
      _ = z ^ (k + 1) * s := by rw [h, pow_succ, mul_assoc]

end C5

open C5

theorem orderOf_ne_two_mul_statedProj {p : ℕ} [hp : Fact p.Prime] (hp3 : p ≠ 3)
    (h2 : (2 : K) ≠ 0) (hQ : ¬ p ∣ Nat.card K) (hQ1 : ¬ p ∣ Nat.card K - 1)
    (hQ2 : ¬ p ∣ Nat.card K + 1) {H : Subgroup (GL (Fin 3) K)}
    (hdet : ∀ A ∈ H, (A : Matrix (Fin 3) (Fin 3) K).det = 1) (w : StatedProj H) :
    orderOf w ≠ 2 * p := by
  intro hw
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hsc : ∀ A : ↥H, (A : StatedProj H) = 1 → ∃ c : Kˣ, c ^ 3 = 1 ∧
      (A : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) c := by
    intro A hA
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hA
    obtain ⟨c, hc⟩ := hA
    refine ⟨c, cube_eq_one_of_det ?_, hc.symm⟩
    rw [hc]
    exact hdet A A.2
  have hw2p : w ^ (2 * p) = 1 := hw ▸ pow_orderOf_eq_one w
  have hot : orderOf (w ^ 2) = p := by
    rw [orderOf_pow_of_dvd two_ne_zero (by rw [hw]; exact dvd_mul_right 2 p), hw]
    omega
  have hos : orderOf (w ^ p) = 2 := by
    rw [orderOf_pow_of_dvd hp0 (by rw [hw]; exact dvd_mul_left p 2), hw,
      Nat.mul_div_cancel _ hp.out.pos]
  obtain ⟨T0, hT0⟩ := QuotientGroup.mk_surjective (w ^ 2)
  obtain ⟨S0, hS0⟩ := QuotientGroup.mk_surjective (w ^ p)
  obtain ⟨c, hc3, hc⟩ := hsc (T0 ^ p) (by
    rw [QuotientGroup.mk_pow, hT0, ← pow_mul, hw2p])
  obtain ⟨d, hd3, hd⟩ := hsc (S0 ^ 2) (by
    rw [QuotientGroup.mk_pow, hS0, ← pow_mul, mul_comm, hw2p])
  set T1 := T0 ^ 3 with hT1
  set S1 := S0 ^ 3 with hS1
  have hT1p : ((T1 : GL (Fin 3) K)) ^ p = 1 := by
    rw [hT1, Subgroup.coe_pow, ← pow_mul, mul_comm, pow_mul, ← Subgroup.coe_pow, hc, ← map_pow,
      hc3, map_one]
  have hS1sq : (S1 : GL (Fin 3) K) * (S1 : GL (Fin 3) K) = 1 := by
    rw [← sq, hS1, Subgroup.coe_pow, ← pow_mul, mul_comm, pow_mul, ← Subgroup.coe_pow, hd,
      ← map_pow, hd3, map_one]
  have hT1ne : (T1 : StatedProj H) ≠ 1 := by
    rw [hT1, QuotientGroup.mk_pow, hT0]
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hot] at this
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp this)
  have hS1w : (S1 : StatedProj H) = w ^ p := by
    rw [hS1, QuotientGroup.mk_pow, hS0, pow_succ, ← hos, pow_orderOf_eq_one, one_mul]
  have hS1ne : (S1 : StatedProj H) ≠ 1 := by
    rw [hS1w]
    intro h
    rw [h, orderOf_one] at hos
    exact absurd hos (by norm_num)
  have hcomm : ((T1 * S1 * T1⁻¹ * S1⁻¹ : ↥H) : StatedProj H) = 1 := by
    have hab : Commute (T1 : StatedProj H) (S1 : StatedProj H) := by
      rw [hS1w, hT1, QuotientGroup.mk_pow, hT0, ← pow_mul]
      exact Commute.pow_pow_self w _ _
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hab.eq]
    group
  obtain ⟨e, he3, he⟩ := hsc _ hcomm
  set z := GeneralLinearGroup.scalar (Fin 3) e with hzdef
  have hz : ∀ g : GL (Fin 3) K, Commute z g := fun g => GeneralLinearGroup.scalar_commute e g
  have hts : (T1 : GL (Fin 3) K) * S1 * (T1 : GL (Fin 3) K)⁻¹ = z * S1 := by
    rw [← mul_inv_eq_iff_eq_mul, ← he]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hzp : z ^ p = 1 := by
    have := conj_pow_eq hz hts p
    rw [hT1p, one_mul, inv_one, mul_one] at this
    exact (mul_eq_right.mp this.symm)
  have hz3 : z ^ 3 = 1 := by rw [hzdef, ← map_pow, he3, map_one]
  have hz1 : z = 1 := by
    have h := pow_gcd_eq_one.mpr ⟨hzp, hz3⟩
    rwa [((Nat.coprime_primes hp.out Nat.prime_three).mpr hp3).gcd_eq_one, pow_one] at h
  rw [hz1, one_mul, mul_inv_eq_iff_eq_mul] at hts
  set tM : Matrix (Fin 3) (Fin 3) K := ((T1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  set sM : Matrix (Fin 3) (Fin 3) K := ((S1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hT : tM ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hT1p, Units.val_one]
  have hI : sM * sM = 1 := by
    rw [← Units.val_mul, hS1sq, Units.val_one]
  have hI1 : sM ≠ 1 := by
    intro h
    apply hS1ne
    have : S1 = 1 := Subtype.ext (Units.ext h)
    rw [this, QuotientGroup.mk_one]
  have hI2 : sM ≠ -1 := by
    intro h
    have hd1 : sM.det = 1 := hdet _ S1.2
    rw [h, det_neg, det_one, Fintype.card_fin] at hd1
    apply h2
    linear_combination -hd1
  have hTI : tM * sM = sM * tM := by
    rw [← Units.val_mul, ← Units.val_mul, hts]
  have := eq_one_of_comm_involution h2 hQ hQ1 hQ2 hT hI hI1 hI2 hTI
  apply hT1ne
  have : T1 = 1 := Subtype.ext (Units.ext this)
  rw [this, QuotientGroup.mk_one]

namespace C5

omit [Finite K] in
theorem det_of_mem_statedSL {n : ℕ} {A : GL (Fin n) K} (hA : A ∈ StatedSL n K) :
    (A : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hA

omit [Finite K] in
theorem det_of_mem_statedSU {n q : ℕ} {A : GL (Fin n) K} (hA : A ∈ StatedSU n q K) :
    (A : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSU hA

end C5

theorem orderOf_ne_two_mul_psl3 {p q : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (h2 : (2 : K) ≠ 0)
    (hK : Nat.card K = q) (hpq : p ∣ q ^ 2 + q + 1)
    (w : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K) : orderOf w ≠ 2 * p := by
  have hq : 1 ≤ q := hK ▸ Nat.card_pos
  obtain ⟨h0, h1, h2', -, -, -⟩ := cyc3_excl hp5 hq hpq
  let e : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K ≃*
      StatedProj (StatedSL 3 K) :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 K)).trans
      (projectiveSpecialLinearGroupEquivStatedProj 3 K)
  rw [← MulEquiv.orderOf_eq e w]
  exact orderOf_ne_two_mul_statedProj (by omega) h2 (hK ▸ h0) (hK ▸ h1) (hK ▸ h2')
    (fun _ hA => det_of_mem_statedSL hA) (e w)

theorem orderOf_ne_two_mul_psu3 {p q : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (h2 : (2 : K) ≠ 0)
    (hK : Nat.card K = q ^ 2) (hpq : p ∣ q ^ 2 - q + 1) (w : StatedProj (StatedSU 3 q K)) :
    orderOf w ≠ 2 * p := by
  have hq : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with rfl | h
    · have h0 : 0 < Nat.card K := Nat.card_pos
      rw [hK] at h0
      simp at h0
    · exact h
  obtain ⟨h0, h1, h2', -, h4, -⟩ := cyc6_excl hp5 hq hpq
  refine orderOf_ne_two_mul_statedProj (by omega) h2 ?_ ?_ ?_
    (fun _ hA => det_of_mem_statedSU hA) w
  · rw [hK]
    exact fun h => h0 (hp.out.dvd_of_dvd_pow h)
  · rw [hK, show q ^ 2 - 1 = (q + 1) * (q - 1) by simpa using Nat.pow_two_sub_pow_two q 1]
    intro h
    rcases (Nat.Prime.dvd_mul hp.out).mp h with h | h
    · exact h2' h
    · exact h1 h
  · rw [hK]
    exact h4

end CFSG.OddStandard.GH71.S55
