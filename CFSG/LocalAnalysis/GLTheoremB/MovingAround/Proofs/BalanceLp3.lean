module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.BalanceLp2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.BalanceFromYS3
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.BalanceLp

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.BalanceLp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut localDeltaIn)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open Matrix

section HeisAlg

variable {F : Type} [Field F] [Finite F] {p : ℕ} {A B : GL (Fin p) F} {ω : Fˣ}

theorem commute_of_commute_heis (hp0 : 0 < p) (hω : IsPrimitiveRoot ω p)
    (hAB : A * B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin p) ω) (hpK : (p : F) ≠ 0) {b : Fˣ}
    (hb : B ^ p = GeneralLinearGroup.scalar (Fin p) b) {v v' : GL (Fin p) F} (hv : v * A = A * v)
    (hv' : v' * A = A * v') : v * v' = v' * v := by
  obtain ⟨P, hP⟩ := exists_aeval_of_commute hp0 hω hAB hpK hb (v := (v : Matrix (Fin p) (Fin p) F))
    (by simpa only [Units.val_mul] using congrArg Units.val hv)
  obtain ⟨P', hP'⟩ := exists_aeval_of_commute hp0 hω hAB hpK hb (v := (v' : Matrix (Fin p) (Fin p) F))
    (by simpa only [Units.val_mul] using congrArg Units.val hv')
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hP, hP', ← map_mul, ← map_mul, mul_comm]

theorem conj_mul_comm (hAB : A * B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin p) ω) {v : GL (Fin p) F}
    (hv : v * A = A * v) : B * v * B⁻¹ * A = A * (B * v * B⁻¹) := by
  have h1 := CFSG.HardMathSupport.Timmesfeld.LocalTwo.HeisP.rel_BA hAB
  have hA : A = GeneralLinearGroup.scalar (Fin p) ω * (B * A * B⁻¹) := by
    rw [h1, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  calc B * v * B⁻¹ * A = B * v * B⁻¹ * (GeneralLinearGroup.scalar (Fin p) ω * (B * A * B⁻¹)) := by
        conv_lhs => rw [hA]
    _ = (B * v * B⁻¹ * GeneralLinearGroup.scalar (Fin p) ω) * (B * A * B⁻¹) := by group
    _ = (GeneralLinearGroup.scalar (Fin p) ω * (B * v * B⁻¹)) * (B * A * B⁻¹) := by
        rw [← GeneralLinearGroup.scalar_commute ω (B * v * B⁻¹)]
    _ = GeneralLinearGroup.scalar (Fin p) ω * (B * (v * A) * B⁻¹) := by group
    _ = GeneralLinearGroup.scalar (Fin p) ω * (B * (A * v) * B⁻¹) := by rw [hv]
    _ = (GeneralLinearGroup.scalar (Fin p) ω * (B * A * B⁻¹)) * (B * v * B⁻¹) := by group
    _ = A * (B * v * B⁻¹) := by rw [← hA]

theorem commutator_test (hAB : A * B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin p) ω) {u : GL (Fin p) F}
    (hu : u * A = A * u) :
    (u * B * u⁻¹ * B⁻¹) * A = A * (u * B * u⁻¹ * B⁻¹) ∧
      conjAut p F (u * B * u⁻¹ * B⁻¹) ∈ innerAut (projectiveSL p F) := by
  refine ⟨?_, conjAut_mem_range_conj_of_det_eq_pow (μ := 1) ?_⟩
  · have h1 := conj_mul_comm hAB (v := u⁻¹) ((show Commute u A from hu).inv_left).eq
    have e : u * B * u⁻¹ * B⁻¹ = u * (B * u⁻¹ * B⁻¹) := by group
    rw [e]
    exact ((show Commute u A from hu).mul_left (show Commute (B * u⁻¹ * B⁻¹) A from h1)).eq
  · rw [one_pow, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (GeneralLinearGroup.det u)]
    group

theorem comm_scalar_mul (c : Fˣ) (g h : GL (Fin p) F) :
    g * (GeneralLinearGroup.scalar (Fin p) c * h) * g⁻¹ * (GeneralLinearGroup.scalar (Fin p) c * h)⁻¹ =
      g * h * g⁻¹ * h⁻¹ := by
  have := commutator_central_mul (a := g) (b := h) (c := 1) (d := GeneralLinearGroup.scalar (Fin p) c)
    (fun x => by rw [one_mul, mul_one]) (fun x => GeneralLinearGroup.scalar_commute c x)
  simpa using this

theorem conj_scalar_add (g : GL (Fin p) F) (s : F) (N : Matrix (Fin p) (Fin p) F) :
    (g : Matrix (Fin p) (Fin p) F) * (Matrix.scalar (Fin p) s + N) *
        ((g⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      Matrix.scalar (Fin p) s + (g : Matrix (Fin p) (Fin p) F) * N *
        ((g⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
  have hgg : (g : Matrix (Fin p) (Fin p) F) * ((g⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Matrix.mul_add, Matrix.add_mul,
    ← (Matrix.scalar_commute s (fun r => Commute.all _ r) (g : Matrix (Fin p) (Fin p) F)).eq, Matrix.mul_assoc,
    hgg, Matrix.mul_one]

theorem B_conj_A (hAB : A * B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin p) ω) :
    (B : Matrix (Fin p) (Fin p) F) * A * ((B⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) =
        ((ω⁻¹ : Fˣ) : F) • (A : Matrix (Fin p) (Fin p) F) ∧
      (B : Matrix (Fin p) (Fin p) F) * ((A⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) *
          ((B⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) =
        (ω : F) • ((A⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
  have h1 := CFSG.HardMathSupport.Timmesfeld.LocalTwo.HeisP.rel_BA hAB
  have h2 : B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin p) ω * A⁻¹ := by
    have e : B * A⁻¹ * B⁻¹ = (B * A * B⁻¹)⁻¹ := by group
    rw [e, h1, _root_.mul_inv_rev, ← map_inv, inv_inv, ← GeneralLinearGroup.scalar_commute ω A⁻¹]
  constructor
  · have h3 := congrArg (fun g : GL (Fin p) F => (g : Matrix (Fin p) (Fin p) F)) h1
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h3
    rw [h3, ← Matrix.smul_eq_diagonal_mul]
  · have h3 := congrArg (fun g : GL (Fin p) F => (g : Matrix (Fin p) (Fin p) F)) h2
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h3
    rw [h3, ← Matrix.smul_eq_diagonal_mul]

theorem isUnit_det_scalar_add_of_ne {M : Matrix (Fin p) (Fin p) F} {μ : F}
    (hM : M ^ p = Matrix.scalar (Fin p) μ) {a : F} (ha : (-a) ^ p ≠ μ) :
    IsUnit (Matrix.scalar (Fin p) a + M).det := by
  classical
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hsc : ∀ c : F, (Matrix.scalar (Fin p) c).mulVec v = c • v := fun c => by
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have h1 : M.mulVec v = (-a) • v := by
    rw [Matrix.add_mulVec, hsc] at hv
    rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]
    exact hv
  have h2 : ∀ n : ℕ, (M ^ n).mulVec v = (-a) ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  have h3 := h2 p
  rw [hM, hsc] at h3
  have h4 : (μ - (-a) ^ p) • v = 0 := by rw [sub_smul, h3, sub_self]
  rcases smul_eq_zero.1 h4 with h5 | h5
  · exact ha (sub_eq_zero.1 h5).symm
  · exact hv0 h5

theorem coeff_theta0 {M : Matrix (Fin p) (Fin p) F} (hind : LinearIndependent F (fun i : Fin p => M ^ (i : ℕ)))
    (hp3 : 3 ≤ p) {a s l ν w : F} (ha : a ≠ 0) (hs : s ≠ 0) (hw : w ≠ 1)
    (h : (Matrix.scalar (Fin p) s + l • M) * (Matrix.scalar (Fin p) a + w • M) =
      ν • ((Matrix.scalar (Fin p) a + M) * (Matrix.scalar (Fin p) s + (l * w) • M))) : s = l * a := by
  have hsc : ∀ c : F, Matrix.scalar (Fin p) c = c • (1 : Matrix (Fin p) (Fin p) F) := fun c => by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [hsc, hsc] at h
  have h3 : (s * a - ν * (a * s)) • M ^ 0 + (s * w + l * a - ν * (a * (l * w) + s)) • M ^ 1 +
      (l * w - ν * (l * w)) • M ^ 2 = 0 := by
    have e : (s * a - ν * (a * s)) • M ^ 0 + (s * w + l * a - ν * (a * (l * w) + s)) • M ^ 1 +
        (l * w - ν * (l * w)) • M ^ 2 =
        (s • (1 : Matrix (Fin p) (Fin p) F) + l • M) * (a • 1 + w • M) -
          ν • ((a • 1 + M) * (s • 1 + (l * w) • M)) := by
      simp only [pow_zero, pow_one, pow_two, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one]
      module
    rw [e, h, sub_self]
  obtain ⟨h4, h5, -⟩ := lin_three hind hp3 h3
  have hν : ν = 1 := by
    have h6 : (1 - ν) * (a * s) = 0 := by linear_combination h4
    have h7 := (mul_eq_zero.1 h6).resolve_right (mul_ne_zero ha hs)
    linear_combination -h7
  subst hν
  have h6 : (s - l * a) * (w - 1) = 0 := by linear_combination h5
  have h7 := (mul_eq_zero.1 h6).resolve_right (sub_ne_zero.2 hw)
  linear_combination h7

theorem coeff_theta1 {M N : Matrix (Fin p) (Fin p) F} (hind : LinearIndependent F (fun i : Fin p => M ^ (i : ℕ)))
    (hp3 : 3 ≤ p) (hNM : N * M = 1) {a s k z ν : F} (ha : a ≠ 0) (hs : s ≠ 0) (hk : k ≠ 0) (hz : z ≠ 0)
    (h : (Matrix.scalar (Fin p) s + (k * z) • N) * (Matrix.scalar (Fin p) a + z⁻¹ • M) =
      ν • ((Matrix.scalar (Fin p) a + M) * (Matrix.scalar (Fin p) s + k • N))) : z * z = 1 := by
  have hsc : ∀ c : F, Matrix.scalar (Fin p) c = c • (1 : Matrix (Fin p) (Fin p) F) := fun c => by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [hsc, hsc] at h
  have hNM' : N * (M * M) = M := by rw [← Matrix.mul_assoc, hNM, Matrix.one_mul]
  have hMN : M * N = 1 := mul_eq_one_comm.1 hNM
  have h' : (s • (1 : Matrix (Fin p) (Fin p) F) + (k * z) • N) * (a • 1 + z⁻¹ • M) * M =
      ν • ((a • (1 : Matrix (Fin p) (Fin p) F) + M) * (s • 1 + k • N)) * M := by rw [h]
  have e1 : (s • (1 : Matrix (Fin p) (Fin p) F) + (k * z) • N) * (a • 1 + z⁻¹ • M) * M =
      (k * z * a) • M ^ 0 + (s * a + k * z * z⁻¹) • M ^ 1 + (s * z⁻¹) • M ^ 2 := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc, hNM, hNM']
    simp only [pow_zero, pow_one, pow_two]
    module
  have e2 : ν • ((a • (1 : Matrix (Fin p) (Fin p) F) + M) * (s • 1 + k • N)) * M =
      (ν * (a * k)) • M ^ 0 + (ν * (a * s + k)) • M ^ 1 + (ν * s) • M ^ 2 := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc, hNM, hMN]
    simp only [pow_zero, pow_one, pow_two]
    module
  rw [e1, e2] at h'
  have h3 : (k * z * a - ν * (a * k)) • M ^ 0 + (s * a + k * z * z⁻¹ - ν * (a * s + k)) • M ^ 1 +
      (s * z⁻¹ - ν * s) • M ^ 2 = 0 := by
    have e : (k * z * a - ν * (a * k)) • M ^ 0 + (s * a + k * z * z⁻¹ - ν * (a * s + k)) • M ^ 1 +
        (s * z⁻¹ - ν * s) • M ^ 2 =
        ((k * z * a) • M ^ 0 + (s * a + k * z * z⁻¹) • M ^ 1 + (s * z⁻¹) • M ^ 2) -
          ((ν * (a * k)) • M ^ 0 + (ν * (a * s + k)) • M ^ 1 + (ν * s) • M ^ 2) := by
      module
    rw [e, h', sub_self]
  obtain ⟨h4, -, h6⟩ := lin_three hind hp3 h3
  have hνz : ν = z := by
    have h7 : (z - ν) * (k * a) = 0 := by linear_combination h4
    have h8 := (mul_eq_zero.1 h7).resolve_right (mul_ne_zero hk ha)
    linear_combination -h8
  have hνz' : ν = z⁻¹ := by
    have h7 : (z⁻¹ - ν) * s = 0 := by linear_combination h6
    have h8 := (mul_eq_zero.1 h7).resolve_right hs
    linear_combination -h8
  have h9 : z = z⁻¹ := hνz.symm.trans hνz'
  calc z * z = z * z⁻¹ := by rw [← h9]
    _ = 1 := mul_inv_cancel₀ hz

end HeisAlg

section CharTwo

variable {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ}

theorem odd_card_sub_one_two : Odd (Nat.card F - 1) := by
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  rw [Nat.card_eq_fintype_card, hn]
  obtain ⟨k, hk⟩ : ∃ k, (n : ℕ) = k + 1 := ⟨n - 1, by have := n.pos; omega⟩
  rw [hk, pow_succ]
  exact ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩

theorem exists_odd_conjAut_pow_eq_one_two (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1)
    {A B : GL (Fin p) F} {ω : Fˣ} (hω : IsPrimitiveRoot ω p)
    (hAB : A * B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin p) ω) {μ b : Fˣ}
    (hμ : A ^ p = GeneralLinearGroup.scalar (Fin p) μ) (hb : B ^ p = GeneralLinearGroup.scalar (Fin p) b)
    {v : GL (Fin p) F} (hv : v * A = A * v) : ∃ m : ℕ, Odd m ∧ conjAut p F (v ^ m) = 1 := by
  classical
  by_cases hζ : μ ^ ((Nat.card F - 1) / p) = 1
  · haveI : Fintype F := Fintype.ofFinite F
    have hp0 := hp.pos
    have hQF : Fintype.card F = Nat.card F := Nat.card_eq_fintype_card.symm
    have hQ1 : 1 ≤ Nat.card F := Nat.card_pos
    have hpQ : ¬ p ∣ Nat.card F := fun hd => by
      have h1 : p ∣ Nat.card F - (Nat.card F - 1) := Nat.dvd_sub hd hpF
      rw [show Nat.card F - (Nat.card F - 1) = 1 by omega] at h1
      exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
    have hpK : (p : F) ≠ 0 := CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card hp hpQ
    have hQs : Nat.card F = p * ((Nat.card F - 1) / p) + 1 := by
      rw [Nat.mul_div_cancel' hpF]
      omega
    have hAQ : A ^ Nat.card F = A := by
      conv_lhs => rw [hQs]
      rw [pow_succ, pow_mul, hμ, ← map_pow, hζ, map_one, one_mul]
    have hAQm : (A : Matrix (Fin p) (Fin p) F) ^ Nat.card F = A := by
      have := congrArg Units.val hAQ
      rwa [Units.val_pow_eq_pow_val] at this
    obtain ⟨P, hP⟩ := exists_aeval_of_commute hp0 hω hAB hpK hb (v := (v : Matrix (Fin p) (Fin p) F))
      (by simpa only [Units.val_mul] using congrArg Units.val hv)
    have hvQ : v ^ Nat.card F = v := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hP, ← map_pow, ← hQF, ← FiniteField.expand_card, Polynomial.expand_aeval,
        hQF, hAQm]
    have hv1 : v ^ (Nat.card F - 1) = 1 := by
      have h1 : v ^ (Nat.card F - 1) * v = 1 * v := by
        rw [← pow_succ, Nat.sub_add_cancel hQ1, hvQ, one_mul]
      exact mul_right_cancel h1
    exact ⟨Nat.card F - 1, odd_card_sub_one_two, by rw [hv1, map_one]⟩
  · exact exists_odd_conjAut_pow_eq_one hp hp2 hpF hω hAB hμ hb hζ hv

theorem commute_conjAut_two (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1)
    {A B : GL (Fin p) F} {ω : Fˣ} (hω : IsPrimitiveRoot ω p)
    (hAB : A * B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin p) ω) {μ b : Fˣ}
    (hμ : A ^ p = GeneralLinearGroup.scalar (Fin p) μ) (hb : B ^ p = GeneralLinearGroup.scalar (Fin p) b)
    {H : Subgroup (MulAut (projectiveSL p F))} (hH : innerAut (projectiveSL p F) ≤ H)
    {t : MulAut (projectiveSL p F)}
    (ht : t ∈ pCoreOf 2 (H ⊓ Subgroup.centralizer ({conjAut p F A} : Set (MulAut (projectiveSL p F)))))
    (Θ : GL (Fin p) F →* GL (Fin p) F) (hΘ : ∀ g, t * conjAut p F g * t⁻¹ = conjAut p F (Θ g))
    (hΘA : ∀ w, w * A = A * w → Θ w * A = A * Θ w) {w : GL (Fin p) F} (hw : w * A = A * w)
    (hwi : conjAut p F w ∈ innerAut (projectiveSL p F)) : t * conjAut p F w = conjAut p F w * t := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (projectiveSL p F) := finite_projectiveSL
  have hwC : conjAut p F w ∈ H ⊓ Subgroup.centralizer ({conjAut p F A} : Set (MulAut (projectiveSL p F))) :=
    ⟨hH hwi, Subgroup.mem_centralizer_singleton_iff.2 (by rw [← map_mul, ← map_mul, hw])⟩
  have hcO : t * conjAut p F w * t⁻¹ * (conjAut p F w)⁻¹ ∈
      pCoreOf 2 (H ⊓ Subgroup.centralizer ({conjAut p F A} : Set (MulAut (projectiveSL p F)))) := by
    have h1 : conjAut p F w * t⁻¹ * (conjAut p F w)⁻¹ ∈
        pCoreOf 2 (H ⊓ Subgroup.centralizer ({conjAut p F A} : Set (MulAut (projectiveSL p F)))) :=
      (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hwC) t⁻¹).1
        (Subgroup.inv_mem _ ht)
    have := Subgroup.mul_mem _ ht h1
    simpa [mul_assoc] using this
  have hcv : t * conjAut p F w * t⁻¹ * (conjAut p F w)⁻¹ = conjAut p F (Θ w * w⁻¹) := by
    rw [hΘ, ← map_inv, ← map_mul]
  rw [hcv] at hcO
  obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _ ⟨_, hcO⟩
  have hj' : conjAut p F (Θ w * w⁻¹) ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
  have hvA : (Θ w * w⁻¹) * A = A * (Θ w * w⁻¹) :=
    ((show Commute (Θ w) A from hΘA w hw).mul_left (show Commute w A from hw).inv_left).eq
  obtain ⟨m, hm, hm1⟩ := exists_odd_conjAut_pow_eq_one_two hp hp2 hpF hω hAB hμ hb hvA
  have hcop : Nat.Coprime (2 ^ j) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hm)
  have hv1 : conjAut p F (Θ w * w⁻¹) = 1 := by
    rw [map_pow] at hm1
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hj')
      (orderOf_dvd_of_pow_eq_one hm1))
  rw [← hcv, mul_inv_eq_one] at hv1
  calc t * conjAut p F w = t * conjAut p F w * t⁻¹ * t := by group
    _ = conjAut p F w * t := by rw [hv1]

end CharTwo

section Theta

variable {F : Type} [Field F] [Finite F] {p : ℕ}

@[expose] noncomputable def theta0 (X : GL (Fin p) F) (σ : F ≃+* F) : GL (Fin p) F →* GL (Fin p) F :=
  (MulAut.conj X).toMonoidHom.comp (GeneralLinearGroup.map (σ : F →+* F))

@[expose] noncomputable def theta1 (X : GL (Fin p) F) (σ : F ≃+* F) : GL (Fin p) F →* GL (Fin p) F :=
  (MulAut.conj X).toMonoidHom.comp ((GeneralLinearGroup.map (σ : F →+* F)).comp
    GeneralLinearGroup.inverseTranspose.toMonoidHom)

theorem conj_theta0 (X : GL (Fin p) F) (σ : F ≃+* F) (g : GL (Fin p) F) :
    (conjAut p F X * fieldAut p F σ) * conjAut p F g * (conjAut p F X * fieldAut p F σ)⁻¹ =
      conjAut p F (theta0 X σ g) := by
  have h1 := (standard_automorphism_transport (K := F) (n := p)).2.2.1 σ g
  calc (conjAut p F X * fieldAut p F σ) * conjAut p F g * (conjAut p F X * fieldAut p F σ)⁻¹
      = conjAut p F X * (fieldAut p F σ * conjAut p F g * (fieldAut p F σ)⁻¹) * (conjAut p F X)⁻¹ := by group
    _ = conjAut p F (theta0 X σ g) := by
      rw [h1, ← map_inv, ← map_mul, ← map_mul]
      rfl

theorem conj_theta1 (X : GL (Fin p) F) (σ : F ≃+* F) (g : GL (Fin p) F) :
    (conjAut p F X * fieldAut p F σ * dualAut p F) * conjAut p F g *
        (conjAut p F X * fieldAut p F σ * dualAut p F)⁻¹ = conjAut p F (theta1 X σ g) := by
  have htrans := standard_automorphism_transport (K := F) (n := p)
  have hδinv : (dualAut p F)⁻¹ = dualAut p F := inv_eq_of_mul_eq_one_right htrans.2.2.2.1
  have h1 := htrans.2.2.2.2.1 g
  have h2 := htrans.2.2.1 σ (GeneralLinearGroup.inverseTranspose g)
  calc (conjAut p F X * fieldAut p F σ * dualAut p F) * conjAut p F g *
        (conjAut p F X * fieldAut p F σ * dualAut p F)⁻¹
      = conjAut p F X * (fieldAut p F σ * (dualAut p F * conjAut p F g * (dualAut p F)⁻¹) *
          (fieldAut p F σ)⁻¹) * (conjAut p F X)⁻¹ := by group
    _ = conjAut p F (theta1 X σ g) := by
      rw [hδinv, h1, h2, ← map_inv, ← map_mul, ← map_mul]
      rfl

theorem coe_theta0 (X : GL (Fin p) F) (σ : F ≃+* F) (g : GL (Fin p) F) :
    ((theta0 X σ g : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      (X : Matrix (Fin p) (Fin p) F) * (g : Matrix (Fin p) (Fin p) F).map σ *
        ((X⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
  show ((X * GeneralLinearGroup.map (σ : F →+* F) g * X⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = _
  rw [Units.val_mul, Units.val_mul, coe_map_GL]
  rfl

theorem coe_theta1_inv (X : GL (Fin p) F) (σ : F ≃+* F) (g : GL (Fin p) F) :
    ((theta1 X σ g⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      (X : Matrix (Fin p) (Fin p) F) * ((g : Matrix (Fin p) (Fin p) F).map σ)ᵀ *
        ((X⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
  show ((X * GeneralLinearGroup.map (σ : F →+* F) (GeneralLinearGroup.inverseTranspose g⁻¹) * X⁻¹ :
    GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = _
  rw [Units.val_mul, Units.val_mul, coe_map_GL, GeneralLinearGroup.coe_inverseTranspose, inv_inv,
    Matrix.transpose_map]
  rfl

theorem map_scalar_GL (σ : F →+* F) (c : Fˣ) :
    GeneralLinearGroup.map σ (GeneralLinearGroup.scalar (Fin p) c) =
      GeneralLinearGroup.scalar (Fin p) (Units.map (σ : F →* F) c) := by
  apply Units.ext
  rw [coe_map_GL, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.scalar_apply, Matrix.diagonal_map (map_zero σ)]
  rfl

theorem theta0_scalar (X : GL (Fin p) F) (σ : F ≃+* F) (c : Fˣ) :
    theta0 X σ (GeneralLinearGroup.scalar (Fin p) c) =
      GeneralLinearGroup.scalar (Fin p) (Units.map ((σ : F →+* F) : F →* F) c) := by
  show X * GeneralLinearGroup.map (σ : F →+* F) (GeneralLinearGroup.scalar (Fin p) c) * X⁻¹ = _
  rw [map_scalar_GL, ← GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]

theorem theta1_scalar (X : GL (Fin p) F) (σ : F ≃+* F) (c : Fˣ) :
    theta1 X σ (GeneralLinearGroup.scalar (Fin p) c) =
      GeneralLinearGroup.scalar (Fin p) (Units.map ((σ : F →+* F) : F →* F) c⁻¹) := by
  have hT : GeneralLinearGroup.inverseTranspose (GeneralLinearGroup.scalar (Fin p) c) =
      GeneralLinearGroup.scalar (Fin p) c⁻¹ := by
    apply Units.ext
    rw [GeneralLinearGroup.coe_inverseTranspose, ← map_inv, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.diagonal_transpose]
  show X * GeneralLinearGroup.map (σ : F →+* F)
    (GeneralLinearGroup.inverseTranspose (GeneralLinearGroup.scalar (Fin p) c)) * X⁻¹ = _
  rw [hT, map_scalar_GL, ← GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]

end Theta

section Delta

variable {F : Type} [Field F] [Finite F] {p : ℕ}

theorem heis_data (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1)
    {A B : GL (Fin p) F} (hAB : A * B ≠ B * A) (hA : conjAut p F A ^ p = 1) (hB : conjAut p F B ^ p = 1)
    (hcomm : conjAut p F A * conjAut p F B = conjAut p F B * conjAut p F A) :
    (p : F) ≠ 0 ∧ ∃ z μ b : Fˣ, IsPrimitiveRoot z p ∧ A * B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin p) z ∧
      A ^ p = GeneralLinearGroup.scalar (Fin p) μ ∧ B ^ p = GeneralLinearGroup.scalar (Fin p) b := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hn : 3 ≤ p := by have := hp.two_le; omega
  have hpQ : ¬ p ∣ Nat.card F := fun hd => by
    have hQ1 : 1 ≤ Nat.card F := Nat.card_pos
    have h1 : p ∣ Nat.card F - (Nat.card F - 1) := Nat.dvd_sub hd hpF
    rw [show Nat.card F - (Nat.card F - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hpK : (p : F) ≠ 0 := CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card hp hpQ
  obtain ⟨z, hz⟩ := CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis.exists_comm_scalar hn hcomm
  have hzrel : A * B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin p) z := by
    rw [hz]
    group
  obtain ⟨b, hb⟩ := CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis.exists_pow_scalar hn hB
  obtain ⟨μ, hμ⟩ := CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis.exists_pow_scalar hn hA
  have hzp : z ^ p = 1 := CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis.comm_scalar_pow_eq_one hn hz hb
  have hz1 : z ≠ 1 := fun e => hAB (by rw [hz, e, map_one, one_mul])
  have hω : IsPrimitiveRoot z p := by
    have := orderOf_eq_prime hzp hz1
    rw [← this]
    exact IsPrimitiveRoot.orderOf z
  exact ⟨hpK, z, μ, b, hω, hzrel, hμ, hb⟩

theorem delta_facts {G : Type*} [Group G] [Finite G] {H : Subgroup G} {x y t : G} (hx : x ≠ 1) (hy : y ≠ 1)
    (ht : t ∈ localDeltaTwoIn H (Subgroup.closure {x, y})) :
    t ∈ pCoreOf 2 (H ⊓ Subgroup.centralizer ({x} : Set G)) ∧ t * x = x * t ∧ t * y = y * t ∧
      ∃ k : ℕ, t ^ (2 ^ k) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : ∀ d ∈ Subgroup.closure ({x, y} : Set G), d ≠ 1 →
      t ∈ pCoreOf 2 (H ⊓ Subgroup.centralizer ({d} : Set G)) := by
    intro d hd hd1
    unfold localDeltaTwoIn at ht
    simp only [Subgroup.mem_iInf] at ht
    exact ht d hd hd1
  have htx := hmem _ (Subgroup.subset_closure (by simp)) hx
  have hty := hmem _ (Subgroup.subset_closure (by simp)) hy
  refine ⟨htx, Subgroup.mem_centralizer_singleton_iff.1 (CFSG.LieType.BorelTits.pCoreOf_le 2 _ htx).2,
    Subgroup.mem_centralizer_singleton_iff.1 (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hty).2, ?_⟩
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _ ⟨t, htx⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem exists_scalar_of_commute_conj (hn : 3 ≤ p) {t : MulAut (projectiveSL p F)}
    {Θ : GL (Fin p) F →* GL (Fin p) F} (hΘ : ∀ g, t * conjAut p F g * t⁻¹ = conjAut p F (Θ g))
    {w : GL (Fin p) F} (hw : t * conjAut p F w = conjAut p F w * t) :
    ∃ l : Fˣ, Θ w = GeneralLinearGroup.scalar (Fin p) l * w := by
  have h1 : conjAut p F (Θ w * w⁻¹) = 1 := by
    rw [map_mul, map_inv, ← hΘ, hw, mul_inv_cancel_right, mul_inv_cancel]
  obtain ⟨l, hl⟩ := CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis.eq_scalar_of_conjAut_eq_one hn h1
  exact ⟨l, by rw [hl, inv_mul_cancel_right]⟩

theorem comm_of_scalar_mul {A : GL (Fin p) F} {Θ : GL (Fin p) F →* GL (Fin p) F} {l : Fˣ}
    (hl : Θ A = GeneralLinearGroup.scalar (Fin p) l * A) {w : GL (Fin p) F} (hw : w * A = A * w) :
    Θ w * A = A * Θ w := by
  have h1 : Θ w * Θ A = Θ A * Θ w := by rw [← map_mul, ← map_mul, hw]
  rw [hl] at h1
  have h2 : GeneralLinearGroup.scalar (Fin p) l * (Θ w * A) =
      GeneralLinearGroup.scalar (Fin p) l * (A * Θ w) := by
    calc GeneralLinearGroup.scalar (Fin p) l * (Θ w * A)
        = Θ w * (GeneralLinearGroup.scalar (Fin p) l * A) := by
          rw [← mul_assoc, GeneralLinearGroup.scalar_commute l (Θ w), mul_assoc]
      _ = GeneralLinearGroup.scalar (Fin p) l * A * Θ w := h1
      _ = GeneralLinearGroup.scalar (Fin p) l * (A * Θ w) := mul_assoc _ _ _
  exact mul_left_cancel h2

theorem card_filter_pow_eq_le (hp0 : 0 < p) (μ : Fˣ) [Fintype Fˣ] [DecidableEq Fˣ] :
    (Finset.univ.filter (fun a : Fˣ => a ^ p = μ)).card ≤ p := by
  rcases (Finset.univ.filter (fun a : Fˣ => a ^ p = μ)).eq_empty_or_nonempty with h | ⟨a0, ha0⟩
  · rw [h, Finset.card_empty]
    exact Nat.zero_le _
  · have ha0' : a0 ^ p = μ := (Finset.mem_filter.1 ha0).2
    calc (Finset.univ.filter (fun a : Fˣ => a ^ p = μ)).card
        = ((Finset.univ.filter (fun a : Fˣ => a ^ p = μ)).image (fun a => a0⁻¹ * a)).card :=
          (Finset.card_image_of_injective _ (mul_right_injective a0⁻¹)).symm
      _ ≤ (Finset.univ.filter (fun a : Fˣ => a ^ p = 1)).card := by
          apply Finset.card_le_card
          intro x hx
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
          have ha' : a ^ p = μ := (Finset.mem_filter.1 ha).2
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [mul_pow, ha', inv_pow, ha0', inv_mul_cancel]
      _ ≤ p := IsCyclic.card_pow_eq_one_le hp0

theorem three_mul_le_card [CharP F 2] (hpF : p ∣ Nat.card F - 1) (hQp : Nat.card F - 1 ≠ p) :
    3 * p ≤ Nat.card F - 1 := by
  obtain ⟨j, hj⟩ := hpF
  have hodd : Odd (Nat.card F - 1) := odd_card_sub_one_two
  rw [hj] at hodd hQp ⊢
  have hjodd : Odd j := (Nat.odd_mul.1 hodd).2
  have hj1 : j ≠ 1 := fun h => hQp (by rw [h, mul_one])
  obtain ⟨j', rfl⟩ := hjodd
  have : 1 ≤ j' := by omega
  nlinarith

theorem eq_one_of_mem_delta_theta0 [CharP F 2] (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1)
    {A B : GL (Fin p) F} (hAB : A * B ≠ B * A) (hA : conjAut p F A ^ p = 1) (hB : conjAut p F B ^ p = 1)
    (hcomm : conjAut p F A * conjAut p F B = conjAut p F B * conjAut p F A) (hA1 : conjAut p F A ≠ 1)
    (hB1 : conjAut p F B ≠ 1) {H : Subgroup (MulAut (projectiveSL p F))} (hH : innerAut (projectiveSL p F) ≤ H)
    {t : MulAut (projectiveSL p F)}
    (ht : t ∈ localDeltaTwoIn H (Subgroup.closure {conjAut p F A, conjAut p F B}))
    {X : GL (Fin p) F} {σ : F ≃+* F} (hteq : t = conjAut p F X * fieldAut p F σ) : t = 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype F := Fintype.ofFinite F
  have : Finite (projectiveSL p F) := finite_projectiveSL
  have hn : 3 ≤ p := by have := hp.two_le; omega
  have hp0 := hp.pos
  obtain ⟨hpK, z, μ, b, hω, hzrel, hμ, hb⟩ := heis_data hp hp2 hpF hAB hA hB hcomm
  obtain ⟨htA, hcA, hcB, k, hk'⟩ := delta_facts hA1 hB1 ht
  have hindA := linearIndependent_pow_of_heis hp0 hω hzrel hpK
  have hΘ : ∀ g, t * conjAut p F g * t⁻¹ = conjAut p F (theta0 X σ g) := fun g => by
    rw [hteq]
    exact conj_theta0 X σ g
  obtain ⟨l, hl⟩ := exists_scalar_of_commute_conj hn hΘ hcA
  obtain ⟨m, hm⟩ := exists_scalar_of_commute_conj hn hΘ hcB
  have hpres : ∀ w, w * A = A * w → theta0 X σ w * A = A * theta0 X σ w := fun w hw =>
    comm_of_scalar_mul hl hw
  have hσz : σ (z : F) = z := by
    have h1 : theta0 X σ (A * B * A⁻¹ * B⁻¹) = A * B * A⁻¹ * B⁻¹ := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hl, hm]
      exact commutator_central_mul (fun g => GeneralLinearGroup.scalar_commute l g)
        (fun g => GeneralLinearGroup.scalar_commute m g)
    rw [hzrel, theta0_scalar] at h1
    have h2 := CFSG.HardMathSupport.Timmesfeld.CrossChar.glScalar_injective hp0 h1
    simpa using congrArg Units.val h2
  have hM : (A : Matrix (Fin p) (Fin p) F) ^ p = Matrix.scalar (Fin p) (μ : F) := by
    have := congrArg Units.val hμ
    rwa [Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar] at this
  have hlA : (X : Matrix (Fin p) (Fin p) F) * (A : Matrix (Fin p) (Fin p) F).map σ *
      ((X⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = (l : F) • (A : Matrix (Fin p) (Fin p) F) := by
    rw [← coe_theta0, hl, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul]
  obtain ⟨hBA, -⟩ := B_conj_A hzrel
  have key : ∀ a : Fˣ, a ^ p ≠ μ → σ a = l * a := by
    intro a ha
    have ha' : (-(a : F)) ^ p ≠ μ := by
      rw [CharTwo.neg_eq]
      intro h
      exact ha (Units.ext (by rw [Units.val_pow_eq_pow_val, h]))
    let u : GL (Fin p) F := Matrix.nonsingInvUnit (Matrix.scalar (Fin p) (a : F) + (A : Matrix (Fin p) (Fin p) F))
      (isUnit_det_scalar_add_of_ne hM ha')
    have hu : ((u : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = Matrix.scalar (Fin p) (a : F) + A := rfl
    have huA : u * A = A * u := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hu, Matrix.add_mul, Matrix.mul_add,
        (Matrix.scalar_commute (a : F) (fun r => Commute.all _ r) (A : Matrix (Fin p) (Fin p) F)).eq]
    obtain ⟨hwA, hwi⟩ := commutator_test hzrel huA
    have hcw := commute_conjAut_two hp hp2 hpF hω hzrel hμ hb hH htA (theta0 X σ) hΘ hpres hwA hwi
    obtain ⟨ν, hν⟩ := exists_scalar_of_commute_conj hn hΘ hcw
    obtain ⟨U', hU'⟩ : ∃ U', U' = theta0 X σ u := ⟨_, rfl⟩
    have h1 : U' * B * U'⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin p) ν * (u * B * u⁻¹ * B⁻¹) := by
      rw [← hν, map_mul, map_mul, map_mul, map_inv, map_inv, hm, ← hU', comm_scalar_mul]
    obtain ⟨Y, hY⟩ : ∃ Y, Y = B * u * B⁻¹ := ⟨_, rfl⟩
    obtain ⟨Y', hY'⟩ : ∃ Y', Y' = B * U' * B⁻¹ := ⟨_, rfl⟩
    have h2 : U' * Y'⁻¹ = GeneralLinearGroup.scalar (Fin p) ν * u * Y⁻¹ := by
      have e1 : U' * B * U'⁻¹ * B⁻¹ = U' * Y'⁻¹ := by rw [hY']; group
      have e2 : u * B * u⁻¹ * B⁻¹ = u * Y⁻¹ := by rw [hY]; group
      rw [← e1, h1, e2, mul_assoc]
    have hU'A : U' * A = A * U' := by rw [hU']; exact hpres u huA
    have hYA : Y * A = A * Y := by rw [hY]; exact conj_mul_comm hzrel huA
    have hY'A : Y' * A = A * Y' := by rw [hY']; exact conj_mul_comm hzrel hU'A
    have hYY' : Y * Y' = Y' * Y := commute_of_commute_heis hp0 hω hzrel hpK hb hYA hY'A
    have h3 : U' * Y = GeneralLinearGroup.scalar (Fin p) ν * u * Y' := by
      calc U' * Y = (U' * Y'⁻¹) * (Y' * Y) := by group
        _ = (U' * Y'⁻¹) * (Y * Y') := by rw [hYY']
        _ = (GeneralLinearGroup.scalar (Fin p) ν * u * Y⁻¹) * (Y * Y') := by rw [h2]
        _ = GeneralLinearGroup.scalar (Fin p) ν * u * Y' := by group
    have hU'm : (U' : Matrix (Fin p) (Fin p) F) =
        Matrix.scalar (Fin p) (σ a) + (l : F) • (A : Matrix (Fin p) (Fin p) F) := by
      rw [hU', coe_theta0, hu, Matrix.map_add _ (map_add σ), Matrix.scalar_apply, Matrix.diagonal_map (map_zero σ),
        ← Matrix.scalar_apply, conj_scalar_add, hlA]
    have hYm : (Y : Matrix (Fin p) (Fin p) F) = Matrix.scalar (Fin p) (a : F) +
        ((z⁻¹ : Fˣ) : F) • (A : Matrix (Fin p) (Fin p) F) := by
      rw [hY, Units.val_mul, Units.val_mul, hu, conj_scalar_add, hBA]
    have hY'm : (Y' : Matrix (Fin p) (Fin p) F) = Matrix.scalar (Fin p) (σ a) +
        ((l : F) * ((z⁻¹ : Fˣ) : F)) • (A : Matrix (Fin p) (Fin p) F) := by
      rw [hY', Units.val_mul, Units.val_mul, hU'm, conj_scalar_add, Matrix.mul_smul, Matrix.smul_mul, hBA,
        smul_smul]
    have h4 := congrArg (fun g : GL (Fin p) F => (g : Matrix (Fin p) (Fin p) F)) h3
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at h4
    have hsmul : ∀ (c : F) (N : Matrix (Fin p) (Fin p) F), Matrix.scalar (Fin p) c * N = c • N := fun c N => by
      rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    rw [hU'm, hYm, hY'm, hu, hsmul, Matrix.smul_mul] at h4
    have hz1 : ((z⁻¹ : Fˣ) : F) ≠ 1 := by
      intro h
      have : z⁻¹ = 1 := Units.ext h
      exact hω.ne_one hp.one_lt (inv_eq_one.1 this)
    exact coeff_theta0 hindA hn (Units.ne_zero a) ((map_ne_zero σ).2 (Units.ne_zero a)) hz1 h4
  have hσ : σ = 1 := by
    refine RingEquiv.ext fun x => ?_
    show σ x = x
    by_cases hx : x = 0
    · rw [hx, map_zero]
    by_cases hQp : Nat.card F - 1 = p
    ·
      have hxp : x ^ p = 1 := by
        have := FiniteField.pow_card_sub_one_eq_one x hx
        rwa [← Nat.card_eq_fintype_card, hQp] at this
      have hω' : IsPrimitiveRoot (z : F) p := IsPrimitiveRoot.coe_units_iff.2 hω
      obtain ⟨i, -, hi⟩ := hω'.eq_pow_of_pow_eq_one hxp
      rw [← hi, map_pow, hσz]
    ·
      have h3p := three_mul_le_card hpF hQp
      have hcardU : Fintype.card Fˣ = Nat.card F - 1 := by
        rw [Fintype.card_units, Nat.card_eq_fintype_card]
      set y : Fˣ := Units.mk0 x hx with hy
      set S := Finset.univ.filter (fun a : Fˣ => a ^ p = μ) with hS
      have hScard : S.card ≤ p := card_filter_pow_eq_le hp0 μ
      have hT : (S ∪ S.image (fun a => y⁻¹ * a)).card < (Finset.univ : Finset Fˣ).card := by
        calc (S ∪ S.image (fun a => y⁻¹ * a)).card ≤ S.card + (S.image (fun a => y⁻¹ * a)).card :=
              Finset.card_union_le _ _
          _ ≤ p + p := add_le_add hScard (Finset.card_image_le.trans hScard)
          _ < (Finset.univ : Finset Fˣ).card := by rw [Finset.card_univ, hcardU]; omega
      obtain ⟨a, -, haT⟩ := Finset.exists_mem_notMem_of_card_lt_card hT
      have ha1 : a ^ p ≠ μ := fun h => haT (Finset.mem_union_left _ (by simp [hS, h]))
      have ha2 : (y * a) ^ p ≠ μ := fun h =>
        haT (Finset.mem_union_right _ (Finset.mem_image.2 ⟨y * a, by simp [hS, h], by group⟩))
      have k1 := key a ha1
      have k2 := key (y * a) ha2
      rw [Units.val_mul, map_mul, k1] at k2
      have hya : ((y : Fˣ) : F) = x := rfl
      rw [hya] at k2
      have hla : (l : F) * a ≠ 0 := mul_ne_zero (Units.ne_zero l) (Units.ne_zero a)
      have h5 : (σ x - x) * ((l : F) * a) = 0 := by linear_combination k2
      exact sub_eq_zero.1 ((mul_eq_zero.1 h5).resolve_right hla)
  rw [hσ, map_one, mul_one] at hteq
  rw [hteq] at hcA hcB hk' ⊢
  exact conjAut_eq_one_of_heis_two hp hp2 hpK hω hzrel hA hB hcA hcB hk'

theorem false_of_mem_delta_theta1 [CharP F 2] (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1)
    {A B : GL (Fin p) F} (hAB : A * B ≠ B * A) (hA : conjAut p F A ^ p = 1) (hB : conjAut p F B ^ p = 1)
    (hcomm : conjAut p F A * conjAut p F B = conjAut p F B * conjAut p F A) (hA1 : conjAut p F A ≠ 1)
    (hB1 : conjAut p F B ≠ 1) {H : Subgroup (MulAut (projectiveSL p F))} (hH : innerAut (projectiveSL p F) ≤ H)
    (hne : ¬(p = 3 ∧ Nat.card F = 4)) {t : MulAut (projectiveSL p F)}
    (ht : t ∈ localDeltaTwoIn H (Subgroup.closure {conjAut p F A, conjAut p F B}))
    {X : GL (Fin p) F} {σ : F ≃+* F} (hteq : t = conjAut p F X * fieldAut p F σ * dualAut p F) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype F := Fintype.ofFinite F
  have : Finite (projectiveSL p F) := finite_projectiveSL
  have hn : 3 ≤ p := by have := hp.two_le; omega
  have hp0 := hp.pos
  obtain ⟨hpK, z, μ, b, hω, hzrel, hμ, hb⟩ := heis_data hp hp2 hpF hAB hA hB hcomm
  obtain ⟨htA, hcA, hcB, -, -⟩ := delta_facts hA1 hB1 ht
  have hindA := linearIndependent_pow_of_heis hp0 hω hzrel hpK
  have hΘ : ∀ g, t * conjAut p F g * t⁻¹ = conjAut p F (theta1 X σ g) := fun g => by
    rw [hteq]
    exact conj_theta1 X σ g
  obtain ⟨l, hl⟩ := exists_scalar_of_commute_conj hn hΘ hcA
  obtain ⟨m, hm⟩ := exists_scalar_of_commute_conj hn hΘ hcB
  have hpres : ∀ w, w * A = A * w → theta1 X σ w * A = A * theta1 X σ w := fun w hw =>
    comm_of_scalar_mul hl hw
  have hz1 : z ≠ 1 := hω.ne_one hp.one_lt
  by_cases hQp : Nat.card F - 1 = p
  ·
    have hσz : σ (z : F) = ((z⁻¹ : Fˣ) : F) := by
      have h1 : theta1 X σ (A * B * A⁻¹ * B⁻¹) = A * B * A⁻¹ * B⁻¹ := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hl, hm]
        exact commutator_central_mul (fun g => GeneralLinearGroup.scalar_commute l g)
          (fun g => GeneralLinearGroup.scalar_commute m g)
      rw [hzrel, theta1_scalar] at h1
      have h2 := CFSG.HardMathSupport.Timmesfeld.CrossChar.glScalar_injective hp0 h1
      have h3 := congrArg Units.val h2
      simp only [Units.coe_map, MonoidHom.coe_coe] at h3
      rw [map_units_inv] at h3
      have h4 : (σ (z : F))⁻¹ = (z : F) := h3
      rw [Units.val_inv_eq_inv_val]
      exact inv_eq_iff_eq_inv.1 h4
    have hω' : IsPrimitiveRoot (z : F) p := IsPrimitiveRoot.coe_units_iff.2 hω
    have hinv : ∀ x : F, x ≠ 0 → σ x = x⁻¹ := by
      intro x hx
      have hxp : x ^ p = 1 := by
        have := FiniteField.pow_card_sub_one_eq_one x hx
        rwa [← Nat.card_eq_fintype_card, hQp] at this
      obtain ⟨i, -, hi⟩ := hω'.eq_pow_of_pow_eq_one hxp
      rw [← hi, map_pow, hσz, Units.val_inv_eq_inv_val, inv_pow]
    have hcube : ∀ x : Fˣ, x ^ 3 = 1 := by
      intro x
      by_cases hx1 : (x : F) = 1
      · rw [show x = 1 from Units.ext hx1, one_pow]
      have hx0 : (x : F) ≠ 0 := Units.ne_zero x
      have hx10 : (x : F) + 1 ≠ 0 := by
        intro h
        apply hx1
        have h2 : (x : F) = -1 := eq_neg_of_add_eq_zero_left h
        rw [h2, CharTwo.neg_eq]
      have h1 := hinv ((x : F) + 1) hx10
      rw [map_add, map_one, hinv _ hx0] at h1
      have e1 : ((x : F)⁻¹ + 1) * ((x : F) * ((x : F) + 1)) = ((x : F) + 1) ^ 2 := by
        rw [add_mul, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul, one_mul]
        ring
      have e2 : ((x : F) + 1)⁻¹ * ((x : F) * ((x : F) + 1)) = x := by
        rw [mul_comm ((x : F) + 1)⁻¹, mul_assoc, mul_inv_cancel₀ hx10, mul_one]
      have h2 : (x : F) ^ 2 + x + 1 = 0 := by
        have h3 : ((x : F)⁻¹ + 1) * ((x : F) * ((x : F) + 1)) =
            ((x : F) + 1)⁻¹ * ((x : F) * ((x : F) + 1)) := by rw [h1]
        rw [e1, e2] at h3
        linear_combination h3
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      linear_combination ((x : F) - 1) * h2
    have hle : Fintype.card Fˣ ≤ 3 := by
      have h1 := IsCyclic.card_pow_eq_one_le (α := Fˣ) (n := 3) (by norm_num)
      rwa [Finset.filter_true_of_mem (fun x _ => hcube x), Finset.card_univ] at h1
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hQp] at hle
    exact hne ⟨by omega, by omega⟩
  ·
    have h3p := three_mul_le_card hpF hQp
    have hcardU : Fintype.card Fˣ = Nat.card F - 1 := by
      rw [Fintype.card_units, Nat.card_eq_fintype_card]
    have hScard := card_filter_pow_eq_le hp0 μ
    have hlt : (Finset.univ.filter (fun a : Fˣ => a ^ p = μ)).card < (Finset.univ : Finset Fˣ).card := by
      rw [Finset.card_univ, hcardU]
      omega
    obtain ⟨a, -, haS⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have ha : a ^ p ≠ μ := fun h => haS (by simp [h])
    have hM : (A : Matrix (Fin p) (Fin p) F) ^ p = Matrix.scalar (Fin p) (μ : F) := by
      have := congrArg Units.val hμ
      rwa [Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar] at this
    have ha' : (-(a : F)) ^ p ≠ μ := by
      rw [CharTwo.neg_eq]
      intro h
      exact ha (Units.ext (by rw [Units.val_pow_eq_pow_val, h]))
    let u : GL (Fin p) F := Matrix.nonsingInvUnit (Matrix.scalar (Fin p) (a : F) + (A : Matrix (Fin p) (Fin p) F))
      (isUnit_det_scalar_add_of_ne hM ha')
    have hu : ((u : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = Matrix.scalar (Fin p) (a : F) + A := rfl
    have huA : u * A = A * u := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hu, Matrix.add_mul, Matrix.mul_add,
        (Matrix.scalar_commute (a : F) (fun r => Commute.all _ r) (A : Matrix (Fin p) (Fin p) F)).eq]
    obtain ⟨hwA, hwi⟩ := commutator_test hzrel huA
    have hcw := commute_conjAut_two hp hp2 hpF hω hzrel hμ hb hH htA (theta1 X σ) hΘ hpres hwA hwi
    obtain ⟨ν, hν⟩ := exists_scalar_of_commute_conj hn hΘ hcw
    obtain ⟨V, hV⟩ : ∃ V, V = theta1 X σ u⁻¹ := ⟨_, rfl⟩
    have hVu : theta1 X σ u = V⁻¹ := by rw [hV, map_inv, inv_inv]
    have h1 : V⁻¹ * B * V * B⁻¹ = GeneralLinearGroup.scalar (Fin p) ν * (u * B * u⁻¹ * B⁻¹) := by
      rw [← hν, map_mul, map_mul, map_mul, map_inv, map_inv, hm, hVu, comm_scalar_mul, inv_inv]
    obtain ⟨Y, hY⟩ : ∃ Y, Y = B * u * B⁻¹ := ⟨_, rfl⟩
    obtain ⟨Z, hZ⟩ : ∃ Z, Z = B * V * B⁻¹ := ⟨_, rfl⟩
    have h2 : V⁻¹ * Z = GeneralLinearGroup.scalar (Fin p) ν * u * Y⁻¹ := by
      have e1 : V⁻¹ * B * V * B⁻¹ = V⁻¹ * Z := by rw [hZ]; group
      have e2 : u * B * u⁻¹ * B⁻¹ = u * Y⁻¹ := by rw [hY]; group
      rw [← e1, h1, e2, mul_assoc]
    have hVA : V * A = A * V := by
      rw [hV]
      exact hpres u⁻¹ ((show Commute u A from huA).inv_left).eq
    have hVu' : V * u = u * V := commute_of_commute_heis hp0 hω hzrel hpK hb hVA huA
    have h3 : Z * Y = GeneralLinearGroup.scalar (Fin p) ν * (u * V) := by
      calc Z * Y = V * (V⁻¹ * Z) * Y := by group
        _ = V * (GeneralLinearGroup.scalar (Fin p) ν * u * Y⁻¹) * Y := by rw [h2]
        _ = V * GeneralLinearGroup.scalar (Fin p) ν * u := by group
        _ = GeneralLinearGroup.scalar (Fin p) ν * (V * u) := by
          rw [← GeneralLinearGroup.scalar_commute, mul_assoc]
        _ = GeneralLinearGroup.scalar (Fin p) ν * (u * V) := by rw [hVu']
    obtain ⟨hBA, hBAi⟩ := B_conj_A hzrel
    have hRA : (X : Matrix (Fin p) (Fin p) F) * ((A : Matrix (Fin p) (Fin p) F).map σ)ᵀ *
        ((X⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) =
          ((l⁻¹ : Fˣ) : F) • ((A⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
      have hscR : ∀ (c : F) (N : Matrix (Fin p) (Fin p) F), N * Matrix.scalar (Fin p) c = c • N := fun c N => by
        rw [← (Matrix.scalar_commute c (fun r => Commute.all _ r) N).eq, Matrix.scalar_apply,
          ← Matrix.smul_eq_diagonal_mul]
      rw [← coe_theta1_inv, map_inv, hl, _root_.mul_inv_rev, ← map_inv, Units.val_mul, GeneralLinearGroup.coe_scalar,
        hscR]
    have hVm : (V : Matrix (Fin p) (Fin p) F) = Matrix.scalar (Fin p) (σ a) +
        ((l⁻¹ : Fˣ) : F) • ((A⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
      rw [hV, coe_theta1_inv, hu, Matrix.map_add _ (map_add σ), Matrix.transpose_add, Matrix.scalar_apply,
        Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, ← Matrix.scalar_apply, conj_scalar_add, hRA]
    have hYm : (Y : Matrix (Fin p) (Fin p) F) = Matrix.scalar (Fin p) (a : F) +
        ((z⁻¹ : Fˣ) : F) • (A : Matrix (Fin p) (Fin p) F) := by
      rw [hY, Units.val_mul, Units.val_mul, hu, conj_scalar_add, hBA]
    have hZm : (Z : Matrix (Fin p) (Fin p) F) = Matrix.scalar (Fin p) (σ a) +
        (((l⁻¹ : Fˣ) : F) * (z : F)) • ((A⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
      rw [hZ, Units.val_mul, Units.val_mul, hVm, conj_scalar_add, Matrix.mul_smul, Matrix.smul_mul, hBAi,
        smul_smul]
    have h4 := congrArg (fun g : GL (Fin p) F => (g : Matrix (Fin p) (Fin p) F)) h3
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at h4
    have hsmul : ∀ (c : F) (N : Matrix (Fin p) (Fin p) F), Matrix.scalar (Fin p) c * N = c • N := fun c N => by
      rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    rw [hZm, hYm, hVm, hu, hsmul] at h4
    have hAiA : ((A⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * (A : Matrix (Fin p) (Fin p) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hzinv : ((z⁻¹ : Fˣ) : F) = (z : F)⁻¹ := Units.val_inv_eq_inv_val z
    rw [hzinv] at h4
    have h5 := coeff_theta1 hindA hn hAiA (Units.ne_zero a) ((map_ne_zero σ).2 (Units.ne_zero a))
      (Units.ne_zero _) (Units.ne_zero z) h4
    apply hz1
    have h6 : z ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, pow_two, h5, Units.val_one])
    have h7 := orderOf_dvd_of_pow_eq_one h6
    rw [hω.eq_orderOf.symm] at h7
    have := Nat.le_of_dvd (by norm_num) h7
    omega

theorem localDeltaTwoIn_eq_bot_two [CharP F 2] (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1)
    {A B : GL (Fin p) F} (hAB : A * B ≠ B * A) (hA : conjAut p F A ^ p = 1) (hB : conjAut p F B ^ p = 1)
    (hcomm : conjAut p F A * conjAut p F B = conjAut p F B * conjAut p F A) (hA1 : conjAut p F A ≠ 1)
    (hB1 : conjAut p F B ≠ 1) (hne : ¬(p = 3 ∧ Nat.card F = 4)) {H : Subgroup (MulAut (projectiveSL p F))}
    (hH : innerAut (projectiveSL p F) ≤ H) :
    localDeltaTwoIn H (Subgroup.closure {conjAut p F A, conjAut p F B}) = ⊥ := by
  have hn : 3 ≤ p := by have := hp.two_le; omega
  rw [eq_bot_iff]
  intro t ht
  rw [Subgroup.mem_bot]
  obtain ⟨X, σ, ε, hε, hteq⟩ := (automorphism_generation (K := F) hn).2 t
  interval_cases ε
  · rw [pow_zero, mul_one] at hteq
    exact eq_one_of_mem_delta_theta0 hp hp2 hpF hAB hA hB hcomm hA1 hB1 hH ht hteq
  · rw [pow_one] at hteq
    exact (false_of_mem_delta_theta1 hp hp2 hpF hAB hA hB hcomm hA1 hB1 hH hne ht hteq).elim

theorem eq_of_mem_delta_two [CharP F 2] (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1)
    {A B : GL (Fin p) F} (hAB : A * B ≠ B * A) (hA : conjAut p F A ^ p = 1) (hB : conjAut p F B ^ p = 1)
    (hcomm : conjAut p F A * conjAut p F B = conjAut p F B * conjAut p F A) (hA1 : conjAut p F A ≠ 1)
    (hB1 : conjAut p F B ≠ 1) {H : Subgroup (MulAut (projectiveSL p F))} (hH : innerAut (projectiveSL p F) ≤ H)
    {t₁ t₂ : MulAut (projectiveSL p F)}
    (h₁ : t₁ ∈ localDeltaTwoIn H (Subgroup.closure {conjAut p F A, conjAut p F B}))
    (h₂ : t₂ ∈ localDeltaTwoIn H (Subgroup.closure {conjAut p F A, conjAut p F B})) (h₁1 : t₁ ≠ 1)
    (h₂1 : t₂ ≠ 1) : t₁ = t₂ := by
  have hn : 3 ≤ p := by have := hp.two_le; omega
  have type1 : ∀ t ∈ localDeltaTwoIn H (Subgroup.closure {conjAut p F A, conjAut p F B}), t ≠ 1 →
      ∃ (X : GL (Fin p) F) (σ : F ≃+* F), t = conjAut p F X * fieldAut p F σ * dualAut p F := by
    intro t ht ht1
    obtain ⟨X, σ, ε, hε, hteq⟩ := (automorphism_generation (K := F) hn).2 t
    interval_cases ε
    · rw [pow_zero, mul_one] at hteq
      exact (ht1 (eq_one_of_mem_delta_theta0 hp hp2 hpF hAB hA hB hcomm hA1 hB1 hH ht hteq)).elim
    · rw [pow_one] at hteq
      exact ⟨X, σ, hteq⟩
  obtain ⟨X₁, σ₁, e₁⟩ := type1 t₁ h₁ h₁1
  obtain ⟨X₂, σ₂, e₂⟩ := type1 t₂ h₂ h₂1
  have hmem : t₁ * t₂⁻¹ ∈ localDeltaTwoIn H (Subgroup.closure {conjAut p F A, conjAut p F B}) :=
    Subgroup.mul_mem _ h₁ (Subgroup.inv_mem _ h₂)
  have h1 := (standard_automorphism_transport (K := F) (n := p)).2.2.1 (σ₁ * σ₂⁻¹) X₂⁻¹
  have hprod : t₁ * t₂⁻¹ = conjAut p F (X₁ * GeneralLinearGroup.map ((σ₁ * σ₂⁻¹ : F ≃+* F) : F →+* F) X₂⁻¹) *
      fieldAut p F (σ₁ * σ₂⁻¹) := by
    calc t₁ * t₂⁻¹ = conjAut p F X₁ * fieldAut p F σ₁ * (fieldAut p F σ₂)⁻¹ * (conjAut p F X₂)⁻¹ := by
          rw [e₁, e₂]
          group
      _ = conjAut p F X₁ * fieldAut p F (σ₁ * σ₂⁻¹) * conjAut p F X₂⁻¹ := by
          rw [map_mul, map_inv, map_inv]
          group
      _ = conjAut p F X₁ * (fieldAut p F (σ₁ * σ₂⁻¹) * conjAut p F X₂⁻¹ * (fieldAut p F (σ₁ * σ₂⁻¹))⁻¹) *
            fieldAut p F (σ₁ * σ₂⁻¹) := by group
      _ = _ := by rw [h1, map_mul (conjAut p F)]
  have := eq_one_of_mem_delta_theta0 hp hp2 hpF hAB hA hB hcomm hA1 hB1 hH hmem hprod
  exact mul_inv_eq_one.1 this

end Delta

section Planes

theorem linear_plane {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpF : p ∣ Nat.card F - 1) {D : Subgroup (MulAut (projectiveSL p F))} (hD : IsElemAbelian p D)
    (hDc : Nat.card D = p ^ 2) (hnb : ¬ IsLocallyOTwoBalanced p 2 D) :
    ∃ A B : GL (Fin p) F, Subgroup.closure {conjAut p F A, conjAut p F B} = D ∧ A * B ≠ B * A ∧
      conjAut p F A ^ p = 1 ∧ conjAut p F B ^ p = 1 ∧
      conjAut p F A * conjAut p F B = conjAut p F B * conjAut p F A ∧ conjAut p F A ≠ 1 ∧ conjAut p F B ≠ 1 ∧
      conjAut p F A ∈ innerAut (projectiveSL p F) ∧ conjAut p F B ∈ innerAut (projectiveSL p F) ∧
      ∃ H : Subgroup (MulAut (projectiveSL p F)), innerAut (projectiveSL p F) ≤ H ∧ localDeltaTwoIn H D ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hn : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨H, hH, hDH, hΔ⟩ := exists_delta_of_not_balanced hp hDc hnb
  have hΔ' : localDeltaIn p H D ≠ ⊥ := fun h0 =>
    hΔ (le_bot_iff.1 ((BalanceFromYS.localDeltaTwoIn_le_localDeltaIn hp hp2 H D).trans h0.le))
  have hDl : D ≤ linearAutGroup p F := by
    by_contra hDl
    exact hΔ' (CFSG.HardMathSupport.Timmesfeld.CrossChar.localDeltaIn_eq_bot_of_not_le_linearAutGroup
      hn hp hp2 hpF hD hDl hH)
  have hDr : D ≤ (conjAut p F).range := fun d hd => by
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1 (hDl hd)
    exact ⟨A, hA⟩
  obtain ⟨x, hx, y, hy, hx1, hyx, hgen⟩ :=
    CFSG.HardMathSupport.Timmesfeld.LocalTwo.exists_gen_pair hp hD hDc
  obtain ⟨A0, rfl⟩ := hDr hx
  obtain ⟨B0, rfl⟩ := hDr hy
  have hy1 : conjAut p F B0 ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
  have hcomm : conjAut p F A0 * conjAut p F B0 = conjAut p F B0 * conjAut p F A0 :=
    congrArg Subtype.val (hD.1.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
  have hAB : A0 * B0 ≠ B0 * A0 := by
    intro hAB
    apply hΔ'
    rw [← hgen]
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.diagAbelianPlaneBalance_holds p F hn p hp hp2 hpF dvd_rfl
      A0 B0 hAB (hD.2 _ hx) (hD.2 _ hy) hx1 hyx H hH (hgen ▸ hDH)
  have hA := hD.2 _ hx
  have hB := hD.2 _ hy
  have hAi : conjAut p F A0 ∈ innerAut (projectiveSL p F) := by
    by_contra hout
    exact hΔ (hgen ▸ localDeltaTwoIn_eq_bot_linear_outer hp hp2 hpF hAB hA hB hcomm hx1 hy1 hout hH)
  have hBi : conjAut p F B0 ∈ innerAut (projectiveSL p F) := by
    by_contra hout
    apply hΔ
    rw [← hgen, Set.pair_comm]
    exact localDeltaTwoIn_eq_bot_linear_outer hp hp2 hpF (Ne.symm hAB) hB hA hcomm.symm hy1 hx1 hout hH
  exact ⟨A0, B0, hgen, hAB, hA, hB, hcomm, hx1, hy1, hAi, hBi, H, hH, hΔ⟩

theorem unitary_balanced {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hne : ¬(p = 3 ∧ ℓ ^ f = 2)) (hpq : p ∣ ℓ ^ f + 1)
    {D : Subgroup (MulAut (primeFormP h (idGram K p)))} (hD : IsElemAbelian p D)
    (hDc : Nat.card D = p ^ 2) : IsLocallyOTwoBalanced p 2 D := by
  have := h.finite
  haveI : Fact p.Prime := ⟨hp⟩
  have hn : 3 ≤ p := by have := hp.two_le; omega
  by_contra hnb
  obtain ⟨H, hH, hDH, hΔ⟩ := exists_delta_of_not_balanced hp hDc hnb
  have hΔ' : localDeltaIn p H D ≠ ⊥ := fun h0 =>
    hΔ (le_bot_iff.1 ((BalanceFromYS.localDeltaTwoIn_le_localDeltaIn hp hp2 H D).trans h0.le))
  by_cases h8 : p = 3 ∧ ℓ ^ f = 8
  · obtain ⟨rfl, h8'⟩ := h8
    obtain ⟨hl2, hf3⟩ := CFSG.HardMathSupport.Solomon.Coordinator.w3_pp_eq_eight h.prime h8'
    exact hΔ' (CFSG.HardMathSupport.Solomon.Coordinator.u38_isLocallyBalancedAbs' h hl2 hf3 D hD hDc H hH hDH)
  have hDl : D ≤ primeFormD h (idGram K p) := by
    by_contra hDl
    exact hΔ' (CFSG.HardMathSupport.Timmesfeld.CrossChar.localDeltaIn_eq_bot_of_not_le_primeFormD h hn hne hp
      hp2 hpq (CFSG.HardMathSupport.Solomon.Coordinator.not_three_pow_div_eq_two h hne h8 hD hDl) hD hDl hH)
  have hDr : D ≤ (primeFormConjHom h (idGram K p)).range := hDl
  obtain ⟨x, hx, y, hy, hx1, hyx, hgen⟩ :=
    CFSG.HardMathSupport.Timmesfeld.LocalTwo.exists_gen_pair hp hD hDc
  obtain ⟨A0, rfl⟩ := hDr hx
  obtain ⟨B0, rfl⟩ := hDr hy
  have hy1 : primeFormConjHom h (idGram K p) B0 ≠ 1 := fun h' => hyx (h' ▸ Subgroup.one_mem _)
  have hcomm : primeFormConjHom h (idGram K p) A0 * primeFormConjHom h (idGram K p) B0 =
      primeFormConjHom h (idGram K p) B0 * primeFormConjHom h (idGram K p) A0 :=
    congrArg Subtype.val (hD.1.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
  have hq3 := CFSG.HardMathSupport.Solomon.Coordinator.three_lt_of_dvd_add_one h hp hp2 hne hpq
  by_cases hAB : A0 * B0 = B0 * A0
  · apply hΔ'
    rw [← hgen]
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.localDeltaIn_eq_bot_of_unitary_plane hn hne hq3 hp hp2 hpq
      hAB (hD.2 _ hx) (hD.2 _ hy) hx1 hyx hH
  · exact hΔ (hgen ▸ localDeltaTwoIn_eq_bot_unitary_heis h hp hp2 hne hpq hAB (hD.2 _ hx) (hD.2 _ hy) hcomm hx1
      hy1 H)

end Planes

section LpC

theorem le_innerAut_of_map {Y M : Type*} [Group Y] [Group M] (hY : commutator Y = ⊤)
    (ε : (Y ⧸ Subgroup.center Y) ≃* M) {B : Subgroup (MulAut Y)} (hB : B.map (modelHom ε) ≤ innerAut M) :
    B ≤ innerAut Y := by
  intro b hb
  obtain ⟨c, hc, hcb⟩ := innerAut_le_map_modelHom ε (hB ⟨b, hb, rfl⟩)
  rw [← modelHom_injective hY ε hcb]
  exact hc

theorem input19_16LpC_holds : BalanceFromYS.Input19_16LpC := by
  intro p hp hp2 K _ _ hq _ hL B hB hBc hnb
  obtain ⟨idx, hidx, ⟨e⟩⟩ := hL
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
  obtain ⟨d, hv⟩ := idx
  change CFSG.HardMathSupport.Timmesfeld.LocalTwo.IsLpEpsIndex (m + 1) d at hidx
  have hY : commutator K = ⊤ := hq.1
  have : Finite (K ⧸ Subgroup.center K) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  rcases hidx with ⟨Q, hd, hQ⟩ | ⟨Q, hd, hQ⟩
  · simp only [Nat.add_sub_cancel] at hd
    subst hd
    have : Fact Q.p.Prime := ⟨Q.prime_p⟩
    have hF : Nat.card (GaloisField Q.p Q.exponent) = Q.p ^ Q.exponent :=
      GaloisField.card _ _ Q.exponent_pos.ne'
    have hpF : m + 1 ∣ Nat.card (GaloisField Q.p Q.exponent) - 1 :=
      CFSG.HardMathSupport.Solomon.Coordinator.dvd_card_galoisField_sub_one hp.one_lt Q hQ
    let θ : (K ⧸ Subgroup.center K) ≃* StatedProj (StatedSL (m + 1) (GaloisField Q.p Q.exponent)) :=
      (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m Q hv)).trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (m + 1) _)
    let ε := θ.trans (statedProjEquivProjectiveSL (m + 1) (GaloisField Q.p Q.exponent))
    have : Finite (projectiveSL (m + 1) (GaloisField Q.p Q.exponent)) := Finite.of_equiv _ ε.toEquiv
    have hD : IsElemAbelian (m + 1) (B.map (modelHom ε)) := hB.map _
    have hDc : Nat.card (B.map (modelHom ε)) = (m + 1) ^ 2 := by
      rw [Subgroup.card_map_of_injective (modelHom_injective hY ε), hBc]
    obtain ⟨A0, B0, hgen, -, -, -, -, -, -, hAi, hBi, -⟩ :=
      linear_plane hp hp2 hpF hD hDc (not_balanced_modelHom hY ε hnb)
    refine ⟨⟨Q.p ^ Q.exponent, by rw [← hF]; exact hpF,
      GaloisField Q.p Q.exponent, inferInstance, inferInstance, hF, ⟨θ⟩⟩, le_innerAut_of_map hY ε ?_⟩
    rw [← hgen, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hAi
    · exact hBi
  · simp only [Nat.add_sub_cancel] at hd
    subst hd
    exfalso
    have : Fact Q.p.Prime := ⟨Q.prime_p⟩
    obtain ⟨⟨hℓ, hf, -, hq'⟩, F, _, _, hK, ⟨eT⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m Q hv e
    have h : UnitaryFieldData Q.p Q.exponent F := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    have hne : ¬(m + 1 = 3 ∧ Q.p ^ Q.exponent = 2) := fun h2 => hq' (by rw [h2.1, h2.2])
    have hpq : m + 1 ∣ Q.p ^ Q.exponent + 1 := by
      rw [← TauCeti.PrimePower.card_def]
      exact Nat.dvd_of_mod_eq_zero hQ
    have hn1 : 1 ≤ m + 1 := by omega
    let ε := eT.trans (statedProjEquivPrimeFormP h hn1)
    have hD : IsElemAbelian (m + 1) (B.map (modelHom ε)) := hB.map _
    have hDc : Nat.card (B.map (modelHom ε)) = (m + 1) ^ 2 := by
      rw [Subgroup.card_map_of_injective (modelHom_injective hY ε), hBc]
    exact not_balanced_modelHom hY ε hnb (unitary_balanced h hp hp2 hne hpq hD hDc)

end LpC

section Fixed

theorem exists_fixed_pGroup {Y : Type*} [Group Y] [Finite Y] {r : ℕ} [Fact r.Prime]
    (hZ : IsPGroup r (Subgroup.center Y)) {B : Subgroup (MulAut Y)} (hBc : Nat.card B = r ^ 2)
    (hBi : B ≤ innerAut Y) {u : MulAut Y} (hu : ∀ b ∈ B, u * b = b * u) :
    ∃ P : Subgroup Y, IsPGroup r P ∧ r ^ 2 ∣ Nat.card P ∧ ∀ x ∈ P, u x = x := by
  classical
  set W : Subgroup Y := B.comap (MulAut.conj : Y →* MulAut Y) with hW
  have hcent : ∀ y ∈ W, y⁻¹ * u y ∈ Subgroup.center Y := by
    intro y hy
    have h1 := hu _ hy
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 := congrArg (fun φ : MulAut Y => φ (u.symm g)) h1
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
    calc g * (y⁻¹ * u y) = y⁻¹ * (y * g * y⁻¹) * u y := by group
      _ = y⁻¹ * (u y * g * (u y)⁻¹) * u y := by rw [h2]
      _ = y⁻¹ * u y * g := by group
  let zh : W →* Subgroup.center Y :=
    { toFun := fun y => ⟨(y : Y)⁻¹ * u y, hcent y y.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun y y' => by
        apply Subtype.ext
        show ((y : Y) * y')⁻¹ * u ((y : Y) * y') = ((y : Y)⁻¹ * u y) * ((y' : Y)⁻¹ * u y')
        have hc := Subgroup.mem_center_iff.1 (hcent y y.2) ((y' : Y)⁻¹)
        rw [map_mul]
        calc ((y : Y) * y')⁻¹ * (u y * u y') = (y' : Y)⁻¹ * ((y : Y)⁻¹ * u y) * u y' := by group
          _ = ((y : Y)⁻¹ * u y) * (y' : Y)⁻¹ * u y' := by rw [hc]
          _ = ((y : Y)⁻¹ * u y) * ((y' : Y)⁻¹ * u y') := by group }
  have hzh : ∀ y : W, ((zh y : Subgroup.center Y) : Y) = (y : Y)⁻¹ * u y := fun y => rfl
  let φ : W →* B := ((MulAut.conj : Y →* MulAut Y).comp W.subtype).codRestrict B (fun w => w.2)
  have hφ : Function.Surjective φ := by
    rintro ⟨b, hb⟩
    obtain ⟨y, rfl⟩ := hBi hb
    exact ⟨⟨y, hb⟩, rfl⟩
  have hcard1 : Nat.card φ.ker * Nat.card B = Nat.card W := Subgroup.card_ker_mul_card_of_surjective hφ
  have hcard2 : Nat.card zh.ker * Nat.card zh.range = Nat.card W := Subgroup.card_ker_mul_card_range zh
  have hle1 : Nat.card zh.range ≤ Nat.card (Subgroup.center Y) := Subgroup.card_le_card_group zh.range
  have hconj1 : ∀ z ∈ Subgroup.center Y, MulAut.conj z = 1 := by
    intro z hz
    ext g
    rw [MulAut.conj_apply, MulAut.one_apply, ← Subgroup.mem_center_iff.1 hz g, mul_inv_cancel_right]
  have hzW : ∀ z ∈ Subgroup.center Y, z ∈ W := fun z hz => by
    show MulAut.conj z ∈ B
    rw [hconj1 z hz]
    exact B.one_mem
  have hle2 : Nat.card (Subgroup.center Y) ≤ Nat.card φ.ker := by
    refine Nat.card_le_card_of_injective
      (fun z => (⟨⟨z, hzW z z.2⟩, ?_⟩ : φ.ker)) ?_
    · rw [MonoidHom.mem_ker]
      apply Subtype.ext
      exact hconj1 z z.2
    · intro z z' h
      have := congrArg (fun w : φ.ker => ((w : W) : Y)) h
      exact Subtype.ext this
  have hge : r ^ 2 ≤ Nat.card zh.ker := by
    have hpos : 0 < Nat.card zh.range := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card zh.ker * Nat.card zh.range < r ^ 2 * Nat.card φ.ker :=
      calc Nat.card zh.ker * Nat.card zh.range < r ^ 2 * Nat.card zh.range := Nat.mul_lt_mul_of_pos_right hlt hpos
        _ ≤ r ^ 2 * Nat.card φ.ker := Nat.mul_le_mul_left _ (hle1.trans hle2)
    rw [hcard2, ← hcard1, hBc, mul_comm] at h1
    exact lt_irrefl _ h1
  have hWr : IsPGroup r W := by
    intro w
    have hb : MulAut.conj (w : Y) ∈ B := w.2
    have hBr : IsPGroup r B := IsPGroup.of_card hBc
    obtain ⟨k1, hk1⟩ := hBr ⟨_, hb⟩
    have h1 : MulAut.conj ((w : Y) ^ (r ^ k1)) = 1 := by
      have := congrArg Subtype.val hk1
      simpa [map_pow] using this
    have h2 : (w : Y) ^ (r ^ k1) ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h3 := congrArg (fun φ : MulAut Y => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc g * (w : Y) ^ (r ^ k1) = ((w : Y) ^ (r ^ k1) * g * ((w : Y) ^ (r ^ k1))⁻¹) * (w : Y) ^ (r ^ k1) := by
            rw [h3]
        _ = (w : Y) ^ (r ^ k1) * g := by group
    obtain ⟨k2, hk2⟩ := hZ ⟨_, h2⟩
    refine ⟨k1 + k2, Subtype.ext ?_⟩
    have h4 := congrArg Subtype.val hk2
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h4
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul, h4]
  refine ⟨zh.ker.map W.subtype, (hWr.to_subgroup zh.ker).map _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective W.subtype_injective]
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hWr.to_subgroup zh.ker)
    rw [hn] at hge ⊢
    have hr1 : 1 < r := (Fact.out : r.Prime).one_lt
    exact pow_dvd_pow r ((Nat.pow_le_pow_iff_right hr1).1 hge)
  · rintro _ ⟨y, hy, rfl⟩
    have h1 := congrArg Subtype.val ((MonoidHom.mem_ker).1 hy)
    rw [hzh] at h1
    simp only [OneMemClass.coe_one] at h1
    show u y = y
    rw [inv_mul_eq_one] at h1
    exact h1.symm

end Fixed

section TwoLp

set_option linter.unusedSectionVars false


open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple ambiguousChev)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieSylowExponent)

theorem char_two_of_chev {m : ℕ} (hp : (m + 1).Prime) (hp2 : m + 1 ≠ 2) {S : Type} [Group S]
    (hchev : IsChevSimple 2 S) (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A m Q).Valid)
    (hQ : Q.card % (m + 1) = 1) (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.A m Q, hv⟩).Group) : Q.p = 2 := by
  have hO : LieOrderFormulasInput := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  have : Fact Q.p.Prime := ⟨Q.prime_p⟩
  have hX : CFSG.Blueprint.LieModel S .PSL (m + 1) Q.p Q.exponent :=
    CFSG.Blueprint.LieModel.of_mulEquiv e.symm
      (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
        (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_typeA m Q hv))
  have hadm := hX.admissible
  have hp3 : 3 ≤ m + 1 := by have := hp.two_le; omega
  have hsyl : lieSylowExponent .PSL (m + 1) = (m + 1) * (m + 1 - 1) / 2 := rfl
  by_contra hQ2
  rcases hchev with hc | hc
  · obtain ⟨-, -, t', n', f', hY⟩ := CrossCharOdd.lie_cases hc
    rcases CFSG.SeitzReduction.CrossChar.crossChar_arith hY.admissible hadm hQ2 (hO S _ _ _ _ hY.admissible hY).2.1
        (hO S _ _ _ _ hadm hX).2.1 with ⟨-, -, -, -, h, -⟩ | ⟨-, -, -, -, h, -⟩ | ⟨-, -, -, h, -⟩
    · omega
    · omega
    · exact absurd h (by decide)
  · obtain ⟨i, hi, ⟨e'⟩⟩ := hc
    cases i with
    | cyclic _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
    | alternating n hn =>
      have h5 : 5 ≤ n := by
        rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
      exact (AltFacts4.inputAltNotLie_holds n ⟨.A m Q, hv⟩ h5).false (e'.symm.trans e)
    | lie d =>
      obtain ⟨d1, hv'⟩ := d
      cases d1 with
      | A k q' =>
        rcases k with _ | _ | k
        · simp [ambiguousChev] at hi
        ·
          have h7 : q'.card = 7 := by simpa [ambiguousChev] using hi
          obtain ⟨hq7, hq1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : (7 : ℕ).Prime)).1
            (by rw [← TauCeti.PrimePower.card_def]; exact h7)
          have hY7 : CFSG.Blueprint.LieModel S .PSL (0 + 1 + 1) q'.p q'.exponent :=
            CFSG.Blueprint.LieModel.of_mulEquiv e'.symm
              (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
                (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_typeA (0 + 1) q' hv'))
          rw [hq7, hq1] at hY7
          have h7Q := CFSG.ComponentClassification.GS82PumpInputs.oddLieCharUnique_holds S .PSL (m + 1) Q.p
            Q.exponent .PSL (0 + 1 + 1) 7 1 hQ2 (by norm_num) hX hY7
          have s1 := (hO S _ _ _ _ hadm hX).2.2
          have s2 := (hO S _ _ _ _ hY7.admissible hY7).2.2
          rw [h7Q] at s1
          rw [s1] at s2
          have e2 : lieSylowExponent .PSL (0 + 1 + 1) * 1 = 1 := by decide
          rw [e2, hsyl] at s2
          obtain ⟨-, h⟩ := eq_three_of_sylow_le_six hp hp3 hadm.2.1 (by norm_num) s2
          omega
        · simp [ambiguousChev] at hi
      | twistedA k q' =>
        rcases k with _ | _ | _ | _ | k
        · simp [ambiguousChev] at hi
        · simp [ambiguousChev] at hi
        ·
          have h3 : q'.card = 3 := by simpa [ambiguousChev] using hi
          obtain ⟨hq3, hq1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).1
            (by rw [← TauCeti.PrimePower.card_def]; exact h3)
          have hY3 : CFSG.Blueprint.LieModel S .PSU (0 + 1 + 1 + 1) q'.p q'.exponent :=
            CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
              (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_of_classical
                (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA (0 + 1 + 1) q' hv' e'))
          rw [hq3, hq1] at hY3
          have h3Q := CFSG.ComponentClassification.GS82PumpInputs.oddLieCharUnique_holds S .PSL (m + 1) Q.p
            Q.exponent .PSU (0 + 1 + 1 + 1) 3 1 hQ2 (by norm_num) hX hY3
          have s1 := (hO S _ _ _ _ hadm hX).2.2
          have s2 := (hO S _ _ _ _ hY3.admissible hY3).2.2
          rw [h3Q] at s1
          rw [s1] at s2
          have e2 : lieSylowExponent .PSU (0 + 1 + 1 + 1) * 1 = 3 := by decide
          rw [e2, hsyl] at s2
          obtain ⟨hm3, hk⟩ := eq_three_of_sylow_le_six hp hp3 hadm.2.1 (by norm_num) s2
          have hQe : Q.exponent = 1 := by omega
          have hQc : Q.card = 3 := by rw [TauCeti.PrimePower.card_def, h3Q, hQe, pow_one]
          rw [hQc, hm3] at hQ
          norm_num at hQ
        · simp [ambiguousChev] at hi
        · simp [ambiguousChev] at hi
      | _ => simp [ambiguousChev] at hi

theorem input19_16_twoLp_holds : BalanceFromYS.Input19_16_twoLp := by
  intro p hp hp2 Y _ _ hY hO hchev hL B' hB'el hB'c hnb
  obtain ⟨idx, hidx, ⟨e⟩⟩ := hL
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
  obtain ⟨d, hv⟩ := idx
  change CFSG.HardMathSupport.Timmesfeld.LocalTwo.IsLpEpsIndex (m + 1) d at hidx
  have hYc : commutator Y = ⊤ := hY.1
  have : Finite (Y ⧸ Subgroup.center Y) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  rcases hidx with ⟨Q, hd, hQ⟩ | ⟨Q, hd, hQ⟩
  · simp only [Nat.add_sub_cancel] at hd
    subst hd
    have : Fact Q.p.Prime := ⟨Q.prime_p⟩
    have hQ2 : Q.p = 2 := char_two_of_chev hp hp2 hchev Q hv hQ e
    have hchar : CharP (GaloisField Q.p Q.exponent) 2 := by
      rw [← hQ2]
      infer_instance
    have hF : Nat.card (GaloisField Q.p Q.exponent) = Q.p ^ Q.exponent :=
      GaloisField.card _ _ Q.exponent_pos.ne'
    have hpF : m + 1 ∣ Nat.card (GaloisField Q.p Q.exponent) - 1 :=
      CFSG.HardMathSupport.Solomon.Coordinator.dvd_card_galoisField_sub_one hp.one_lt Q hQ
    let θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSL (m + 1) (GaloisField Q.p Q.exponent)) :=
      (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m Q hv)).trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (m + 1) _)
    let ε := θ.trans (statedProjEquivProjectiveSL (m + 1) (GaloisField Q.p Q.exponent))
    have : Finite (projectiveSL (m + 1) (GaloisField Q.p Q.exponent)) := Finite.of_equiv _ ε.toEquiv
    have hD : IsElemAbelian (m + 1) (B'.map (modelHom ε)) := hB'el.map _
    have hDc : Nat.card (B'.map (modelHom ε)) = (m + 1) ^ 2 := by
      rw [Subgroup.card_map_of_injective (modelHom_injective hYc ε), hB'c]
    obtain ⟨A0, B0, hgen, hAB, hA, hB, hcomm, hA1, hB1, hAi, hBi, H0, hH0, hΔ0⟩ :=
      linear_plane hp hp2 hpF hD hDc (not_balanced_modelHom hYc ε hnb)
    have h34 : m + 1 = 3 ∧ Nat.card (GaloisField Q.p Q.exponent) = 4 := by
      by_contra hne
      exact hΔ0 (hgen ▸ localDeltaTwoIn_eq_bot_two hp hp2 hpF hAB hA hB hcomm hA1 hB1 hne hH0)
    obtain ⟨h3, h4⟩ := h34
    have hinn : B' ≤ innerAut Y := by
      refine le_innerAut_of_map hYc ε ?_
      rw [← hgen, Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hAi
      · exact hBi
    obtain rfl : m = 2 := by omega
    refine ⟨rfl, ⟨GaloisField Q.p Q.exponent, inferInstance, inferInstance, h4, ⟨θ⟩⟩, hinn, fun H hH hΔ => ?_⟩
    have hinj := modelHom_injective hYc ε
    have hH' : innerAut (projectiveSL (2 + 1) (GaloisField Q.p Q.exponent)) ≤ H.map (modelHom ε) :=
      (innerAut_le_map_modelHom ε).trans (Subgroup.map_mono hH)
    have hmap := Inputs123a.map_localDeltaTwoIn_le (modelHom ε) hinj H B'
    have huniq : ∀ u₁ ∈ localDeltaTwoIn H B', ∀ u₂ ∈ localDeltaTwoIn H B', u₁ ≠ 1 → u₂ ≠ 1 → u₁ = u₂ := by
      intro u₁ hu₁ u₂ hu₂ hu₁1 hu₂1
      apply hinj
      have m1 := hmap ⟨u₁, hu₁, rfl⟩
      have m2 := hmap ⟨u₂, hu₂, rfl⟩
      rw [← hgen] at m1 m2
      exact eq_of_mem_delta_two hp hp2 hpF hAB hA hB hcomm hA1 hB1 hH' m1 m2
        (fun h => hu₁1 (hinj (h.trans (map_one _).symm))) (fun h => hu₂1 (hinj (h.trans (map_one _).symm)))
    obtain ⟨u, hu, hu1⟩ : ∃ u ∈ localDeltaTwoIn H B', u ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hΔ (eq_bot_iff.2 fun x hx => (Subgroup.mem_bot).2 (hcon x hx))
    have hΔu : localDeltaTwoIn H B' = Subgroup.zpowers u := by
      apply le_antisymm
      · intro x hx
        by_cases hx1 : x = 1
        · rw [hx1]
          exact Subgroup.one_mem _
        · rw [huniq x hx u hu hx1 hu1]
          exact Subgroup.mem_zpowers u
      · rw [Subgroup.zpowers_le]
        exact hu
    have hinv : u⁻¹ = u := huniq _ (Subgroup.inv_mem _ hu) u hu (inv_ne_one.2 hu1) hu1
    have hsq : u ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← hinv]
      exact inv_mul_cancel u
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf u = 2 := orderOf_eq_prime hsq hu1
    refine ⟨u, ⟨hord, ?_⟩, hΔu⟩
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hZ : IsPGroup 3 (Subgroup.center Y) :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltFacts2.isPGroup_center_of_core_eq_bot hp hO
    have hucomm : ∀ b ∈ B', u * b = b * u := by
      intro b hb
      by_cases hb1 : b = 1
      · rw [hb1, mul_one, one_mul]
      · have h1 : u ∈ pCoreOf 2 (H ⊓ Subgroup.centralizer ({b} : Set (MulAut Y))) := by
          have h2 := hu
          unfold localDeltaTwoIn at h2
          simp only [Subgroup.mem_iInf] at h2
          exact h2 b hb hb1
        exact Subgroup.mem_centralizer_singleton_iff.1 (CFSG.LieType.BorelTits.pCoreOf_le 2 _ h1).2
    obtain ⟨P, hP, h9, hfix⟩ := exists_fixed_pGroup hZ (r := 3) (by simpa using hB'c) hinn hucomm
    exact ⟨P, hP, by simpa using h9, hfix⟩
  · simp only [Nat.add_sub_cancel] at hd
    subst hd
    exfalso
    have : Fact Q.p.Prime := ⟨Q.prime_p⟩
    obtain ⟨⟨hℓ, hf, -, hq'⟩, K, _, _, hK, ⟨eT⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m Q hv e
    have h : UnitaryFieldData Q.p Q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    have hne : ¬(m + 1 = 3 ∧ Q.p ^ Q.exponent = 2) := fun h2 => hq' (by rw [h2.1, h2.2])
    have hpq : m + 1 ∣ Q.p ^ Q.exponent + 1 := by
      rw [← TauCeti.PrimePower.card_def]
      exact Nat.dvd_of_mod_eq_zero hQ
    have hn1 : 1 ≤ m + 1 := by omega
    let ε := eT.trans (statedProjEquivPrimeFormP h hn1)
    have hD : IsElemAbelian (m + 1) (B'.map (modelHom ε)) := hB'el.map _
    have hDc : Nat.card (B'.map (modelHom ε)) = (m + 1) ^ 2 := by
      rw [Subgroup.card_map_of_injective (modelHom_injective hYc ε), hB'c]
    exact not_balanced_modelHom hYc ε hnb (unitary_balanced h hp hp2 hne hpq hD hDc)

end TwoLp

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.BalanceLp
