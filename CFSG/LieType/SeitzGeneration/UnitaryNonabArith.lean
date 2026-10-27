module

public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem bar_mul_eq_one_of_pow_eq (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f + 1) {μ α : K} (hμ0 : μ ≠ 0) (hμ : μ ^ p = α)
    (hα : α ^ (ℓ ^ f + 1) = 1) : h.bar μ * μ = 1 := by
  have hfin := h.finite
  have := Fintype.ofFinite K
  have hq2 : 2 ≤ ℓ ^ f := Nat.succ_le_of_lt (Nat.one_lt_pow (by have := h.one_le; omega)
    h.prime.one_lt)
  have hNe : h.bar μ * μ = μ ^ (ℓ ^ f + 1) := by rw [h.bar_apply, ← pow_succ]
  have h1 : (h.bar μ * μ) ^ p = 1 := by
    rw [hNe, ← pow_mul, mul_comm (ℓ ^ f + 1) p, pow_mul μ p, hμ, hα]
  have h2 : (h.bar μ * μ) ^ (ℓ ^ f - 1) = 1 := by
    rw [hNe, ← pow_mul]
    have h3 : (ℓ ^ f + 1) * (ℓ ^ f - 1) = Fintype.card K - 1 := by
      rw [← Nat.card_eq_fintype_card, h.card_eq_sq, sq]
      have := Nat.mul_self_sub_mul_self_eq (ℓ ^ f) 1
      simpa using this.symm
    rw [h3]
    exact FiniteField.pow_card_sub_one_eq_one μ hμ0
  have hcop : Nat.gcd p (ℓ ^ f - 1) = 1 := by
    rcases (Nat.dvd_prime hp).1 (Nat.gcd_dvd_left p (ℓ ^ f - 1)) with h4 | h4
    · exact h4
    · exfalso
      have h5 : p ∣ ℓ ^ f - 1 := by
        have := Nat.gcd_dvd_right p (ℓ ^ f - 1)
        rwa [h4] at this
      have h6 : p ∣ 2 := by
        have e : ℓ ^ f + 1 = (ℓ ^ f - 1) + 2 := by omega
        rw [e] at hpq
        exact (Nat.dvd_add_right h5).1 hpq
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h6)
  have := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rwa [hcop, pow_one] at this

theorem bar_mul_eq_one_of_scalar_pow (h : UnitaryFieldData ℓ f K) {g : GL (Fin n) K} (hn : 1 ≤ n)
    (hg : g ∈ primeFormUnitary h (idGram K n)) {lam : K}
    (hlam : ((g ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = lam • 1) :
    h.bar lam * lam = 1 := by
  have h1 := mem_primeFormUnitary.1 (pow_mem hg p)
  simp only [idGram, Units.val_one] at h1
  rw [hlam, barTranspose_smul_mul_smul] at h1
  have h2 := congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩
  simpa using h2

theorem qcommMat_pow_left {T U : Matrix (Fin n) (Fin n) K} {d : K} (h : U * T = d • (T * U))
    (k : ℕ) : U ^ k * T = d ^ k • (T * U ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc U ^ (k + 1) * T = U * (U ^ k * T) := by rw [pow_succ', Matrix.mul_assoc]
      _ = U * (d ^ k • (T * U ^ k)) := by rw [ih]
      _ = d ^ k • ((U * T) * U ^ k) := by rw [Matrix.mul_smul, Matrix.mul_assoc]
      _ = d ^ k • ((d • (T * U)) * U ^ k) := by rw [h]
      _ = d ^ (k + 1) • (T * U ^ (k + 1)) := by
        rw [Matrix.smul_mul, smul_smul, pow_succ d k, pow_succ' U k, Matrix.mul_assoc]

theorem qcommMat_pow_pow {X Y : Matrix (Fin n) (Fin n) K} {c : K} (h : Y * X = c • (X * Y))
    (a b : ℕ) : Y ^ b * X ^ a = c ^ (a * b) • (X ^ a * Y ^ b) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hab : a * b + b = (a + 1) * b := by ring
    calc Y ^ b * X ^ (a + 1) = (Y ^ b * X ^ a) * X := by rw [pow_succ, Matrix.mul_assoc]
      _ = c ^ (a * b) • ((X ^ a * Y ^ b) * X) := by rw [ih, Matrix.smul_mul]
      _ = c ^ (a * b) • (X ^ a * (Y ^ b * X)) := by rw [Matrix.mul_assoc]
      _ = c ^ (a * b) • (X ^ a * (c ^ b • (X * Y ^ b))) := by rw [qcommMat_pow_left h b]
      _ = c ^ (a * b) • (c ^ b • (X ^ (a + 1) * Y ^ b)) := by
        rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← pow_succ]
      _ = c ^ ((a + 1) * b) • (X ^ (a + 1) * Y ^ b) := by
        rw [smul_smul, ← pow_add, hab]

theorem qcommMat_pow_prod {T U : Matrix (Fin n) (Fin n) K} {d : K} (h : U * T = d • (T * U))
    (k : ℕ) : (T * U) ^ k = d ^ (k.choose 2) • (T ^ k * U ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hc : (k + 1).choose 2 = k.choose 2 + k := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ, Nat.choose_one_right]
      ring
    calc (T * U) ^ (k + 1) = (T * U) ^ k * (T * U) := pow_succ _ _
      _ = d ^ (k.choose 2) • (T ^ k * (U ^ k * T) * U) := by
        rw [ih, Matrix.smul_mul]; simp only [Matrix.mul_assoc]
      _ = d ^ (k.choose 2) • (T ^ k * (d ^ k • (T * U ^ k)) * U) := by
        rw [qcommMat_pow_left h k]
      _ = d ^ ((k + 1).choose 2) • (T ^ (k + 1) * U ^ (k + 1)) := by
        rw [hc, Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← pow_add]
        congr 1
        rw [pow_succ T k, pow_succ U k]
        simp only [Matrix.mul_assoc]

theorem mat_pow_mul_comm (X M : Matrix (Fin n) (Fin n) K) (a : ℕ) :
    X ^ a * (X * M) = X * (X ^ a * M) := by
  rw [← Matrix.mul_assoc, ← (Commute.self_pow X a).eq, Matrix.mul_assoc]

theorem smul_one_pow_mat (α : K) (a : ℕ) :
    (α • (1 : Matrix (Fin n) (Fin n) K)) ^ a = (α ^ a) • (1 : Matrix (Fin n) (Fin n) K) := by
  rw [smul_pow, one_pow]

theorem pow_word_p {X Y : Matrix (Fin n) (Fin n) K} {α β c : K} (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : X ^ p = α • 1) (hY : Y ^ p = β • 1) (hYX : Y * X = c • (X * Y)) (hc : c ^ p = 1)
    (a b : ℕ) : (X ^ a * Y ^ b) ^ p = (α ^ a * β ^ b) • 1 := by
  have h2p : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have hcp : (c ^ (a * b)) ^ (p.choose 2) = 1 := by
    obtain ⟨m, hm⟩ := Nat.Prime.dvd_choose_self hp two_ne_zero h2p
    have hcpa : (c ^ (a * b)) ^ p = 1 := by
      rw [← pow_mul, mul_comm (a * b) p, pow_mul c p (a * b), hc, one_pow]
    rw [hm, pow_mul (c ^ (a * b)) p m, hcpa, one_pow]
  have hXa : (X ^ a) ^ p = α ^ a • 1 := by
    rw [← pow_mul, mul_comm a p, pow_mul X p a, hX, smul_one_pow_mat]
  have hYb : (Y ^ b) ^ p = β ^ b • 1 := by
    rw [← pow_mul, mul_comm b p, pow_mul Y p b, hY, smul_one_pow_mat]
  rw [qcommMat_pow_prod (qcommMat_pow_pow hYX a b) p, hcp, one_smul, hXa, hYb, Matrix.smul_mul,
    Matrix.one_mul, smul_smul]

theorem exists_pth_power_word [Finite K] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) {α β : K}
    (hα : α ≠ 0) (hβ : β ≠ 0) :
    ∃ a b : ℕ, ¬ (p ∣ a ∧ p ∣ b) ∧ ∃ ν : K, ν ^ p = α ^ a * β ^ b := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hgen : ∀ x : Kˣ, x ∈ Submonoid.powers g := fun x => mem_powers_iff_mem_zpowers.2 (hg x)
  obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).1 (hgen (Units.mk0 α hα))
  obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).1 (hgen (Units.mk0 β hβ))
  have hαi : α = (g : K) ^ i := by
    have := congrArg Units.val hi
    simpa using this.symm
  have hβj : β = (g : K) ^ j := by
    have := congrArg Units.val hj
    simpa using this.symm
  have hp1 : 1 < p := hp.one_lt
  by_cases hpi : p ∣ i
  · obtain ⟨k, rfl⟩ := hpi
    refine ⟨1, 0, fun h => hp1.ne' (Nat.dvd_one.1 h.1), (g : K) ^ k, ?_⟩
    rw [hαi, pow_one, pow_zero, mul_one, ← pow_mul, mul_comm]
  by_cases hpj : p ∣ j
  · obtain ⟨k, rfl⟩ := hpj
    refine ⟨0, 1, fun h => hp1.ne' (Nat.dvd_one.1 h.2), (g : K) ^ k, ?_⟩
    rw [hβj, pow_one, pow_zero, one_mul, ← pow_mul, mul_comm]
  refine ⟨j, (p - 1) * i, fun h => hpj h.1, (g : K) ^ (i * j), ?_⟩
  have hp' : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
  have key : i * j + j * ((p - 1) * i) = i * j * p := by
    conv_rhs => rw [← hp']
    ring
  rw [hαi, hβj, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, key]

theorem pow_mul_pow_pow_of_comm {G : Type*} [Group G] {e₁ e₂ : G} (hc : Commute e₁ e₂)
    (a b m : ℕ) : (e₁ ^ a * e₂ ^ b) ^ m = e₁ ^ (a * m) * e₂ ^ (b * m) := by
  rw [(hc.pow_pow a b).mul_pow, ← pow_mul, ← pow_mul]

theorem mem_zpowers_iff_exists_pow_p {G : Type*} [Group G] {p : ℕ} (hp : 0 < p) {e x : G}
    (he : e ^ p = 1) : x ∈ Subgroup.zpowers e ↔ ∃ m : ℕ, e ^ m = x := by
  have hfin : IsOfFinOrder e := isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp, he⟩
  rw [← hfin.mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff]

end CFSG.LieType.SeitzGeneration
