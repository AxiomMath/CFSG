module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.DiagPlane
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisTv

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo

variable {n : ℕ} {F : Type} [Field F]

theorem toLin'_rel {S T : GL (Fin n) F} {u : Fˣ}
    (h : S * T = GeneralLinearGroup.scalar (Fin n) u * (T * S)) :
    Matrix.toLin' (S : Matrix (Fin n) (Fin n) F) * Matrix.toLin' (T : Matrix (Fin n) (Fin n) F) =
      (u : F) • (Matrix.toLin' (T : Matrix (Fin n) (Fin n) F) *
        Matrix.toLin' (S : Matrix (Fin n) (Fin n) F)) := by
  have h1 := congrArg (fun g : GL (Fin n) F => Matrix.toLin' (g : Matrix (Fin n) (Fin n) F)) h
  simp only [Units.val_mul, Matrix.toLin'_mul, GeneralLinearGroup.coe_scalar] at h1
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, h1, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, map_smul, Matrix.toLin'_one, LinearMap.smul_comp,
    LinearMap.id_comp]

section GroupLemmas

variable {G : Type*} [Group G]

theorem pow_mul_comm_central {X Y z : G} (hz : ∀ g, z * g = g * z) (hXY : X * Y = z * (Y * X))
    (k : ℕ) : Y ^ k * X = z⁻¹ ^ k * (X * Y ^ k) := by
  have hYX : Y * X = z⁻¹ * (X * Y) := by rw [hXY, ← mul_assoc, inv_mul_cancel, one_mul]
  have hc : ∀ (m : ℕ) (g : G), Commute (z⁻¹ ^ m) g := fun m g =>
    ((show Commute z g from hz g).inv_left).pow_left m
  induction k with
  | zero => simp
  | succ k ih =>
    calc Y ^ (k + 1) * X = Y * (Y ^ k * X) := by rw [pow_succ', mul_assoc]
      _ = Y * (z⁻¹ ^ k * (X * Y ^ k)) := by rw [ih]
      _ = z⁻¹ ^ k * (Y * (X * Y ^ k)) := by rw [← mul_assoc, (hc k Y).eq.symm, mul_assoc]
      _ = z⁻¹ ^ k * ((Y * X) * Y ^ k) := by rw [← mul_assoc Y X]
      _ = z⁻¹ ^ k * ((z⁻¹ * (X * Y)) * Y ^ k) := by rw [hYX]
      _ = z⁻¹ ^ (k + 1) * (X * Y ^ (k + 1)) := by
          rw [pow_succ z⁻¹ k, pow_succ' Y k]
          simp only [mul_assoc]

theorem mul_pow_central {X Y z : G} (hz : ∀ g, z * g = g * z) (hXY : X * Y = z * (Y * X))
    (k : ℕ) : (X * Y) ^ k = z⁻¹ ^ (k.choose 2) * (X ^ k * Y ^ k) := by
  have hc : ∀ (m : ℕ) (g : G), Commute (z⁻¹ ^ m) g := fun m g =>
    ((show Commute z g from hz g).inv_left).pow_left m
  induction k with
  | zero => simp
  | succ k ih =>
    calc (X * Y) ^ (k + 1) = (X * Y) ^ k * (X * Y) := by rw [pow_succ]
      _ = (z⁻¹ ^ (k.choose 2) * (X ^ k * Y ^ k)) * (X * Y) := by rw [ih]
      _ = z⁻¹ ^ (k.choose 2) * (X ^ k * (Y ^ k * X) * Y) := by simp only [mul_assoc]
      _ = z⁻¹ ^ (k.choose 2) * (X ^ k * (z⁻¹ ^ k * (X * Y ^ k)) * Y) := by
          rw [pow_mul_comm_central hz hXY k]
      _ = z⁻¹ ^ (k.choose 2) * (z⁻¹ ^ k * (X ^ k * (X * Y ^ k) * Y)) := by
          rw [← mul_assoc (X ^ k), (hc k (X ^ k)).eq.symm, mul_assoc, mul_assoc, mul_assoc]
          simp only [mul_assoc]
      _ = z⁻¹ ^ ((k + 1).choose 2) * (X ^ (k + 1) * Y ^ (k + 1)) := by
          have : (k + 1).choose 2 = k.choose 2 + k := by
            rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
          rw [this, pow_add, ← mul_assoc, pow_succ X k, pow_succ Y k]
          simp only [mul_assoc]

theorem mul_pow_prime_central {X Y z : G} (hz : ∀ g, z * g = g * z) (hXY : X * Y = z * (Y * X))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hzp : z ^ p = 1) : (X * Y) ^ p = X ^ p * Y ^ p := by
  rw [mul_pow_central hz hXY p]
  have hdvd : p ∣ p.choose 2 :=
    hp.dvd_choose_self (by norm_num) (lt_of_le_of_ne hp.two_le (Ne.symm hp2))
  obtain ⟨m, hm⟩ := hdvd
  rw [hm, pow_mul, inv_pow, hzp, inv_one, one_pow, one_mul]

end GroupLemmas

section GLRel

variable [Finite F]

theorem scalar_eq_one_iff (hn : 0 < n) {u : Fˣ} :
    GeneralLinearGroup.scalar (Fin n) u = 1 ↔ u = 1 := by
  constructor
  · intro h
    have := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) ⟨0, hn⟩ ⟨0, hn⟩) h
    simp at this
    exact this
  · rintro rfl
    exact map_one _

theorem eq_scalar_of_conjAut_eq_one (hn : 3 ≤ n) {B : GL (Fin n) F} (h : conjAut n F B = 1) :
    ∃ c : Fˣ, GeneralLinearGroup.scalar (Fin n) c = B :=
  (eq_one_of_conjAut_mul_fieldAut_eq_one hn B 1 (by rw [map_one, mul_one]; exact h)).2

theorem exists_comm_scalar (hn : 3 ≤ n) {A B : GL (Fin n) F}
    (hcomm : conjAut n F A * conjAut n F B = conjAut n F B * conjAut n F A) :
    ∃ z : Fˣ, A * B = GeneralLinearGroup.scalar (Fin n) z * (B * A) := by
  obtain ⟨z, hz⟩ := CrossChar.exists_scalar_eq_commutator hn hcomm
  exact ⟨z, by rw [hz]; group⟩

theorem exists_pow_scalar (hn : 3 ≤ n) {A : GL (Fin n) F} {p : ℕ} (hA : conjAut n F A ^ p = 1) :
    ∃ a : Fˣ, A ^ p = GeneralLinearGroup.scalar (Fin n) a := by
  have : conjAut n F (A ^ p) = 1 := by rw [map_pow, hA]
  obtain ⟨a, ha⟩ := eq_scalar_of_conjAut_eq_one hn this
  exact ⟨a, ha.symm⟩

theorem comm_scalar_pow_eq_one (hn : 3 ≤ n) {A B : GL (Fin n) F} {z : Fˣ}
    (hAB : A * B = GeneralLinearGroup.scalar (Fin n) z * (B * A)) {p : ℕ} {b : Fˣ}
    (hb : B ^ p = GeneralLinearGroup.scalar (Fin n) b) : z ^ p = 1 := by
  have hzc : ∀ g : GL (Fin n) F, GeneralLinearGroup.scalar (Fin n) z * g =
      g * GeneralLinearGroup.scalar (Fin n) z := fun g => GeneralLinearGroup.scalar_commute z g
  have h1 : A * B * A⁻¹ = GeneralLinearGroup.scalar (Fin n) z * B := by
    rw [hAB]; group
  have h2 : (A * B * A⁻¹) ^ p = A * B ^ p * A⁻¹ := conj_pow
  have h3 : (GeneralLinearGroup.scalar (Fin n) z * B) ^ p =
      GeneralLinearGroup.scalar (Fin n) z ^ p * B ^ p :=
    (show Commute (GeneralLinearGroup.scalar (Fin n) z) B from hzc B).mul_pow p
  have h4 : A * B ^ p * A⁻¹ = B ^ p := by
    rw [hb, ← GeneralLinearGroup.scalar_commute b A, mul_assoc, mul_inv_cancel, mul_one]
  rw [h1, h3, h4] at h2
  have h5 : GeneralLinearGroup.scalar (Fin n) z ^ p = 1 := by
    have h2' : GeneralLinearGroup.scalar (Fin n) z ^ p * B ^ p = 1 * B ^ p := by
      rw [h2, one_mul]
    exact mul_right_cancel h2'
  rw [← map_pow, scalar_eq_one_iff (by omega)] at h5
  exact h5

theorem exists_pthpower_mul {p : ℕ} (hp : p.Prime) (a b : Fˣ) (ha : ¬ ∃ e : Fˣ, e ^ p = a) :
    ∃ (i : ℕ) (e : Fˣ), e ^ p = a ^ i * b := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hnat : ∀ x : Fˣ, ∃ k : ℕ, g ^ k = x := fun x => by
    have := hg x
    rw [← mem_powers_iff_mem_zpowers] at this
    exact (Submonoid.mem_powers_iff x g).1 this
  obtain ⟨α, hα⟩ := hnat a
  obtain ⟨β, hβ⟩ := hnat b
  have hpα : ¬ p ∣ α := by
    rintro ⟨m, rfl⟩
    exact ha ⟨g ^ m, by rw [← hα, ← pow_mul, mul_comm]⟩
  have hα0 : (α : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  set i : ℕ := ((-(β : ZMod p)) * (α : ZMod p)⁻¹).val with hi
  have hdvd : p ∣ i * α + β := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [hi, ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hα0, mul_one]
    exact neg_add_cancel _
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨i, g ^ k, ?_⟩
  have hk' : k * p = α * i + β := by rw [mul_comm k p, ← hk, mul_comm]
  rw [← hα, ← hβ, ← pow_mul, ← pow_mul, ← pow_add, hk']

end GLRel

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis
