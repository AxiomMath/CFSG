module

public import CFSG.GH74.GLS.Stage2.OddAut.Lin3Aut
public import CFSG.GH74.GLS.Stage2.OddAut.LinNEig

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section ScalarN

variable {K : Type*} [Field K] {n : ℕ}

theorem coe_scalar_smul_n (u : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin n) u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (u : K) • (1 : Matrix (Fin n) (Fin n) K) := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem scalar_commute_n (u : Kˣ) (g : GL (Fin n) K) :
    Commute (GeneralLinearGroup.scalar (Fin n) u : GL (Fin n) K) g := by
  apply Units.ext
  show (GeneralLinearGroup.scalar (Fin n) u : GL (Fin n) K).1 * g.1 =
    g.1 * (GeneralLinearGroup.scalar (Fin n) u : GL (Fin n) K).1
  rw [coe_scalar_smul_n, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem scalar_injective_n (hn : 0 < n) :
    Function.Injective (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K) := by
  intro u v h
  have h1 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) h
  simp only [coe_scalar_smul_n, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h1
  exact Units.ext h1

theorem det_scalar_n (u : Kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) u : GL (Fin n) K) = u ^ n := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, coe_scalar_smul_n, Matrix.det_smul, Matrix.det_one]
  simp

theorem comm_scalar_pow_n_dim {a b : GL (Fin n) K} {u : Kˣ}
    (h : a * b = GeneralLinearGroup.scalar (Fin n) u * (b * a)) : u ^ n = 1 := by
  have h1 := congrArg (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ) h
  rw [map_mul, map_mul, map_mul, det_scalar_n] at h1
  have h2 : u ^ n * (GeneralLinearGroup.det b * GeneralLinearGroup.det a) =
      1 * (GeneralLinearGroup.det b * GeneralLinearGroup.det a) :=
    calc u ^ n * (GeneralLinearGroup.det b * GeneralLinearGroup.det a)
        = GeneralLinearGroup.det a * GeneralLinearGroup.det b := h1.symm
      _ = 1 * (GeneralLinearGroup.det b * GeneralLinearGroup.det a) := by rw [one_mul, mul_comm]
  exact mul_right_cancel h2

theorem comm_scalar_pow_n {a b : GL (Fin n) K} {u : Kˣ} {r : ℕ} {β : Kˣ} (hn : 0 < n)
    (h : a * b = GeneralLinearGroup.scalar (Fin n) u * (b * a))
    (hb : b ^ r = GeneralLinearGroup.scalar (Fin n) β) : u ^ r = 1 := by
  have hconj : a * b * a⁻¹ = GeneralLinearGroup.scalar (Fin n) u * b := by
    calc a * b * a⁻¹ = (GeneralLinearGroup.scalar (Fin n) u * (b * a)) * a⁻¹ := by rw [h]
      _ = GeneralLinearGroup.scalar (Fin n) u * b := by group
  have h1 : a * b ^ r * a⁻¹ = (a * b * a⁻¹) ^ r := by
    simp
  rw [hconj, (scalar_commute_n u b).mul_pow r, hb] at h1
  have h3 : a * GeneralLinearGroup.scalar (Fin n) β * a⁻¹ = GeneralLinearGroup.scalar (Fin n) β := by
    rw [← (scalar_commute_n β a).eq, mul_inv_cancel_right]
  rw [h3, ← map_pow, ← map_mul] at h1
  have := scalar_injective_n hn h1
  have h5 : u ^ r * β = 1 * β := by rw [one_mul]; exact this.symm
  exact mul_right_cancel h5

theorem units_eq_one_of_coprime {u : Kˣ} {r : ℕ} (hcop : Nat.Coprime n r) (h1 : u ^ n = 1)
    (h2 : u ^ r = 1) : u = 1 :=
  orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1)
    (orderOf_dvd_of_pow_eq_one h2))

theorem exists_unit_pow_eq {r : ℕ} (hcop : Nat.Coprime n r) {A : GL (Fin n) K} {u : Kˣ}
    (h : A ^ r = GeneralLinearGroup.scalar (Fin n) u) : ∃ c : Kˣ, c ^ r = u := by
  have h1 : (GeneralLinearGroup.det A) ^ r = u ^ n := by
    rw [← map_pow, h, det_scalar_n]
  obtain ⟨s, t, hst⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  refine ⟨(GeneralLinearGroup.det A) ^ s * u ^ t, ?_⟩
  set D : Kˣ := GeneralLinearGroup.det A with hD
  have e1 : (D ^ s) ^ r = (u ^ (n : ℤ)) ^ s := by
    rw [← zpow_natCast (D ^ s) r, ← _root_.zpow_mul, mul_comm s, _root_.zpow_mul, zpow_natCast, h1, zpow_natCast]
  have e2 : (u ^ t) ^ r = u ^ (t * (r : ℤ)) := by
    rw [← zpow_natCast (u ^ t) r, ← _root_.zpow_mul]
  calc (D ^ s * u ^ t) ^ r = (D ^ s) ^ r * (u ^ t) ^ r := mul_pow _ _ _
    _ = u ^ (n * s) * u ^ (t * (r : ℤ)) := by
        rw [e1, e2, ← _root_.zpow_mul]
    _ = u ^ (s * (n : ℤ) + t * r) := by
        rw [← _root_.zpow_add, mul_comm (n : ℤ) s]
    _ = u := by rw [hst, zpow_one]

end ScalarN

section LiftsN

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem exists_lifts_n (hn : 3 ≤ n) {r : ℕ} (hr : r.Prime)
    (V : Subgroup (MulAut (projectiveSL n K)))
    (hVI : V ≤ (conjAut n K).range) (hVc : Nat.card V = r ^ 2) (hVe : ∀ v ∈ V, v ^ r = 1)
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) :
    ∃ (a b : GL (Fin n) K) (ua ub u : Kˣ), conjAut n K a ∈ V ∧ conjAut n K b ∈ V ∧
      a ^ r = GeneralLinearGroup.scalar (Fin n) ua ∧ b ^ r = GeneralLinearGroup.scalar (Fin n) ub ∧
      a * b = GeneralLinearGroup.scalar (Fin n) u * (b * a) ∧
      (∀ i j : ℕ, (∃ w : Kˣ, a ^ i * b ^ j = GeneralLinearGroup.scalar (Fin n) w) →
        r ∣ i ∧ r ∣ j) ∧
      ∀ v ∈ V, ∃ i j : ℕ, v = conjAut n K (a ^ i * b ^ j) := by
  obtain ⟨v₁, hv₁, v₂, hv₂, hind, hspan⟩ := exists_basis_elemAbelian hr V hVc hVe hVab
  obtain ⟨a, rfl⟩ := hVI hv₁
  obtain ⟨b, rfl⟩ := hVI hv₂
  have hc : conjAut n K a * conjAut n K b = conjAut n K b * conjAut n K a := hVab _ hv₁ _ hv₂
  have hone : ∀ A : GL (Fin n) K, conjAut n K A = 1 →
      ∃ w : Kˣ, A = GeneralLinearGroup.scalar (Fin n) w :=
    fun A h => (conjAut_eq_one_iff_of_three_le hn A).mp h
  obtain ⟨ua, hua⟩ := hone (a ^ r) (by rw [map_pow]; exact hVe _ hv₁)
  obtain ⟨ub, hub⟩ := hone (b ^ r) (by rw [map_pow]; exact hVe _ hv₂)
  obtain ⟨u, hu⟩ := hone (a * b * a⁻¹ * b⁻¹) (by
    simp only [map_mul, map_inv]
    rw [hc]
    group)
  refine ⟨a, b, ua, ub, u, hv₁, hv₂, hua, hub, ?_, ?_, ?_⟩
  · calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
      _ = GeneralLinearGroup.scalar (Fin n) u * (b * a) := by rw [hu, mul_assoc]
  · rintro i j ⟨w, hw⟩
    apply hind
    have := congrArg (conjAut n K) hw
    rw [map_mul, map_pow, map_pow, conjAut_scalar] at this
    exact this
  · intro v hv
    obtain ⟨i, j, hij⟩ := hspan v hv
    exact ⟨i, j, by rw [hij, map_mul, map_pow, map_pow]⟩

omit [Finite K] in
theorem mul_pow_diag_n {B M : Matrix (Fin n) (Fin n) K} {d : Fin n → K}
    (h : M * B = B * Matrix.diagonal d) (i : ℕ) :
    M ^ i * B = B * Matrix.diagonal (d ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal,
      pow_succ]
    rfl

theorem inner_plane_toral_of_coprime (hn : 3 ≤ n) {r : ℕ} (hr : r.Prime) (hcop : Nat.Coprime n r)
    (hrK : r ∣ Nat.card K - 1) (V : Subgroup (MulAut (projectiveSL n K)))
    (hVI : V ≤ (conjAut n K).range) (hVc : Nat.card V = r ^ 2) (hVe : ∀ v ∈ V, v ^ r = 1)
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) :
    ∃ B : GL (Fin n) K, ∀ v ∈ V, ∃ (x : GL (Fin n) K) (d : Fin n → K), v = conjAut n K x ∧
      (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
        (B : Matrix (Fin n) (Fin n) K) * Matrix.diagonal d := by
  classical
  have hn0 : 0 < n := by omega
  obtain ⟨a, b, ua, ub, u, -, -, hau, hbu, hab, -, hspan⟩ := exists_lifts_n hn hr V hVI hVc hVe hVab
  have hu : u = 1 :=
    units_eq_one_of_coprime hcop (comm_scalar_pow_n_dim hab) (comm_scalar_pow_n hn0 hab hbu)
  rw [hu, map_one, one_mul] at hab
  obtain ⟨la, hla⟩ := exists_unit_pow_eq hcop hau
  obtain ⟨lb, hlb⟩ := exists_unit_pow_eq hcop hbu
  set a' : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) la⁻¹ * a with ha'
  set b' : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) lb⁻¹ * b with hb'
  have ha'r : a' ^ r = 1 := by
    rw [ha', (scalar_commute_n _ a).mul_pow, hau, ← map_pow, ← map_mul, inv_pow, hla,
      inv_mul_cancel, map_one]
  have hb'r : b' ^ r = 1 := by
    rw [hb', (scalar_commute_n _ b).mul_pow, hbu, ← map_pow, ← map_mul, inv_pow, hlb,
      inv_mul_cancel, map_one]
  have hab' : a' * b' = b' * a' := by
    have hc : Commute a b := hab
    have h1 : Commute a (GeneralLinearGroup.scalar (Fin n) lb⁻¹ * b) :=
      (scalar_commute_n lb⁻¹ a).symm.mul_right hc
    exact (((scalar_commute_n la⁻¹ _).mul_left h1)).eq
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨ω₀, hω₀⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r (by rwa [Nat.card_units])
  have hω : IsPrimitiveRoot (ω₀ : K) r := by
    have h1 := IsPrimitiveRoot.orderOf ω₀
    rw [hω₀] at h1
    exact IsPrimitiveRoot.coe_units_iff.mpr h1
  have ha'M : (a' : Matrix (Fin n) (Fin n) K) ^ r = 1 := by
    rw [← Units.val_pow_eq_pow_val, ha'r, Units.val_one]
  have hb'M : (b' : Matrix (Fin n) (Fin n) K) ^ r = 1 := by
    rw [← Units.val_pow_eq_pow_val, hb'r, Units.val_one]
  have hab'M : (a' : Matrix (Fin n) (Fin n) K) * b' = b' * a' := by
    rw [← Units.val_mul, ← Units.val_mul, hab']
  obtain ⟨B₀, da, db, hB, h1, h2⟩ := exists_joint_eigenbasis_n hr.pos hω _ _ ha'M hb'M hab'M
  refine ⟨Matrix.nonsingInvUnit B₀ hB, fun v hv => ?_⟩
  obtain ⟨i, j, hij⟩ := hspan v hv
  refine ⟨a' ^ i * b' ^ j, da ^ i * db ^ j, ?_, ?_⟩
  · have hca : conjAut n K a' = conjAut n K a := by rw [ha', map_mul, conjAut_scalar, one_mul]
    have hcb : conjAut n K b' = conjAut n K b := by rw [hb', map_mul, conjAut_scalar, one_mul]
    rw [hij, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, hca, hcb]
  · have hBg : ((Matrix.nonsingInvUnit B₀ hB : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = B₀ := rfl
    rw [hBg, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      Matrix.mul_assoc, mul_pow_diag_n h2 j, ← Matrix.mul_assoc, mul_pow_diag_n h1 i,
      Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    rfl

end LiftsN

end CFSG.GH74.GLS.Stage2.OddAut
