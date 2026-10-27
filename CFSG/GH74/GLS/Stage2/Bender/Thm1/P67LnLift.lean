module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnAut
public import CFSG.GH74.GLS.Stage2.OddAut.Lin3Cyc
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Lift

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem eq_scalar_of_conjAut_eq_one (hn : 3 ≤ n) {A : GL (Fin n) K} (h : conjAut n K A = 1) :
    ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin n) c = A := by
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn A 1 (by simpa using h)
  exact ⟨c, hc⟩

omit [Finite K] in
theorem scalar_eq_one {u : Kˣ} (hn : 0 < n)
    (h : Matrix.GeneralLinearGroup.scalar (Fin n) u = (1 : GL (Fin n) K)) : u = 1 := by
  have h2 := congrArg (fun U : GL (Fin n) K =>
    (U : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) h
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    Units.val_one, Matrix.one_apply_eq] at h2
  exact Units.ext h2

omit [Finite K] in
theorem units_eq_one_of_pow_eq_one {r : ℕ} (hr : r.Prime) (hrK1 : ¬ r ∣ Nat.card K - 1) {u : Kˣ}
    (hu : u ^ r = 1) : u = 1 := by
  have hcop : Nat.Coprime r (Nat.card Kˣ) := by
    rw [Nat.card_units]
    exact (Nat.Prime.coprime_iff_not_dvd hr).2 hrK1
  have h1 : orderOf u ∣ r := orderOf_dvd_of_pow_eq_one hu
  have h2 : orderOf u ∣ Nat.card Kˣ := orderOf_dvd_natCard u
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem lifts_commute (hn : 3 ≤ n) {r : ℕ} (hr : r.Prime) (hrK1 : ¬ r ∣ Nat.card K - 1)
    {x y : GL (Fin n) K} (hxy : conjAut n K x * conjAut n K y = conjAut n K y * conjAut n K x)
    (hy : y ^ r = 1) : x * y = y * x := by
  have h1 : conjAut n K (x * y * x⁻¹ * y⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    calc conjAut n K x * conjAut n K y * (conjAut n K x)⁻¹ * (conjAut n K y)⁻¹
        = (conjAut n K x * conjAut n K y) * (conjAut n K y * conjAut n K x)⁻¹ := by group
      _ = 1 := by rw [hxy]; simp
  obtain ⟨c, hc⟩ := eq_scalar_of_conjAut_eq_one hn h1
  have h2 : x * y * x⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin n) c * y := by
    calc x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin n) c * y := by rw [← hc]
  have h3 : (Matrix.GeneralLinearGroup.scalar (Fin n) c * y) ^ r = 1 := by
    rw [← h2, conj_pow, hy]; group
  rw [(scalar_commute' c y).mul_pow, hy, mul_one, ← map_pow] at h3
  have h4 : c ^ r = 1 := scalar_eq_one (by omega) h3
  have h5 : c = 1 := units_eq_one_of_pow_eq_one hr hrK1 h4
  rw [h5, map_one, one_mul] at h2
  calc x * y = (x * y * x⁻¹) * x := by group
    _ = y * x := by rw [h2]

theorem exists_lift_group (hn : 3 ≤ n) {r : ℕ} [Fact r.Prime] (hrK1 : ¬ r ∣ Nat.card K - 1)
    {V : Subgroup (MulAut (projectiveSL n K))} [hVe : IsElementaryAbelian r ↥V]
    (hVc : Nat.card ↥V = r ^ 2) (hVD : ∀ v ∈ V, ∃ A : GL (Fin n) K, v = conjAut n K A) :
    ∃ W : Subgroup (GL (Fin n) K), IsElementaryAbelian r ↥W ∧ Nat.card ↥W = r ^ 2 ∧
      (∀ x ∈ W, conjAut n K x ∈ V) ∧ (∀ v ∈ V, ∃ x ∈ W, conjAut n K x = v) := by
  classical
  have hr : r.Prime := Fact.out
  have hVpow : ∀ v ∈ V, v ^ r = 1 := fun v hv =>
    elemPow_eq_one_of_isElementaryAbelian (A := V) v hv
  have hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw => by
    have := hVe.toIsMulCommutative.is_comm.comm (⟨v, hv⟩ : ↥V) ⟨w, hw⟩
    exact congrArg Subtype.val this
  have hcomm : ∀ x y : GL (Fin n) K, conjAut n K x ∈ V → conjAut n K y ∈ V → y ^ r = 1 →
      x * y = y * x := fun x y hx hy hyr =>
    lifts_commute hn hr hrK1 (hVcomm _ hx _ hy) hyr
  let W : Subgroup (GL (Fin n) K) :=
    { carrier := {x | conjAut n K x ∈ V ∧ x ^ r = 1}
      one_mem' := ⟨by simp, one_pow r⟩
      mul_mem' := fun {x y} hx hy => by
        refine ⟨by rw [map_mul]; exact V.mul_mem hx.1 hy.1, ?_⟩
        rw [(show Commute x y from hcomm x y hx.1 hy.1 hy.2).mul_pow, hx.2, hy.2, mul_one]
      inv_mem' := fun {x} hx => by
        refine ⟨by rw [map_inv]; exact V.inv_mem hx.1, ?_⟩
        rw [inv_pow, hx.2, inv_one] }
  have hWcomm : ∀ x y : ↥W, x * y = y * x := fun x y =>
    Subtype.ext (hcomm x y x.2.1 y.2.1 y.2.2)
  have hWe : IsElementaryAbelian r ↥W :=
    { toIsMulCommutative := ⟨⟨fun a b => hWcomm a b⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext x.2.2 }
  let f : ↥W → ↥V := fun x => ⟨conjAut n K x, x.2.1⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : conjAut n K ((x : GL (Fin n) K)⁻¹ * y) = 1 := by
      have := congrArg Subtype.val hxy
      rw [map_mul, map_inv]
      change conjAut n K x = conjAut n K y at this
      rw [this]; simp
    obtain ⟨c, hc⟩ := eq_scalar_of_conjAut_eq_one hn h1
    have hxy' : Commute (x : GL (Fin n) K) y := hcomm x y x.2.1 y.2.1 y.2.2
    have h2 : ((x : GL (Fin n) K)⁻¹ * y) ^ r = 1 := by
      rw [hxy'.inv_left.mul_pow, inv_pow, x.2.2, y.2.2]
      simp
    rw [← hc, ← map_pow] at h2
    have h3 : c ^ r = 1 := scalar_eq_one (by omega) h2
    have h4 : c = 1 := units_eq_one_of_pow_eq_one hr hrK1 h3
    rw [h4, map_one] at hc
    apply Subtype.ext
    have h5 : (x : GL (Fin n) K)⁻¹ * y = 1 := hc.symm
    exact (inv_mul_eq_one.mp h5)
  have hsurj : Function.Surjective f := by
    intro v
    obtain ⟨A, hA⟩ := hVD v.1 v.2
    have h1 : conjAut n K (A ^ r) = 1 := by
      rw [map_pow, ← hA]; exact hVpow _ v.2
    obtain ⟨u, hu⟩ := eq_scalar_of_conjAut_eq_one hn h1
    have hcop : Nat.Coprime (Nat.card Kˣ) r := by
      rw [Nat.card_units]
      exact ((Nat.Prime.coprime_iff_not_dvd hr).2 hrK1).symm
    obtain ⟨μ, hμ⟩ := (powCoprime hcop).surjective u⁻¹
    have hμ' : μ ^ r = u⁻¹ := hμ
    refine ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin n) μ * A, ?_, ?_⟩, ?_⟩
    · rw [map_mul, conjAut_scalar', one_mul, ← hA]; exact v.2
    · rw [(scalar_commute' μ A).mul_pow, ← map_pow, hμ', ← hu, ← map_mul, inv_mul_cancel,
        map_one]
    · apply Subtype.ext
      change conjAut n K (Matrix.GeneralLinearGroup.scalar (Fin n) μ * A) = v.1
      rw [map_mul, conjAut_scalar', one_mul, hA]
  refine ⟨W, hWe, ?_, fun x hx => hx.1, fun v hv => ?_⟩
  · have := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
    rw [this, hVc]
  · obtain ⟨⟨x, hx⟩, hxv⟩ := hsurj ⟨v, hv⟩
    exact ⟨x, hx, congrArg Subtype.val hxv⟩

end Lift

section Cyclic

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem false_of_sylow_cyclic {r : ℕ} [Fact r.Prime] (W : Subgroup (GL (Fin n) K))
    [IsElementaryAbelian r ↥W] (hWc : Nat.card ↥W = r ^ 2)
    (hcyc : ∀ P : Sylow r (GL (Fin n) K), IsCyclic P) : False := by
  have hWp : IsPGroup r ↥W := IsElementaryAbelian.isPGroup r W
  obtain ⟨P, hP⟩ := hWp.exists_le_sylow
  have : IsCyclic ↥W := by
    have := hcyc P
    exact isCyclic_of_injective (Subgroup.inclusion hP) (Subgroup.inclusion_injective hP)
  exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hWc this

theorem isCyclic_sylow_gl_of_div {r : ℕ} [Fact r.Prime] (hr2 : Odd r)
    (hrK : ¬ r ∣ Nat.card K) (hdiv : n / orderOf (Nat.card K : ZMod r) ≤ 1)
    (P : Sylow r (GL (Fin n) K)) : IsCyclic P := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨φ⟩ := CFSG.GroupTheory.WeirSylow.sylow_GL hr2 K (by rwa [← Nat.card_eq_fintype_card]) n P
  rw [Nat.card_eq_fintype_card] at hdiv
  exact (MulEquiv.isCyclic φ).mpr (OddAut.isCyclic_sigmaModel_of_div_le_one
    (Fact.out : r.Prime).one_lt hdiv)

end Cyclic

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln
