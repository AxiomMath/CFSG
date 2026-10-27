module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {K : Type} [Field K]

theorem scalars_commute {z : SpecialLinearGroup (Fin n) K} (hz : z ∈ scalars n K)
    (g : SpecialLinearGroup (Fin n) K) : Commute z g :=
  (Subgroup.mem_center_iff.1 (scalars_le_center n K hz) g).symm

theorem scalars_eq_one_of_sq (h2 : (2 : K) = 0) (hn : 0 < n) {z : SpecialLinearGroup (Fin n) K}
    (hz : z ∈ scalars n K) (hz2 : z ^ 2 = 1) : z = 1 := by
  obtain ⟨c, -, hc⟩ := mem_scalars.1 hz
  have h1 : ((z ^ 2 : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (1 : Matrix (Fin n) (Fin n) K) := by
    rw [hz2]
    rfl
  rw [Matrix.SpecialLinearGroup.coe_pow, pow_two, hc, ← map_mul] at h1
  have h3 : ((c : K) * (c : K)) = 1 := by
    have h4 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M ⟨0, hn⟩ ⟨0, hn⟩) h1
    simpa [Matrix.scalar_apply, Matrix.diagonal_apply_eq] using h4
  have h5 : ((c : K) - 1) * ((c : K) - 1) = 0 := by
    linear_combination h3 + (1 - (c : K)) * h2
  have h6 : (c : K) = 1 := sub_eq_zero.1 (mul_self_eq_zero.1 h5)
  apply Subtype.ext
  rw [hc, h6, map_one]
  rfl

theorem scalars_eq_one_of_two_pow (h2 : (2 : K) = 0) (hn : 0 < n) {z : SpecialLinearGroup (Fin n) K}
    (hz : z ∈ scalars n K) (a : ℕ) (hza : z ^ (2 ^ a) = 1) : z = 1 := by
  induction a generalizing z with
  | zero => simpa using hza
  | succ a ih =>
    refine ih hz ?_
    have hw : z ^ (2 ^ a) ∈ scalars n K := (scalars n K).pow_mem hz _
    refine scalars_eq_one_of_sq h2 hn hw ?_
    rw [← pow_mul, ← pow_succ]
    exact hza

variable [Finite K]

theorem exists_lift_two_pow (h2 : (2 : K) = 0) (hn : 0 < n) {y : projectiveSL n K} {a : ℕ}
    (hy : y ^ (2 ^ a) = 1) :
    ∃ g : SpecialLinearGroup (Fin n) K, proj n K g = y ∧ g ^ (2 ^ a) = 1 := by
  classical
  obtain ⟨g₀, rfl⟩ := proj_surjective n K y
  have hw : g₀ ^ (2 ^ a) ∈ scalars n K := by
    rw [← proj_eq_one_iff, map_pow]
    exact hy
  have hwinv : (g₀ ^ (2 ^ a))⁻¹ ∈ scalars n K := (scalars n K).inv_mem hw
  have hcentral : ∀ z ∈ scalars n K, ∀ g : SpecialLinearGroup (Fin n) K, Commute z g :=
    fun z hz g => scalars_commute hz g
  let f : ↥(scalars n K) → ↥(scalars n K) := fun z => z ^ (2 ^ a)
  have hfinj : Function.Injective f := by
    intro z₁ z₂ h
    have h' : (z₁ : SpecialLinearGroup (Fin n) K) ^ (2 ^ a) =
        (z₂ : SpecialLinearGroup (Fin n) K) ^ (2 ^ a) := congrArg Subtype.val h
    have hc : Commute (z₁ : SpecialLinearGroup (Fin n) K) (z₂ : SpecialLinearGroup (Fin n) K)⁻¹ :=
      hcentral _ z₁.2 _
    have h1 : ((z₁ : SpecialLinearGroup (Fin n) K) * (z₂ : SpecialLinearGroup (Fin n) K)⁻¹) ^ (2 ^ a) =
        1 := by
      rw [hc.mul_pow, inv_pow, h', mul_inv_cancel]
    have h3 := scalars_eq_one_of_two_pow h2 hn
      ((scalars n K).mul_mem z₁.2 ((scalars n K).inv_mem z₂.2)) a h1
    exact Subtype.ext (mul_inv_eq_one.1 h3)
  have hfsurj : Function.Surjective f := Finite.injective_iff_surjective.1 hfinj
  obtain ⟨z, hz⟩ := hfsurj ⟨(g₀ ^ (2 ^ a))⁻¹, hwinv⟩
  have hz' : (z : SpecialLinearGroup (Fin n) K) ^ (2 ^ a) = (g₀ ^ (2 ^ a))⁻¹ := congrArg Subtype.val hz
  refine ⟨(z : SpecialLinearGroup (Fin n) K) * g₀, ?_, ?_⟩
  · rw [map_mul, proj_eq_one_iff.2 z.2, one_mul]
  · rw [(hcentral _ z.2 g₀).mul_pow, hz', inv_mul_cancel]

theorem eq_of_proj_eq_of_two_pow (h2 : (2 : K) = 0) (hn : 0 < n) {g g' : SpecialLinearGroup (Fin n) K}
    {a : ℕ} (hg : g ^ (2 ^ a) = 1) (hg' : g' ^ (2 ^ a) = 1) (h : proj n K g = proj n K g') : g = g' := by
  have hz : g⁻¹ * g' ∈ scalars n K := proj_eq_proj_iff.1 h
  have hc : Commute g (g⁻¹ * g') := (scalars_commute hz g).symm
  have h1 : (g⁻¹ * g') ^ (2 ^ a) = 1 := by
    have h3 : g' ^ (2 ^ a) = g ^ (2 ^ a) * (g⁻¹ * g') ^ (2 ^ a) := by
      rw [← hc.mul_pow, mul_inv_cancel_left]
    rw [hg, one_mul] at h3
    rw [← h3]
    exact hg'
  have h4 := scalars_eq_one_of_two_pow h2 hn hz a h1
  exact inv_mul_eq_one.1 h4

theorem pow_scalar_of_conjAut_pow {A : GL (Fin n) K} (hn : 3 ≤ n) {m : ℕ}
    (h : conjAut n K A ^ m = 1) : ∃ c : Kˣ, A ^ m = GeneralLinearGroup.scalar (Fin n) c := by
  have h1 : conjAut n K (A ^ m) = 1 := by
    rw [map_pow]
    exact h
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn (A ^ m) 1
    (by rw [map_one, mul_one]; exact h1)
  exact ⟨c, hc.symm⟩

theorem comm_scalar_of_conjAut_comm {A B : GL (Fin n) K} (hn : 3 ≤ n)
    (h : conjAut n K B * conjAut n K A = conjAut n K A * conjAut n K B) :
    ∃ c : Kˣ, B * A * B⁻¹ * A⁻¹ = GeneralLinearGroup.scalar (Fin n) c := by
  have h1 : conjAut n K (B * A * B⁻¹ * A⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact h
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn (B * A * B⁻¹ * A⁻¹) 1
    (by rw [map_one, mul_one]; exact h1)
  exact ⟨c, hc.symm⟩

end CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin

end
