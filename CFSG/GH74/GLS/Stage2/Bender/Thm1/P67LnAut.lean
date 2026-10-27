module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Odd

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem exists_conj_field_of_odd (hn : 3 ≤ n) {α : MulAut (projectiveSL n K)} {m : ℕ}
    (hm : Odd m) (hα : α ^ m = 1) :
    ∃ (A : GL (Fin n) K) (σ : K ≃+* K), α = conjAut n K A * fieldAut n K σ := by
  have hR : α ∈ standardAutGroup n K := by rw [(automorphism_generation hn).1]; trivial
  have hδδ : dualAut n K * dualAut n K = 1 :=
    (standard_automorphism_transport (K := K) (n := n)).2.2.2.1
  have hsq : α * α ∈ semilinearAutGroup n K := by
    rcases mem_or_mul_dualAut_mem hR with h | h
    · exact mul_mem h h
    · have h' := dualAut_mul_mul_dualAut_mem h
      have : α * α = (α * dualAut n K) * (dualAut n K * (α * dualAut n K) * dualAut n K) := by
        calc α * α = α * (dualAut n K * dualAut n K) * α * (dualAut n K * dualAut n K) := by
              rw [hδδ]; group
          _ = _ := by group
      rw [this]
      exact mul_mem h h'
  obtain ⟨k, rfl⟩ := hm
  have hα' : α = (α * α) ^ (k + 1) := by
    have h1 : α ^ (2 * k + 1) = 1 := hα
    calc α = α ^ (2 * k + 1) * α := by rw [h1, one_mul]
      _ = (α * α) ^ (k + 1) := by rw [← pow_succ, ← sq, ← pow_mul]; ring_nf
  rw [hα']
  exact mem_semilinearAutGroup_iff.mp (pow_mem hsq _)

end Odd

section Field

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem isCyclic_ringAut (K : Type) [Field K] [Finite K] : IsCyclic (K ≃+* K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hp⟩ := CharP.exists K
  have hpp : p.Prime := CharP.char_is_prime K p
  obtain ⟨m, -, hm⟩ := FiniteField.card K p
  exact (card_ringAut_and_isCyclic hpp K (by rw [Nat.card_eq_fintype_card, hm])).2

theorem exists_fieldHom (hn : 3 ≤ n) (S : Subgroup (MulAut (projectiveSL n K)))
    (hS : ∀ α ∈ S, α ∈ semilinearAutGroup n K) :
    ∃ φ : ↥S →* (K ≃+* K), ∀ α : ↥S, ∃ A : GL (Fin n) K,
      (α : MulAut (projectiveSL n K)) = conjAut n K A * fieldAut n K (φ α) := by
  choose A σ h using fun α : ↥S => mem_semilinearAutGroup_iff.mp (hS α α.2)
  have hu : ∀ {A B : GL (Fin n) K} {σ τ : K ≃+* K},
      conjAut n K A * fieldAut n K σ = conjAut n K B * fieldAut n K τ → σ = τ := by
    intro A B σ τ hh
    exact (ProjectivePlane.standard_form_unique hn (ε := 0) (η := 0) (by norm_num) (by norm_num)
      (by simpa using hh)).1
  refine ⟨{ toFun := σ, map_one' := ?_, map_mul' := ?_ }, fun α => ⟨A α, h α⟩⟩
  · refine hu (A := A 1) (B := 1) ?_
    rw [← h 1]
    simp
  · intro α β
    apply hu
    rw [← h (α * β), Subgroup.coe_mul, h α, h β, conjAut_mul_fieldAut_mul]

theorem exists_inner_diag_of_elem (hn : 3 ≤ n) {r : ℕ} [Fact r.Prime]
    {V : Subgroup (MulAut (projectiveSL n K))} (hVe : IsElementaryAbelian r ↥V)
    (hVc : Nat.card ↥V = r ^ 2) (hVE : ∀ α ∈ V, α ∈ semilinearAutGroup n K) :
    ∃ v ∈ V, v ≠ 1 ∧ ∃ A : GL (Fin n) K, v = conjAut n K A := by
  obtain ⟨φ, hφ⟩ := exists_fieldHom hn V hVE
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    by_contra hv1
    obtain ⟨A, hA⟩ := hφ v
    rw [hv, map_one, mul_one] at hA
    exact hcon v v.2 (fun h => hv1 (Subtype.ext h)) A hA
  have : IsCyclic ↥V := by
    have := isCyclic_ringAut K
    exact isCyclic_of_injective φ hinj
  exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hVc this

end Field

section Unip

variable {K : Type} [Field K] [Finite K] {n : ℕ}

omit [Finite K] in
theorem conjAut_scalar' (u : Kˣ) :
    conjAut n K (Matrix.GeneralLinearGroup.scalar (Fin n) u) = 1 := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  rw [conjAut_proj, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, Units.mul_inv_eq_iff_eq_mul]
  have h1 : ((Matrix.GeneralLinearGroup.scalar (Fin n) u : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (u : K) • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [h1, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

omit [Finite K] in
theorem scalar_commute' (u : Kˣ) (A : GL (Fin n) K) :
    Commute (Matrix.GeneralLinearGroup.scalar (Fin n) u : GL (Fin n) K) A := by
  apply Units.ext
  have h1 : ((Matrix.GeneralLinearGroup.scalar (Fin n) u : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (u : K) • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  change _ * _ = _ * _
  rw [h1, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem coprime_card_units (p : ℕ) [Fact p.Prime] [CharP K p] : Nat.Coprime (Nat.card Kˣ) p := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hp, hm⟩ := FiniteField.card K p
  have h1 : Nat.card Kˣ = p ^ (m : ℕ) - 1 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, hm]
  rw [h1]
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_)
  have h2 : p ∣ p ^ (m : ℕ) := dvd_pow_self p m.ne_zero
  have h3 : 1 ≤ p ^ (m : ℕ) := Nat.one_le_pow _ _ hp.pos
  have h4 : p ∣ p ^ (m : ℕ) - (p ^ (m : ℕ) - 1) := Nat.dvd_sub h2 h
  rw [Nat.sub_sub_self h3] at h4
  exact hp.one_lt.ne' (Nat.dvd_one.mp h4)

theorem exists_unipotent_lift (hn : 3 ≤ n) (p : ℕ) [Fact p.Prime] [CharP K p]
    {A : GL (Fin n) K} (hA : conjAut n K A ^ p = 1) :
    ∃ g : Matrix.SpecialLinearGroup (Fin n) K,
      conjAut n K A = MulAut.conj (proj n K g) ∧ (g : Matrix (Fin n) (Fin n) K) ^ p = 1 := by
  have h1 : conjAut n K (A ^ p) = 1 := by rw [map_pow]; exact hA
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn (A ^ p) 1 (by simpa using h1)
  set μ : Kˣ := (powCoprime (coprime_card_units p)).symm c with hμ
  have hμp : μ ^ p = c := by
    have := (powCoprime (coprime_card_units (K := K) p)).apply_symm_apply c
    rw [powCoprime_apply] at this
    exact this
  set A' : GL (Fin n) K := Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹ * A with hA'
  have hA'p : A' ^ p = 1 := by
    rw [hA', (scalar_commute' μ⁻¹ A).mul_pow, ← map_pow, ← hc, ← map_mul, inv_pow, hμp,
      inv_mul_cancel, map_one]
  have hMp : ((A' : Matrix (Fin n) (Fin n) K)) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hA'p]; rfl
  have hdet : (A' : Matrix (Fin n) (Fin n) K).det = 1 := by
    have h2 : (A' : Matrix (Fin n) (Fin n) K).det ^ p = 1 := by
      rw [← Matrix.det_pow, hMp, Matrix.det_one]
    have h3 : ((A' : Matrix (Fin n) (Fin n) K).det - 1) ^ p = 0 := by
      rw [sub_pow_char, h2, one_pow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.mp h3)
  let g : Matrix.SpecialLinearGroup (Fin n) K := ⟨(A' : Matrix (Fin n) (Fin n) K), hdet⟩
  refine ⟨g, ?_, hMp⟩
  have hAeq : A = Matrix.GeneralLinearGroup.scalar (Fin n) μ * A' := by
    rw [hA', ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have htoGL : (Matrix.SpecialLinearGroup.toGL g : GL (Fin n) K) = A' := Units.ext rfl
  rw [← conjAut_toGL, htoGL, hAeq, map_mul, conjAut_scalar', one_mul]

end Unip

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln
