module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRigidityFieldRigid
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotPositionBNormalForm
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearPureGraph

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart)
open CFSG.Quasithin (perfectCore map_perfectCore)

section General

variable {P : Type*} [Group P]

theorem autFixSubgroup_conj (α ψ : MulAut P) :
    autFixSubgroup (ψ * α * ψ⁻¹) = (autFixSubgroup α).map ψ.toMonoidHom := by
  ext x
  rw [mem_autFixSubgroup]
  constructor
  · intro h
    refine ⟨ψ⁻¹ x, ?_, by simp⟩
    change α (ψ⁻¹ x) = ψ⁻¹ x
    have h' := congrArg (fun z => (ψ⁻¹ : MulAut P) z) h
    simp only [MulAut.mul_apply, MulAut.inv_apply_self] at h'
    exact h'
  · rintro ⟨z, hz, rfl⟩
    have hz' : α z = z := hz
    rw [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hz']

theorem autFixSubgroup_mulAut_conj (y : P) :
    autFixSubgroup (MulAut.conj y) = centralizer ({y} : Set P) := by
  ext x
  rw [mem_autFixSubgroup, MulAut.conj_apply, mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * y = (y * x * y⁻¹) * y := by rw [h]
      _ = y * x := by group
  · intro h
    calc y * x * y⁻¹ = x * y * y⁻¹ := by rw [h]
      _ = x := by group

theorem perfectCore_autFixSubgroup_conj [Finite P] (α ψ : MulAut P) :
    perfectCore (autFixSubgroup (ψ * α * ψ⁻¹)) =
      (perfectCore (autFixSubgroup α)).map ψ.toMonoidHom := by
  rw [autFixSubgroup_conj, map_perfectCore]

end General

section Inner

variable {n : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem exists_conjAut_eq_mulAut_conj (hn : 3 ≤ n) (A : GL (Fin n) K)
    (hA : conjAut n K A ^ 2 = 1) :
    ∃ y : projectiveSL n K, y * y = 1 ∧ conjAut n K A = MulAut.conj y := by
  have hA2 : conjAut n K (A * A) * fieldAut n K 1 = 1 := by
    rw [map_one, mul_one, map_mul, ← pow_two, hA]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn (A * A) 1 hA2
  obtain ⟨μ, hμ⟩ := isSquare_of_charTwo' (c : K)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hμ
    exact c.ne_zero hμ
  set m : Kˣ := Units.mk0 μ hμ0 with hm
  have hcm : c = m * m := Units.ext (by rw [Units.val_mul, hm, Units.val_mk0, hμ])
  set s : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) m⁻¹ with hs
  set B : GL (Fin n) K := A * s with hB
  have hB2 : B * B = 1 := by
    have hsA : s * A = A * s := GeneralLinearGroup.scalar_commute _ _
    calc B * B = (A * A) * (s * s) := by
          rw [hB]
          calc A * s * (A * s) = A * (s * A) * s := by simp only [mul_assoc]
            _ = A * (A * s) * s := by rw [hsA]
            _ = A * A * (s * s) := by simp only [mul_assoc]
      _ = GeneralLinearGroup.scalar (Fin n) (c * (m⁻¹ * m⁻¹)) := by
          rw [← hc, hs, ← map_mul, ← map_mul]
      _ = 1 := by
          rw [hcm, show m * m * (m⁻¹ * m⁻¹) = 1 by group, map_one]
  have hdet : (B : Matrix (Fin n) (Fin n) K).det = 1 := by
    have h1 : (B : Matrix (Fin n) (Fin n) K).det * (B : Matrix (Fin n) (Fin n) K).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, hB2, Units.val_one, Matrix.det_one]
    exact eq_one_of_mul_self_eq_one_charTwo h1
  set B' : SpecialLinearGroup (Fin n) K := ⟨B, hdet⟩ with hB'
  have hBB' : SpecialLinearGroup.toGL B' = B := Units.ext rfl
  have hcB : conjAut n K A = conjAut n K (SpecialLinearGroup.toGL B') := by
    rw [hBB', hB, map_mul, hs, conjAut_scalar, mul_one]
  refine ⟨proj n K B', ?_, by rw [hcB, conjAut_toGL]⟩
  have hB'2 : B' * B' = 1 := by
    apply Subtype.ext
    have := congrArg (fun X : GL (Fin n) K => (X : Matrix (Fin n) (Fin n) K)) hB2
    simpa using this
  rw [← map_mul, hB'2, map_one]

end Inner

section Std

variable {n : ℕ} {K : Type} [Field K] [Finite K]

@[expose] def IsStdCore (X : Subgroup (projectiveSL n K)) : Prop :=
  (∃ (k : ℕ) (P : InvPlacement n k), P.elt K ≠ 1 ∧
      X = perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K)))) ∨
    ∃ C : GL (Fin n) K, ((C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = UnitaryHigher.blockSwapJ n r) ∧
      X = perfectCore (autFixSubgroup (conjAut n K C * dualAut n K))

theorem exists_isStdCore_of_linearFieldPart_eq_one {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hn : 3 ≤ n) (α : MulAut (projectiveSL n K)) (hα2 : α ^ 2 = 1) (hα1 : α ≠ 1)
    (hfc : linearFieldPart K hn α = 1) :
    ∃ (X : Subgroup (projectiveSL n K)) (ψ : MulAut (projectiveSL n K)), IsStdCore X ∧
      perfectCore (autFixSubgroup α) = X.map ψ.toMonoidHom := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have := Finite.one_lt_card (α := K)
      rw [hK, pow_zero] at this
      omega
    · exact h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  obtain ⟨A, ε, hε, rfl⟩ := (linearFieldPart_eq_one_iff hn α).1 hfc
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  ·
    rw [pow_zero, mul_one] at hα2 hα1 ⊢
    obtain ⟨y, hyy, hy⟩ := exists_conjAut_eq_mulAut_conj hn A hα2
    obtain ⟨k, P, c, hc⟩ := exists_conj_eq_elt hyy
    have hy' : MulAut.conj y =
        MulAut.conj c⁻¹ * MulAut.conj (P.elt K) * (MulAut.conj c⁻¹)⁻¹ := by
      rw [← hc, ← map_inv, ← map_mul, ← map_mul, inv_inv]
      congr 1
      group
    refine ⟨perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))), MulAut.conj c⁻¹,
      Or.inl ⟨k, P, ?_, rfl⟩, ?_⟩
    · intro h1
      apply hα1
      rw [hy, hy', h1, map_one, mul_one, mul_inv_cancel]
    · rw [hy, hy', perfectCore_autFixSubgroup_conj, autFixSubgroup_mulAut_conj]
  ·
    rw [pow_one] at hα2 ⊢
    obtain ⟨-, ⟨H, C, -, hHC, hC⟩, -⟩ :=
      UnitaryHigher.even_linear_pure_graph_involution_normal_forms hf hK hn A hα2
    refine ⟨perfectCore (autFixSubgroup (conjAut n K C * dualAut n K)), conjAut n K H,
      Or.inr ⟨C, ?_, rfl⟩, ?_⟩
    · rcases hC with ⟨h1, -⟩ | ⟨r, hr, hJ, -⟩
      · exact Or.inl h1
      · exact Or.inr ⟨r, hr, hJ⟩
    · rw [hHC, perfectCore_autFixSubgroup_conj]

theorem innerGraphFieldRigid_of_std {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n)
    (hstd : ∀ X₁ X₂ : Subgroup (projectiveSL n K), IsStdCore X₁ → IsStdCore X₂ →
      FieldRigidIn hn X₁ X₂) :
    InnerGraphFieldRigid K hn := by
  intro α₁ α₂ h₁ h₂ h₁' h₂' hf₁ hf₂
  obtain ⟨X₁, ψ₁, hX₁, he₁⟩ := exists_isStdCore_of_linearFieldPart_eq_one hK hn α₁ h₁ h₁' hf₁
  obtain ⟨X₂, ψ₂, hX₂, he₂⟩ := exists_isStdCore_of_linearFieldPart_eq_one hK hn α₂ h₂ h₂' hf₂
  rw [he₁, he₂]
  exact (hstd X₁ X₂ hX₁ hX₂).map ψ₁ ψ₂

end Std

end CFSG.SeitzReduction.LinearPilot
