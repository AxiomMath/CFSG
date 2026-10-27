module

public import CFSG.GH74.Generic.S45.LCoverEq
public import CFSG.GH74.Generic.S45.LSymFix
public import CFSG.GH74.Generic.S45.LSporCommon

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.LieType.Steinberg Subgroup CFSG.ComponentClassification
open CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix

theorem proj_slConjugation_slGraphAut {F : Type} [Field F] {m : ℕ}
    (B : Matrix.GeneralLinearGroup (Fin m) F) (g : Matrix.SpecialLinearGroup (Fin m) F) :
    LinearFlag.proj m F ((CatalogueBHigherLinearAction.slConjugation m F B *
        CatalogueBGraphForm.slGraphAut m F) g) =
      (LinearFlag.conjAut m F B * LinearFlag.dualAut m F) (LinearFlag.proj m F g) := by
  change LinearFlag.proj m F (CatalogueBHigherLinearAction.slConjugation m F B
      (CatalogueBGraphForm.slGraphAut m F g)) = _
  rw [MulAut.mul_apply, LinearFlag.dualAut_proj, LinearFlag.conjAut_proj]
  rfl

theorem exists_symmetric_graph_fixed {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2) {m : ℕ}
    (hm : 3 ≤ m) (B : Matrix.GeneralLinearGroup (Fin m) F)
    (hB : (B : Matrix (Fin m) (Fin m) F)ᵀ = B) :
    ∃ c : Matrix.SpecialLinearGroup (Fin m) F,
      (CatalogueBHigherLinearAction.slConjugation m F B * CatalogueBGraphForm.slGraphAut m F) c = c ∧
        orderOf (LinearFlag.proj m F c) = 4 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hBdet : IsUnit (B : Matrix (Fin m) (Fin m) F).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
  obtain ⟨cm, hdet, hcB, hnsc, hc4⟩ := exists_isometry_order_four h2 hm
    (B : Matrix (Fin m) (Fin m) F) hB hBdet
  let c : Matrix.SpecialLinearGroup (Fin m) F := ⟨cm, hdet⟩
  have hcc : (c : Matrix (Fin m) (Fin m) F) = cm := rfl
  refine ⟨c, ?_, ?_⟩
  · apply Subtype.ext
    change ((CatalogueBHigherLinearAction.slConjugation m F B
        (CatalogueBGraphForm.slGraphAut m F c) : Matrix.SpecialLinearGroup (Fin m) F) :
          Matrix (Fin m) (Fin m) F) = _
    rw [CatalogueBHigherLinearAction.slConjugation_matrix, CatalogueBGraphForm.slGraphAut_matrix]
    set c' : Matrix (Fin m) (Fin m) F :=
      ((c⁻¹ : Matrix.SpecialLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F) with hc'
    have h1 : c' * cm = 1 := by
      have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin m) F =>
        (g : Matrix (Fin m) (Fin m) F)) (inv_mul_cancel c)
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at this
      exact this
    have h2' : B.val * cmᵀ = c' * B.val := by
      calc B.val * cmᵀ = (c' * cm) * B.val * cmᵀ := by rw [h1, Matrix.one_mul]
        _ = c' * (cm * B.val * cmᵀ) := by simp only [Matrix.mul_assoc]
        _ = c' * B.val := by rw [hcB]
    have h3 : cm * B.val = B.val * c'ᵀ := by
      have := congrArg Matrix.transpose h2'
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hB] at this
      exact this
    calc B.val * c'ᵀ * (B⁻¹).val = cm * B.val * (B⁻¹).val := by rw [h3]
      _ = cm := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  · have hc4' : c ^ 4 = 1 := by
      apply Subtype.ext
      have : c ^ 4 = (c * c) * (c * c) := by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      rw [this]
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hcc]
      exact hc4
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := LinearFlag.proj m F c)
      (by
        rw [pow_one, ← map_pow, LinearFlag.proj_eq_one_iff]
        rintro ⟨l, -, hl⟩
        apply hnsc (l : F)
        have : ((c ^ 2 : Matrix.SpecialLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F) =
            cm * cm := by
          rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, hcc]
        rw [← this, hl, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal])
      (by
        rw [show 2 ^ (1 + 1) = 4 by norm_num, ← map_pow, hc4', map_one])
    rw [h]
    norm_num

theorem exists_symmetric_graph_fixed_proj {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2)
    {m : ℕ} (hm : 3 ≤ m) (B : Matrix.GeneralLinearGroup (Fin m) F)
    (hB : (B : Matrix (Fin m) (Fin m) F)ᵀ = B) :
    ∃ p : LinearFlag.projectiveSL m F,
      (LinearFlag.conjAut m F B * LinearFlag.dualAut m F) p = p ∧ orderOf p = 4 := by
  obtain ⟨c, hc, hord⟩ := exists_symmetric_graph_fixed hF hm B hB
  refine ⟨LinearFlag.proj m F c, ?_, hord⟩
  rw [← proj_slConjugation_slGraphAut, hc]

theorem Hyp1310.false_of_symmetric_graph {K : Type} [Group K] [Finite K] {y : MulAut K}
    {L : Subgroup K} (hyp : Hyp1310 K y L) {yb : MulAut (K ⧸ Subgroup.center K)}
    (hyb : ∀ k : K, yb (QuotientGroup.mk k) = QuotientGroup.mk (y k))
    {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2) {m : ℕ} (hm : 3 ≤ m)
    (ψ : K ⧸ Subgroup.center K ≃* LinearFlag.projectiveSL m F) (B : Matrix.GeneralLinearGroup (Fin m) F)
    (hB : (B : Matrix (Fin m) (Fin m) F)ᵀ = B)
    (hψ : ∀ s, ψ (yb s) = (LinearFlag.conjAut m F B * LinearFlag.dualAut m F) (ψ s)) : False := by
  classical
  obtain ⟨c, hτc, hord'⟩ := exists_symmetric_graph_fixed hF hm B hB
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨hKp, hZ2, -, -, hno4, -⟩ := hyp.data
  have hPp : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin (m' + 1)) F) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_perfect (m' + 1) F
      (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  have hsplit : ∀ (E : Type) [Group E] [Finite E]
      (π : E →* Matrix.SpecialLinearGroup (Fin (m' + 1)) F), Function.Surjective π →
        π.ker ≤ Subgroup.center E → IsPGroup 2 π.ker →
          ∃ σ : Matrix.SpecialLinearGroup (Fin (m' + 1)) F →* E, ∀ x, π (σ x) = x :=
    fun E _ _ π hπ hcen h2' =>
      (sl_central_two_extension_splitting m' hF hπ hcen h2').imp fun _ h => h.1
  let η : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K)
  have hη : Function.Surjective η := QuotientGroup.mk'_surjective _
  have hηker : η.ker = Subgroup.center K := QuotientGroup.ker_mk' _
  have hη2 : IsPGroup 2 η.ker := by rw [hηker]; exact hZ2
  let β : Matrix.SpecialLinearGroup (Fin (m' + 1)) F →* K ⧸ Subgroup.center K :=
    ψ.symm.toMonoidHom.comp (LinearFlag.proj (m' + 1) F)
  have hβ : Function.Surjective β := ψ.symm.surjective.comp (LinearFlag.proj_surjective (m' + 1) F)
  let τ : MulAut (Matrix.SpecialLinearGroup (Fin (m' + 1)) F) :=
    CatalogueBHigherLinearAction.slConjugation (m' + 1) F B *
      CatalogueBGraphForm.slGraphAut (m' + 1) F
  have hτ : ∀ g, β (τ g) = yb (β g) := by
    intro g
    change ψ.symm (LinearFlag.proj (m' + 1) F (τ g)) = yb (ψ.symm (LinearFlag.proj (m' + 1) F g))
    rw [proj_slConjugation_slGraphAut]
    apply ψ.injective
    rw [MulEquiv.apply_symm_apply, hψ, MulEquiv.apply_symm_apply]
  have hord : orderOf (β c) = 4 := by
    change orderOf (ψ.symm (LinearFlag.proj (m' + 1) F c)) = 4
    rw [MulEquiv.orderOf_eq]
    exact hord'
  obtain ⟨x, hx, h4⟩ := exists_fixed_dvd_of_cover hKp hPp hsplit hη hηker.le hη2 hβ
    (y := y) (yb := yb) (fun k => (hyb k).symm) hτ hτc (by rw [hord])
  exact hno4 x hx h4

end CFSG.GH74.Generic.S45
