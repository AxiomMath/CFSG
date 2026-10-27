module

public import CFSG.CGT.Foote82.T66.CaseIIBasic

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.PGLModel

namespace CaseII

abbrev I6 : Type := Fin 2 ⊕ Fin 2 ⊕ Fin 2

abbrev mat (g : GL I6 (ZMod 2)) : Matrix I6 I6 (ZMod 2) := (g : Matrix I6 I6 (ZMod 2))

theorem cdim6_eq_rank (g : GL I6 (ZMod 2)) : cdim6 g = (mat g - 1).rank := rfl

theorem cdim6_conj (g a : GL I6 (ZMod 2)) : cdim6 (g * a * g⁻¹) = cdim6 a := by
  rw [cdim6_eq_rank, cdim6_eq_rank]
  have e : mat (g * a * g⁻¹) - 1 = mat g * (mat a - 1) * mat g⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    simp [Matrix.GeneralLinearGroup.coe_mul, mul_assoc]
  rw [e, Matrix.rank_mul_eq_left_of_isUnit_det, Matrix.rank_mul_eq_right_of_isUnit_det]
  · exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  · exact (Matrix.isUnit_iff_isUnit_det _).1 g⁻¹.isUnit

@[expose] def iu : I6 := Sum.inr (Sum.inr 0)
@[expose] def iv : I6 := Sum.inr (Sum.inr 1)
@[expose] def ix : I6 := Sum.inl 0
@[expose] def iy : I6 := Sum.inr (Sum.inl 0)

@[expose] def matR₀ : Matrix I6 I6 (ZMod 2) := Matrix.of fun i j =>
  if i = j then 1 else if i = iu ∧ j = iv then 1 else 0

@[expose] def matR₁ : Matrix I6 I6 (ZMod 2) := Matrix.of fun i j =>
  if Equiv.swap ix iy i = j then 1 else 0

@[expose] def matSuv : Matrix I6 I6 (ZMod 2) := Matrix.of fun i j =>
  if Equiv.swap iu iv i = j then 1 else 0

@[expose] def matPxy : Matrix I6 I6 (ZMod 2) := Matrix.of fun i j =>
  if i = j then 1 else if i = iy ∧ j = ix then 1 else 0

@[expose] def matQxy : Matrix I6 I6 (ZMod 2) := Matrix.of fun i j =>
  if i = j then 1 else if i = ix ∧ j = iy then 1 else 0

theorem matR₀_mul_self : matR₀ * matR₀ = 1 := by decide

theorem matR₁_mul_self : matR₁ * matR₁ = 1 := by decide

theorem matR₀_comm : matR₀ * matR₁ = matR₁ * matR₀ := by decide

theorem isUnit_det_of_mul_self {A : Matrix I6 I6 (ZMod 2)} (h : A * A = 1) : IsUnit A.det := by
  have : A.det * A.det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
  exact IsUnit.of_mul_eq_one _ this

theorem rank_matR₀ : (matR₀ - 1).rank = 1 := by
  have h1 : (matR₀ - 1) * matSuv = Matrix.diagonal (Pi.single iu 1) := by decide
  have hS : IsUnit matSuv.det := isUnit_det_of_mul_self (by decide)
  rw [← Matrix.rank_mul_eq_left_of_isUnit_det matSuv (matR₀ - 1) hS, h1, Matrix.rank_diagonal]
  decide

theorem rank_matR₁ : (matR₁ - 1).rank = 1 := by
  have h1 : matPxy * (matR₁ - 1) * matQxy = Matrix.diagonal (Pi.single ix 1) := by decide
  have hP : IsUnit matPxy.det := isUnit_det_of_mul_self (by decide)
  have hQ : IsUnit matQxy.det := isUnit_det_of_mul_self (by decide)
  rw [← Matrix.rank_mul_eq_right_of_isUnit_det matPxy (matR₁ - 1) hP,
    ← Matrix.rank_mul_eq_left_of_isUnit_det matQxy (matPxy * (matR₁ - 1)) hQ, h1,
    Matrix.rank_diagonal]
  decide

@[expose] def refl₀ : GL I6 (ZMod 2) := ⟨matR₀, matR₀, matR₀_mul_self, matR₀_mul_self⟩

@[expose] def refl₁ : GL I6 (ZMod 2) := ⟨matR₁, matR₁, matR₁_mul_self, matR₁_mul_self⟩

theorem refl₀_mem : refl₀ ∈ orthogonalMinus 2 (ZMod 2) 1 1 := by
  apply Subgroup.subset_closure
  show ∀ w : I6 → ZMod 2, minusQuadForm 2 (1 : ZMod 2) 1 (matR₀.mulVec w) =
    minusQuadForm 2 (1 : ZMod 2) 1 w
  decide

theorem refl₁_mem : refl₁ ∈ orthogonalMinus 2 (ZMod 2) 1 1 := by
  apply Subgroup.subset_closure
  show ∀ w : I6 → ZMod 2, minusQuadForm 2 (1 : ZMod 2) 1 (matR₁.mulVec w) =
    minusQuadForm 2 (1 : ZMod 2) 1 w
  decide

theorem refl₀_mul_self : refl₀ * refl₀ = 1 := Units.ext matR₀_mul_self

theorem refl₁_mul_self : refl₁ * refl₁ = 1 := Units.ext matR₁_mul_self

theorem refl₀_ne_one : refl₀ ≠ 1 := by
  intro h
  have := congrArg (fun g : GL I6 (ZMod 2) => (g : Matrix I6 I6 (ZMod 2)) iu iv) h
  revert this
  decide

theorem refl₁_ne_one : refl₁ ≠ 1 := by
  intro h
  have := congrArg (fun g : GL I6 (ZMod 2) => (g : Matrix I6 I6 (ZMod 2)) ix iy) h
  revert this
  decide

theorem refl₀_ne_refl₁ : refl₀ ≠ refl₁ := by
  intro h
  have := congrArg (fun g : GL I6 (ZMod 2) => (g : Matrix I6 I6 (ZMod 2)) iu iv) h
  revert this
  decide

theorem orderOf_eq_two_of_mul_self {G : Type*} [Group G] {g : G} (h : g * g = 1) (h1 : g ≠ 1) :
    orderOf g = 2 :=
  orderOf_eq_prime (by rw [sq, h]) h1

theorem orderOf_refl₀ : orderOf refl₀ = 2 := orderOf_eq_two_of_mul_self refl₀_mul_self refl₀_ne_one

theorem orderOf_refl₁ : orderOf refl₁ = 2 := orderOf_eq_two_of_mul_self refl₁_mul_self refl₁_ne_one

theorem refl_comm : refl₀ * refl₁ = refl₁ * refl₀ := Units.ext matR₀_comm

theorem cdim6_refl₀ : cdim6 refl₀ = 1 := rank_matR₀

theorem cdim6_refl₁ : cdim6 refl₁ = 1 := rank_matR₁

theorem range_refl_inf :
    LinearMap.range (Matrix.mulVecLin (mat refl₀ - 1)) ⊓
      LinearMap.range (Matrix.mulVecLin (mat refl₁ - 1)) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
  rw [Submodule.mem_bot]
  have key : ∀ (a b : I6 → ZMod 2), (matR₁ - 1).mulVec b = (matR₀ - 1).mulVec a →
      (matR₀ - 1).mulVec a = 0 := by
    intro a b h
    funext i
    have hu := congrFun h iu
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Matrix.mulVec, dotProduct,
      matR₀, matR₁, Matrix.of_apply, Fintype.sum_sum_type, Fin.sum_univ_two, iu, iv, ix, iy,
      Equiv.swap_apply_def, Pi.zero_apply] at hu ⊢
    revert hu
    rcases i with i | i | i <;> fin_cases i <;> simp
  exact key a b hb

theorem mem_range_conj {g M : GL I6 (ZMod 2)} {x : I6 → ZMod 2}
    (hx : x ∈ LinearMap.range (Matrix.mulVecLin (mat (g * M * g⁻¹) - 1))) :
    (mat g⁻¹).mulVec x ∈ LinearMap.range (Matrix.mulVecLin (mat M - 1)) := by
  obtain ⟨a, rfl⟩ := hx
  refine ⟨(mat g⁻¹).mulVec a, ?_⟩
  have e : mat (g * M * g⁻¹) - 1 = mat g * (mat M - 1) * mat g⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    simp [Matrix.GeneralLinearGroup.coe_mul, mul_assoc]
  have hgi : mat g⁻¹ * mat g = 1 := by
    simp [mat, ← Matrix.GeneralLinearGroup.coe_mul]
  simp only [Matrix.mulVecLin_apply]
  rw [e, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    hgi, Matrix.one_mul]

theorem range_refl_conj_inf (g : GL I6 (ZMod 2)) :
    LinearMap.range (Matrix.mulVecLin (mat (g * refl₀ * g⁻¹) - 1)) ⊓
      LinearMap.range (Matrix.mulVecLin (mat (g * refl₁ * g⁻¹) - 1)) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨h0, h1⟩
  have h := (Submodule.mem_inf.2 ⟨mem_range_conj h0, mem_range_conj h1⟩ :
    (mat g⁻¹).mulVec x ∈ _ ⊓ _)
  rw [range_refl_inf, Submodule.mem_bot] at h
  rw [Submodule.mem_bot]
  have hg : mat g * mat g⁻¹ = 1 := by
    simp [mat, ← Matrix.GeneralLinearGroup.coe_mul]
  calc x = (mat g * mat g⁻¹).mulVec x := by rw [hg, Matrix.one_mulVec]
    _ = (mat g).mulVec ((mat g⁻¹).mulVec x) := by rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [h, Matrix.mulVec_zero]

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {G L : Subgroup (GLV V)} {z : GLV V} {v : V} {H₁ : Subgroup (GLV V)}
  {ψ : ↥H₁ ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1)}

namespace Ctx

variable (c : Ctx G L z v H₁ ψ)
include c

theorem orderOf_psi_z : orderOf ((ψ ⟨z, c.z_mem⟩ : ↥(orthogonalMinus 2 (ZMod 2) 1 1)) :
    GL I6 (ZMod 2)) = 2 := by
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, c.orderOf_z]

theorem exists_g (hG1 : CaseIIG1) :
    ∃ g : GLV V, ∃ hg : g ∈ HH G L v,
      (g * z * g⁻¹) * z = z * (g * z * g⁻¹) ∧ g * z * g⁻¹ ≠ z ∧
      LinearMap.range (Matrix.mulVecLin (mat (ψ ⟨z, c.z_mem⟩) - 1)) ⊓
        LinearMap.range (Matrix.mulVecLin
          (mat (ψ ⟨g, c.H_le hg⟩ * ψ ⟨z, c.z_mem⟩ * (ψ ⟨g, c.H_le hg⟩)⁻¹) - 1)) = ⊥ := by
  obtain ⟨r, hr⟩ : ∃ r : GL I6 (ZMod 2),
      r = ((ψ ⟨z, c.z_mem⟩ : ↥(orthogonalMinus 2 (ZMod 2) 1 1)) : GL I6 (ZMod 2)) := ⟨_, rfl⟩
  have hrO : r ∈ orthogonalMinus 2 (ZMod 2) 1 1 := hr ▸ (ψ ⟨z, c.z_mem⟩).2
  have hr2 : orderOf r = 2 := hr ▸ c.orderOf_psi_z
  have hr1 : cdim6 r = 1 := hr ▸ c.data.ψ_z
  obtain ⟨g₁, hg₁, hg₁r⟩ := (hG1 refl₀ refl₀_mem orderOf_refl₀ cdim6_refl₀).1 r hrO hr2 hr1
  have hg₁O : g₁ ∈ orthogonalMinus 2 (ZMod 2) 1 1 := omega_le_O hg₁
  obtain ⟨r', hr'⟩ : ∃ r' : GL I6 (ZMod 2), r' = g₁ * refl₁ * g₁⁻¹ := ⟨_, rfl⟩
  have hr'O : r' ∈ orthogonalMinus 2 (ZMod 2) 1 1 :=
    hr' ▸ Subgroup.mul_mem _ (Subgroup.mul_mem _ hg₁O refl₁_mem) (Subgroup.inv_mem _ hg₁O)
  have hr'2 : orderOf r' = 2 := by
    rw [hr', ← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_refl₁]
  have hr'1 : cdim6 r' = 1 := by rw [hr', cdim6_conj, cdim6_refl₁]
  obtain ⟨g₂, hg₂, hg₂r⟩ := (hG1 r hrO hr2 hr1).1 r' hr'O hr'2 hr'1
  obtain ⟨g, hg⟩ : ∃ g : GLV V, g = (ψ.symm ⟨g₂, omega_le_O hg₂⟩ : GLV V) := ⟨_, rfl⟩
  have hgH₁ : g ∈ H₁ := hg ▸ (ψ.symm ⟨g₂, omega_le_O hg₂⟩).2
  have hψg : ψ ⟨g, hgH₁⟩ = ⟨g₂, omega_le_O hg₂⟩ := by
    have : (⟨g, hgH₁⟩ : ↥H₁) = ψ.symm ⟨g₂, omega_le_O hg₂⟩ := Subtype.ext hg
    rw [this, MulEquiv.apply_symm_apply]
  have hgH : g ∈ HH G L v := by
    rw [c.mem_H_iff hgH₁, hψg]
    exact hg₂
  refine ⟨g, hgH, ?_, ?_, ?_⟩
  ·
    have hu : g * z * g⁻¹ ∈ H₁ :=
      H₁.mul_mem (H₁.mul_mem hgH₁ c.z_mem) (H₁.inv_mem hgH₁)
    have hψu : ((ψ ⟨g * z * g⁻¹, hu⟩ : ↥(orthogonalMinus 2 (ZMod 2) 1 1)) : GL I6 (ZMod 2)) =
        r' := by
      have e : (⟨g * z * g⁻¹, hu⟩ : ↥H₁) = ⟨g, hgH₁⟩ * ⟨z, c.z_mem⟩ * ⟨g, hgH₁⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, hψg]
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hr]
      exact hg₂r
    have hcomm : r' * r = r * r' := by
      rw [hr', ← hg₁r]
      simp only [mul_assoc, inv_mul_cancel_left]
      rw [← mul_assoc refl₁ refl₀, ← refl_comm, mul_assoc]
    have key : (⟨g * z * g⁻¹, hu⟩ : ↥H₁) * ⟨z, c.z_mem⟩ = ⟨z, c.z_mem⟩ * ⟨g * z * g⁻¹, hu⟩ := by
      apply ψ.injective
      apply Subtype.ext
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hψu, ← hr]
      exact hcomm
    exact congrArg Subtype.val key
  ·
    intro hEq
    have hu : g * z * g⁻¹ ∈ H₁ :=
      H₁.mul_mem (H₁.mul_mem hgH₁ c.z_mem) (H₁.inv_mem hgH₁)
    have hψu : ((ψ ⟨g * z * g⁻¹, hu⟩ : ↥(orthogonalMinus 2 (ZMod 2) 1 1)) : GL I6 (ZMod 2)) =
        r' := by
      have e : (⟨g * z * g⁻¹, hu⟩ : ↥H₁) = ⟨g, hgH₁⟩ * ⟨z, c.z_mem⟩ * ⟨g, hgH₁⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, hψg]
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hr]
      exact hg₂r
    have h1 : r' = r := by
      rw [← hψu, hr, show (⟨g * z * g⁻¹, hu⟩ : ↥H₁) = ⟨z, c.z_mem⟩ from Subtype.ext hEq]
    apply refl₀_ne_refl₁
    have h2 : g₁ * refl₁ * g₁⁻¹ = g₁ * refl₀ * g₁⁻¹ := by rw [← hr', h1, hg₁r]
    have h3 := congrArg (fun x => g₁⁻¹ * x * g₁) h2
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at h3
    exact h3.symm
  ·
    have e1 : mat (ψ ⟨g, c.H_le hgH⟩ * ψ ⟨z, c.z_mem⟩ * (ψ ⟨g, c.H_le hgH⟩)⁻¹) =
        mat (g₁ * refl₁ * g₁⁻¹) := by
      have h2 : ((ψ ⟨g, c.H_le hgH⟩ : ↥(orthogonalMinus 2 (ZMod 2) 1 1)) : GL I6 (ZMod 2)) = g₂ :=
        congrArg Subtype.val hψg
      rw [Subgroup.coe_inv, h2, ← hr, hg₂r, hr']
    have e0 : mat ((ψ ⟨z, c.z_mem⟩ : ↥(orthogonalMinus 2 (ZMod 2) 1 1)) : GL I6 (ZMod 2)) =
        mat (g₁ * refl₀ * g₁⁻¹) := by
      rw [← hr, hg₁r]
    rw [e1, e0]
    exact range_refl_conj_inf g₁

end Ctx

end CaseII

end CFSG.CGT.Foote82
