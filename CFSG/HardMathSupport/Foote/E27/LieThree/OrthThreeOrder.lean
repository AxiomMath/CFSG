module

public import CFSG.HardMathSupport.Foote.E27.LieThree.OrthSylowBound
public import CFSG.RankThree.PartOne.N143.O7Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Foote.E27

open Matrix CFSG.RankThree.PartOne.N143.O7 CFSG.Assembly.LowTwoRank

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

@[expose] noncomputable def formB : LinearMap.BilinForm (ZMod 3) (Idx → ZMod 3) :=
  Matrix.toBilin' gramM

theorem formB_apply (x y : Idx → ZMod 3) : formB x y = x ⬝ᵥ (gramM *ᵥ y) := by
  unfold formB
  rw [Matrix.toBilin'_apply']

theorem gramM_mul_self : gramM * gramM = 1 := by decide +kernel

theorem gramM_transpose : gramMᵀ = gramM := by decide +kernel

theorem formB_symm : formB.IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [formB_apply, formB_apply, dotProduct_comm, dot_mulVec_left, gramM_transpose]

theorem formB_nondegenerate : formB.Nondegenerate := by
  have hdet : gramM.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det gramM_mul_self
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  exact (Matrix.nondegenerate_toBilin'_iff.2 (Matrix.nondegenerate_of_det_ne_zero hdet))

theorem formB_eq_polar (x y : Idx → ZMod 3) : formB x y = qf (x + y) - qf x - qf y := by
  rw [formB_apply, qf_eq_gram, qf_eq_gram, qf_eq_gram]
  have hs : y ⬝ᵥ (gramM *ᵥ x) = x ⬝ᵥ (gramM *ᵥ y) := by
    rw [dotProduct_comm, dot_mulVec_left, gramM_transpose]
  rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hs]
  generalize x ⬝ᵥ (gramM *ᵥ y) = a
  generalize x ⬝ᵥ (gramM *ᵥ x) = b
  generalize y ⬝ᵥ (gramM *ᵥ y) = c
  revert a b c
  decide

theorem iso_qf {A : GL Idx (ZMod 3)} (hA : A ∈ Iso) (v : Idx → ZMod 3) :
    qf ((A : Matrix Idx Idx (ZMod 3)) *ᵥ v) = qf v := by
  unfold Iso at hA
  refine Subgroup.closure_induction (p := fun (A : GL Idx (ZMod 3)) _ => ∀ v, qf ((A : Matrix Idx Idx (ZMod 3)) *ᵥ v) = qf v)
    (fun A hA => hA) (fun v => by simp) (fun A B _ _ hA hB v => ?_) (fun A _ hA v => ?_) hA v
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hA, hB]
  · have := hA (((A⁻¹ : GL Idx (ZMod 3)) : Matrix Idx Idx (ZMod 3)) *ᵥ v)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at this
    exact this.symm

@[expose] noncomputable def linHom :
    GL Idx (ZMod 3) ≃* ((Idx → ZMod 3) ≃ₗ[ZMod 3] (Idx → ZMod 3)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) (Idx → ZMod 3))

theorem linHom_apply (A : GL Idx (ZMod 3)) (v : Idx → ZMod 3) :
    linHom A v = (A : Matrix Idx Idx (ZMod 3)) *ᵥ v := rfl

theorem formB_linHom {A : GL Idx (ZMod 3)} (hA : A ∈ Iso) (x y : Idx → ZMod 3) :
    formB (linHom A x) (linHom A y) = formB x y := by
  rw [formB_eq_polar, formB_eq_polar, linHom_apply, linHom_apply, ← Matrix.mulVec_add,
    iso_qf hA, iso_qf hA, iso_qf hA]

theorem card_le_generic (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (ZMod 3))
    (hn : (Matrix.toBilin' M).Nondegenerate) (hs : (Matrix.toBilin' M).IsSymm)
    (hd : Module.finrank (ZMod 3) (ι → ZMod 3) ≤ 7) {G : Type} [Group G] [Finite G]
    (φ : G →* ((ι → ZMod 3) ≃ₗ[ZMod 3] (ι → ZMod 3))) (hφ : Function.Injective φ)
    (hiso : ∀ g x y, Matrix.toBilin' M (φ g x) (φ g y) = Matrix.toBilin' M x y)
    (hp : IsPGroup 3 G) :
    Nat.card G ≤ 3 ^ OrthSyl.bnd (Module.finrank (ZMod 3) (ι → ZMod 3)) :=
  OrthSyl.card_le_of_isPGroup (K := ZMod 3) (V := ι → ZMod 3) (Nat.card_zmod 3) (by decide) hn hs
    hd φ hφ hiso hp

theorem factorization_three_om_le : (Nat.card ↥Om).factorization 3 ≤ 9 := by
  let P : Sylow 3 ↥Om := default
  have hcard := P.card_eq_multiplicity
  let φ : ↥(P : Subgroup ↥Om) →* ((Idx → ZMod 3) ≃ₗ[ZMod 3] (Idx → ZMod 3)) :=
    linHom.toMonoidHom.comp (Om.subtype.comp (P : Subgroup ↥Om).subtype)
  have hφ : Function.Injective φ :=
    linHom.injective.comp (Subgroup.subtype_injective _ |>.comp (Subgroup.subtype_injective _))
  have hiso : ∀ g x y, formB (φ g x) (φ g y) = formB x y := fun g x y =>
    formB_linHom (om_le_iso g.1.2) x y
  have hd : Module.finrank (ZMod 3) (Idx → ZMod 3) ≤ 7 := by
    rw [Module.finrank_fintype_fun_eq_card]; simp [Idx]
  have h := card_le_generic Idx gramM formB_nondegenerate formB_symm hd φ hφ hiso P.isPGroup'
  have h7 : Module.finrank (ZMod 3) (Idx → ZMod 3) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card]; simp [Idx]
  rw [h7, hcard] at h
  have : 3 ^ (Nat.card ↥Om).factorization 3 ≤ 3 ^ OrthSyl.bnd 7 := h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this |>.trans (by decide)

end CFSG.HardMathSupport.Foote.E27
