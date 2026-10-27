module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryBar
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Linear

variable {n : ℕ} {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem conjAut_mem_inner_of_det_eq_units_pow (hn : 1 ≤ n) {A : GL (Fin n) F} {u : Fˣ}
    (hu : Matrix.GeneralLinearGroup.det A = u ^ n) : conjAut n F A ∈ inner (projectiveSL n F) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hdet : (((GeneralLinearGroup.scalar (Fin n) u⁻¹ * A : GL (Fin n) F)) :
      Matrix (Fin n) (Fin n) F).det = 1 := by
    have h1 := congrArg (fun v : Fˣ => (v : F)) hu
    simp only [Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply] at h1
    rw [Units.val_mul, det_mul, GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, h1, Units.val_inv_eq_inv_val,
      inv_pow, inv_mul_cancel₀ (pow_ne_zero _ u.ne_zero)]
  obtain ⟨g, hg⟩ : ∃ g : SpecialLinearGroup (Fin n) F,
      SpecialLinearGroup.toGL g = GeneralLinearGroup.scalar (Fin n) u⁻¹ * A :=
    ⟨⟨_, hdet⟩, Units.ext rfl⟩
  have hA : A = GeneralLinearGroup.scalar (Fin n) u * SpecialLinearGroup.toGL g := by
    rw [hg, map_inv, mul_inv_cancel_left]
  rw [hA, map_mul, conjAut_scalar, one_mul, conjAut_toGL]
  exact ⟨_, rfl⟩

end Linear

theorem exists_conj_eq_of_fieldBar_conj_mem_coset {f : ℕ} {K' : Type} [Field K']
    (h : UnitaryFieldData 2 f K') {m : ℕ} (C : GL (Fin m) K') (hC : IsPrimeFormGram C)
    (hm : 3 ≤ m) {φ : K' ≃+* K'} (hφ : ∀ x, φ x = h.bar x)
    {d : MulAut (primeFormP h (C : Matrix (Fin m) (Fin m) K'))}
    (hd : d ∈ primeFormD h (C : Matrix (Fin m) (Fin m) K'))
    (hcoset : d * primeFormFieldHom h hC φ * d⁻¹ * (primeFormFieldHom h hC φ)⁻¹ ∈
      inner (primeFormP h (C : Matrix (Fin m) (Fin m) K'))) :
    ∃ y : primeFormP h (C : Matrix (Fin m) (Fin m) K'),
      d * primeFormFieldHom h hC φ * d⁻¹ =
        MulAut.conj y * primeFormFieldHom h hC φ * (MulAut.conj y)⁻¹ := by
  obtain ⟨y, hy⟩ := primeFormBarInvertsInput_holds f K' h m C hC hm φ hφ d hd hcoset
  exact ⟨y, by rw [hy]⟩

end CFSG.SeitzReduction.SymplecticPilot
