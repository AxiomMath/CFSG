module

public import CFSG.FeitThompson.Representations.IrreducibleCharactersOrthonormalBasis
import CFSG.FeitThompson.Representations.InducedIrreducibleNormOrbitFormula
import CFSG.FeitThompson.Representations.CoprimePrimeAutFixedConjugacyClasses
import Mathlib.LinearAlgebra.Matrix.Permutation

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module

noncomputable section

variable {H : Type*} [Group H]

theorem trace_eq_natCard_fixed_of_basis_perm {R M ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Finite ι] (b : Module.Basis ι R M) (σ : Equiv.Perm ι)
    (T : M →ₗ[R] M) (hT : ∀ i, T (b i) = b (σ i)) :
    LinearMap.trace R M T = (Nat.card {i // σ i = i} : R) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  rw [LinearMap.trace_eq_matrix_trace R b T]
  have hmat : LinearMap.toMatrix b b T = (σ⁻¹).permMatrix R := by
    ext i j
    rw [LinearMap.toMatrix_apply, hT, b.repr_self]
    simp [Equiv.Perm.permMatrix, Equiv.Perm.inv_def, Equiv.eq_symm_apply,
      Finsupp.single_apply, eq_comm]
  rw [hmat, Matrix.trace_permutation]
  congr 1
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.subtypeEquivRight (by simp [Function.IsFixedPt, eq_comm]))

def classFun.compAut (α : MulAut H) : classFun H →ₗ[ℂ] classFun H where
  toFun f := ⟨(f : H → ℂ) ∘ α, mem_classFun.2 fun _ _ h =>
    mem_classFun.1 f.2 _ _ (MonoidHom.map_isConj (α : H →* H) h)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem classFun.coe_compAut_apply (α : MulAut H) (f : classFun H) :
    ((classFun.compAut α f : classFun H) : H → ℂ) = (f : H → ℂ) ∘ α := (rfl)

@[simp] theorem classFun.compAut_one : classFun.compAut (1 : MulAut H) = LinearMap.id := by
  ext f h
  simp

theorem classFun.compAut_mul (α β : MulAut H) :
    classFun.compAut (α * β) = classFun.compAut β ∘ₗ classFun.compAut α := by
  ext f h
  simp

def classFun.basisConjClasses (H : Type*) [Group H] [Finite H] :
    Module.Basis (ConjClasses H) ℂ (classFun H) :=
  (Pi.basisFun ℂ (ConjClasses H)).map (classFun.equivConjClasses H).symm

open scoped Classical in
theorem classFun.coe_basisConjClasses_apply [Finite H] (K : ConjClasses H) :
    ((classFun.basisConjClasses H K : classFun H) : H → ℂ) =
      fun g => if ConjClasses.mk g = K then 1 else 0 := by
  classical
  ext g
  rw [classFun.basisConjClasses]
  simp [Pi.single_apply]

def conjClassesAut (α : MulAut H) : Equiv.Perm (ConjClasses H) where
  toFun := ConjClasses.map (α : H →* H)
  invFun := ConjClasses.map (α.symm : H →* H)
  left_inv K := by
    obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective K
    change ConjClasses.mk _ = _
    simp
  right_inv K := by
    obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective K
    change ConjClasses.mk _ = _
    simp

@[simp] theorem conjClassesAut_mk (α : MulAut H) (a : H) :
    conjClassesAut α (ConjClasses.mk a) = ConjClasses.mk (α a) := (rfl)

@[simp] theorem conjClassesAut_one : conjClassesAut (1 : MulAut H) = 1 := by
  ext K
  obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective K
  simp

theorem mk_eq_conjClassesAut_iff (α : MulAut H) (K : ConjClasses H) (y : H) :
    ConjClasses.mk y = conjClassesAut α K ↔ ConjClasses.mk (α.symm y) = K := by
  rw [← (conjClassesAut α).injective.eq_iff (a := ConjClasses.mk (α.symm y)) (b := K),
    conjClassesAut_mk, MulEquiv.apply_symm_apply]

theorem carrier_conjClassesAut (α : MulAut H) (K : ConjClasses H) :
    (conjClassesAut α K).carrier = (α : H → H) '' K.carrier := by
  ext y
  simp only [ConjClasses.mem_carrier_iff_mk_eq, Set.mem_image, mk_eq_conjClassesAut_iff]
  refine ⟨fun h => ⟨α.symm y, h, by simp⟩, ?_⟩
  rintro ⟨x, hx, rfl⟩
  simpa using hx

theorem conjClassesAut_eq_self_iff (α : MulAut H) (K : ConjClasses H) :
    conjClassesAut α K = K ↔ (α : H → H) '' K.carrier = K.carrier := by
  rw [← carrier_conjClassesAut]
  exact ⟨fun h => by rw [h], fun h => conjClasses_carrier_injective h⟩

theorem mem_Irr_comp_mulAut {χ : H → ℂ} (hχ : χ ∈ Irr H) (α : MulAut H) :
    χ ∘ α ∈ Irr H := by
  rw [← normalInduction_irrChars_eq_Irr] at hχ ⊢
  exact NormalInduction.mem_irrChars_comp_mulEquiv hχ α

def irrAut (α : MulAut H) : Equiv.Perm (Irr H) where
  toFun χ := ⟨(χ : H → ℂ) ∘ α, mem_Irr_comp_mulAut χ.2 α⟩
  invFun χ := ⟨(χ : H → ℂ) ∘ α.symm, mem_Irr_comp_mulAut χ.2 α.symm⟩
  left_inv χ := Subtype.ext (by ext h; simp)
  right_inv χ := Subtype.ext (by ext h; simp)

@[simp] theorem coe_irrAut_apply (α : MulAut H) (χ : Irr H) :
    ((irrAut α χ : Irr H) : H → ℂ) = (χ : H → ℂ) ∘ α := (rfl)

@[simp] theorem irrAut_one : irrAut (1 : MulAut H) = 1 := by
  ext χ h
  simp

theorem irrAut_eq_self_iff (α : MulAut H) (χ : Irr H) :
    irrAut α χ = χ ↔ ∀ h : H, (χ : H → ℂ) (α h) = (χ : H → ℂ) h := by
  rw [Subtype.ext_iff, coe_irrAut_apply, funext_iff]
  rfl

theorem compAut_basisIrr [Finite H] (α : MulAut H) (χ : Irr H) :
    classFun.compAut α (classFun.basisIrr H χ) = classFun.basisIrr H (irrAut α χ) := by
  apply Subtype.ext
  rw [classFun.coe_compAut_apply, classFun.basisIrr_apply, classFun.basisIrr_apply,
    Irr.coe_toClassFun, Irr.coe_toClassFun, coe_irrAut_apply]

theorem compAut_basisConjClasses [Finite H] (α : MulAut H) (K : ConjClasses H) :
    classFun.compAut α (classFun.basisConjClasses H K) =
      classFun.basisConjClasses H ((conjClassesAut α)⁻¹ K) := by
  classical
  apply Subtype.ext
  rw [classFun.coe_compAut_apply, classFun.coe_basisConjClasses_apply,
    classFun.coe_basisConjClasses_apply]
  ext g
  simp only [Function.comp_apply]
  congr 1
  rw [eq_comm, Equiv.Perm.inv_def, Equiv.eq_symm_apply, eq_comm, conjClassesAut_mk]

theorem trace_compAut_eq_card_fixed_Irr [Finite H] (α : MulAut H) :
    LinearMap.trace ℂ (classFun H) (classFun.compAut α)
      = (Nat.card {χ : Irr H // irrAut α χ = χ} : ℂ) :=
  trace_eq_natCard_fixed_of_basis_perm (classFun.basisIrr H) (irrAut α) _ (compAut_basisIrr α)

theorem trace_compAut_eq_card_fixed_conjClasses [Finite H] (α : MulAut H) :
    LinearMap.trace ℂ (classFun H) (classFun.compAut α)
      = (Nat.card {K : ConjClasses H // (conjClassesAut α)⁻¹ K = K} : ℂ) :=
  trace_eq_natCard_fixed_of_basis_perm (classFun.basisConjClasses H) ((conjClassesAut α)⁻¹) _
    (compAut_basisConjClasses α)

theorem card_fixed_irrAut_eq_card_fixed_conjClassesAut [Finite H] (α : MulAut H) :
    Nat.card {χ : Irr H // irrAut α χ = χ}
      = Nat.card {K : ConjClasses H // conjClassesAut α K = K} := by
  have h : ((Nat.card {χ : Irr H // irrAut α χ = χ} : ℂ))
      = (Nat.card {K : ConjClasses H // (conjClassesAut α)⁻¹ K = K} : ℂ) := by
    rw [← trace_compAut_eq_card_fixed_Irr α, trace_compAut_eq_card_fixed_conjClasses α]
  have h2 : Nat.card {χ : Irr H // irrAut α χ = χ}
      = Nat.card {K : ConjClasses H // (conjClassesAut α)⁻¹ K = K} := by
    exact_mod_cast h
  refine h2.trans (Nat.card_congr (Equiv.subtypeEquivRight fun K => ?_))
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, eq_comm]

theorem card_fixed_Irr_eq_card_fixed_conjClasses [Finite H] (α : MulAut H) :
    Nat.card {χ : Irr H // ∀ h : H, (χ : H → ℂ) (α h) = (χ : H → ℂ) h}
      = Nat.card {K : ConjClasses H // (α : H → H) '' K.carrier = K.carrier} := by
  rw [← Nat.card_congr (Equiv.subtypeEquivRight (irrAut_eq_self_iff α)),
    ← Nat.card_congr (Equiv.subtypeEquivRight (conjClassesAut_eq_self_iff α))]
  exact card_fixed_irrAut_eq_card_fixed_conjClassesAut α

end

end CFSG.FeitThompson
