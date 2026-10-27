module

public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.FieldTheory.Separable
public import CFSG.FeitThompson.Representations.QuadraticSplittingExtensionDegreeTwo

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Polynomial Matrix Module MatrixGroups

variable {E : Type*} [Field E]

theorem squarefree_minpoly_of_pow_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n E} {r : ℕ} (hr : (r : E) ≠ 0) (hA : A ^ r = 1) :
    Squarefree (minpoly E A) := by
  have hdvd : minpoly E A ∣ X ^ r - C 1 := by
    apply minpoly.dvd; simp [hA]
  exact Squarefree.squarefree_of_dvd hdvd
    ((Polynomial.separable_X_pow_sub_C (1 : E) hr one_ne_zero).squarefree)

theorem eq_smul_one_of_charpoly_eq_sq {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n E} {a : E} {r : ℕ} (hr : (r : E) ≠ 0) (hA : A ^ r = 1)
    (hcp : A.charpoly = (X - C a) ^ 2) : A = a • (1 : Matrix n n E) := by
  have hsq := squarefree_minpoly_of_pow_eq_one hr hA
  have h1 : minpoly E A ∣ (X - C a) := by
    rw [← hsq.dvd_pow_iff_dvd two_ne_zero, ← hcp]
    exact Matrix.minpoly_dvd_charpoly A
  obtain ⟨q, hq⟩ := h1
  have h2 : (aeval A) (X - C a) = 0 := by rw [hq, map_mul, minpoly.aeval, zero_mul]
  simpa only [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, sub_eq_zero] using h2

theorem ne_of_charpoly_eq_mul_linear {A : Matrix (Fin 2) (Fin 2) E} {a b : E} {r : ℕ}
    (hrE : (r : E) ≠ 0) (hodd : Odd r) (hA : A ^ r = 1) (hA1 : A ≠ 1) (hdet : A.det = 1)
    (hcp : A.charpoly = (X - C a) * (X - C b)) : a ≠ b := by
  rintro rfl
  have hsq : A.charpoly = (X - C a) ^ 2 := by rw [hcp]; ring
  have hAs : A = a • (1 : Matrix (Fin 2) (Fin 2) E) := eq_smul_one_of_charpoly_eq_sq hrE hA hsq
  have ha2 : a ^ 2 = 1 := by rw [hAs, Matrix.det_smul] at hdet; simpa using hdet
  have har : a ^ r = 1 := by
    rw [hAs, _root_.smul_pow, one_pow] at hA
    simpa using congrFun (congrFun hA 0) 0
  obtain ⟨m, hm⟩ := hodd
  have ha : a = 1 := by rwa [hm, pow_add, pow_mul, ha2, one_pow, one_mul, pow_one] at har
  exact hA1 (by rw [hAs, ha, one_smul])

theorem mul_eq_one_of_charpoly_eq_mul_linear {A : Matrix (Fin 2) (Fin 2) E} {a b : E}
    (hdet : A.det = 1) (hcp : A.charpoly = (X - C a) * (X - C b)) : a * b = 1 := by
  have h2 := Matrix.det_eq_sign_charpoly_coeff A
  rw [hcp, hdet] at h2
  simp only [Fintype.card_fin, mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero,
    zero_sub] at h2
  simpa using h2.symm

theorem mulVec_mem_eigenspace_mulVecLin {A : Matrix (Fin 2) (Fin 2) E} {a : E}
    {v : Fin 2 → E} (hv : v ∈ Module.End.eigenspace (A.mulVecLin : Module.End E (Fin 2 → E)) a) :
    A *ᵥ v ∈ Module.End.eigenspace (A.mulVecLin : Module.End E (Fin 2 → E)) a :=
  (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mp
    (Module.End.eigenspace_mem_invtSubmodule _ a) v hv

theorem finrank_eigenspace_mulVecLin_eq_one {A : Matrix (Fin 2) (Fin 2) E} {a b : E} (hab : a ≠ b)
    (hcp : A.charpoly = (X - C a) * (X - C b)) :
    finrank E (Module.End.eigenspace (A.mulVecLin : Module.End E (Fin 2 → E)) a) = 1 := by
  set f : Module.End E (Fin 2 → E) := A.mulVecLin with hf
  have hfc : LinearMap.charpoly f = A.charpoly := by rw [hf]; exact Matrix.charpoly_mulVecLin A
  have h1 : f.HasEigenvalue a := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hfc, hcp]; simp [IsRoot]
  have h2 : f.HasEigenvalue b := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hfc, hcp]; simp [IsRoot]
  have ha1 : 1 ≤ finrank E (f.eigenspace a) :=
    Submodule.one_le_finrank_iff.mpr (Module.End.hasEigenvalue_iff.mp h1)
  have hb1 : 1 ≤ finrank E (f.eigenspace b) :=
    Submodule.one_le_finrank_iff.mpr (Module.End.hasEigenvalue_iff.mp h2)
  have hd : Disjoint (f.eigenspace a) (f.eigenspace b) :=
    Module.End.disjoint_genEigenspace f hab 1 1
  have := Submodule.finrank_add_finrank_le_of_disjoint hd
  rw [Module.finrank_fin_fun] at this
  omega

theorem isCompl_eigenspace_mulVecLin {A : Matrix (Fin 2) (Fin 2) E} {a b : E} (hab : a ≠ b)
    (hcp : A.charpoly = (X - C a) * (X - C b)) :
    IsCompl (Module.End.eigenspace (A.mulVecLin : Module.End E (Fin 2 → E)) a)
      (Module.End.eigenspace (A.mulVecLin : Module.End E (Fin 2 → E)) b) := by
  refine (Submodule.isCompl_iff_disjoint _ _ ?_).mpr
    (Module.End.disjoint_genEigenspace _ hab 1 1)
  rw [Module.finrank_fin_fun, finrank_eigenspace_mulVecLin_eq_one hab hcp,
    finrank_eigenspace_mulVecLin_eq_one hab.symm (by rw [hcp]; ring)]

theorem eigenspace_mulVecLin_ne {A : Matrix (Fin 2) (Fin 2) E} {a b : E} (hab : a ≠ b)
    (hcp : A.charpoly = (X - C a) * (X - C b)) :
    Module.End.eigenspace (A.mulVecLin : Module.End E (Fin 2 → E)) a ≠
      Module.End.eigenspace (A.mulVecLin : Module.End E (Fin 2 → E)) b := by
  intro h
  have hd : Disjoint (Module.End.eigenspace (A.mulVecLin : Module.End E (Fin 2 → E)) a)
      (Module.End.eigenspace (A.mulVecLin : Module.End E (Fin 2 → E)) b) :=
    Module.End.disjoint_genEigenspace _ hab 1 1
  rw [h, disjoint_self] at hd
  have h1 := finrank_eigenspace_mulVecLin_eq_one hab.symm (A := A) (by rw [hcp]; ring)
  rw [hd] at h1
  simp at h1

theorem eq_eigenspace_mulVecLin_of_invariant {A : Matrix (Fin 2) (Fin 2) E} {a b : E} (hab : a ≠ b)
    (hcp : A.charpoly = (X - C a) * (X - C b)) {W : Submodule E (Fin 2 → E)}
    (hW1 : finrank E W = 1) (hWi : ∀ v ∈ W, A *ᵥ v ∈ W) :
    W = Module.End.eigenspace (A.mulVecLin : Module.End E (Fin 2 → E)) a ∨
      W = Module.End.eigenspace (A.mulVecLin : Module.End E (Fin 2 → E)) b := by
  set f : Module.End E (Fin 2 → E) := A.mulVecLin with hf
  have hfc : LinearMap.charpoly f = A.charpoly := by rw [hf]; exact Matrix.charpoly_mulVecLin A
  obtain ⟨v, hv, hv0⟩ : ∃ v ∈ W, v ≠ 0 := by
    refine (Submodule.ne_bot_iff W).mp ?_
    intro h; rw [h] at hW1; simp at hW1
  have hWs : W = E ∙ v := eq_span_singleton_of_mem_of_finrank_eq_one hW1 hv hv0
  have hfv : f v ∈ W := hWi v hv
  rw [hWs, Submodule.mem_span_singleton] at hfv
  obtain ⟨c, hc⟩ := hfv
  have hce : f.HasEigenvalue c := Module.End.hasEigenvalue_of_hasEigenvector
    (x := v) ⟨Module.End.mem_eigenspace_iff.mpr hc.symm, hv0⟩
  have hroot : (LinearMap.charpoly f).IsRoot c :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly f c).mp hce
  rw [hfc, hcp] at hroot
  simp only [IsRoot, eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero] at hroot
  rcases hroot with h | h
  · exact Or.inl (Submodule.eq_of_le_of_finrank_eq
      (by rw [hWs, Submodule.span_singleton_le_iff_mem]
          exact Module.End.mem_eigenspace_iff.mpr (by rw [← hc, ← h]))
      (by rw [hW1, finrank_eigenspace_mulVecLin_eq_one hab hcp]))
  · exact Or.inr (Submodule.eq_of_le_of_finrank_eq
      (by rw [hWs, Submodule.span_singleton_le_iff_mem]
          exact Module.End.mem_eigenspace_iff.mpr (by rw [← hc, ← h]))
      (by rw [hW1, finrank_eigenspace_mulVecLin_eq_one hab.symm (by rw [hcp]; ring)]))

theorem exists_finiteField_natCard_eq_or_and_two_invariant_lines (k : Type u) [Field k] [Finite k]
    {p r : ℕ} [CharP k p] (hr : r.Prime) (hodd : Odd r) (hrp : r ≠ p) (x : SL(2, k))
    (hx : orderOf x = r) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : Finite E),
      Function.Injective (algebraMap k E) ∧
      (Nat.card E = Nat.card k ∨ Nat.card E = Nat.card k ^ 2) ∧
      ∃ a b : E, a ≠ b ∧ a * b = 1 ∧
        ∃ W₁ W₂ : Submodule E (Fin 2 → E),
          W₁ ≠ W₂ ∧ finrank E W₁ = 1 ∧ finrank E W₂ = 1 ∧ IsCompl W₁ W₂ ∧
          (∀ v ∈ W₁, (x : Matrix (Fin 2) (Fin 2) k).map (algebraMap k E) *ᵥ v = a • v) ∧
          (∀ v ∈ W₂, (x : Matrix (Fin 2) (Fin 2) k).map (algebraMap k E) *ᵥ v = b • v) ∧
          ∀ W : Submodule E (Fin 2 → E), finrank E W = 1 →
            (∀ v ∈ W, (x : Matrix (Fin 2) (Fin 2) k).map (algebraMap k E) *ᵥ v ∈ W) →
              W = W₁ ∨ W = W₂ := by
  classical
  set A : Matrix (Fin 2) (Fin 2) k := (x : Matrix (Fin 2) (Fin 2) k) with hA
  have hp : p.Prime := CharP.char_is_prime k p
  have hmon : A.charpoly.Monic := Matrix.charpoly_monic A
  have hdeg : A.charpoly.natDegree = 2 := by
    rw [Matrix.charpoly_natDegree_eq_dim]; simp
  obtain ⟨a, b, hab⟩ := exists_eq_mul_linear_splittingField hmon hdeg
  refine ⟨A.charpoly.SplittingField, inferInstance, inferInstance, inferInstance,
    FaithfulSMul.algebraMap_injective _ _, natCard_splittingField_eq_or hmon hdeg, a, b, ?_⟩
  have hchar : CharP A.charpoly.SplittingField p :=
    charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective k _) p
  have hrE : (r : A.charpoly.SplittingField) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff _ p]
    intro hdvd
    exact hrp ((Nat.prime_dvd_prime_iff_eq hp hr).mp hdvd).symm
  set A' : Matrix (Fin 2) (Fin 2) A.charpoly.SplittingField :=
    A.map (algebraMap k A.charpoly.SplittingField) with hA'
  have hcp : A'.charpoly = (X - C a) * (X - C b) := by rw [hA', Matrix.charpoly_map]; exact hab
  have hdet' : A'.det = 1 := by
    rw [hA', ← RingHom.mapMatrix_apply, ← RingHom.map_det, hA,
      Matrix.SpecialLinearGroup.det_coe, map_one]
  have hAr : A ^ r = 1 := by
    rw [hA, ← Matrix.SpecialLinearGroup.coe_pow, ← hx, pow_orderOf_eq_one,
      Matrix.SpecialLinearGroup.coe_one]
  have hpow : A' ^ r = 1 := by
    rw [hA', ← RingHom.mapMatrix_apply, ← map_pow, hAr, map_one]
  have hA1 : A ≠ 1 := by
    intro h
    have hx1 : x = 1 := by
      ext i j; rw [Matrix.SpecialLinearGroup.coe_one, ← hA, h]
    rw [hx1, orderOf_one] at hx
    exact hr.one_lt.ne hx
  have hne1 : A' ≠ 1 := by
    intro h
    refine hA1 ?_
    have hmap : A.map (algebraMap k A.charpoly.SplittingField) =
        (1 : Matrix (Fin 2) (Fin 2) k).map (algebraMap k A.charpoly.SplittingField) := by
      rw [Matrix.map_one _ (map_zero _) (map_one _), ← hA', h]
    exact Matrix.map_injective (FaithfulSMul.algebraMap_injective k _) hmap
  have hne : a ≠ b := ne_of_charpoly_eq_mul_linear hrE hodd hpow hne1 hdet' hcp
  refine ⟨hne, mul_eq_one_of_charpoly_eq_mul_linear hdet' hcp,
    Module.End.eigenspace (A'.mulVecLin : Module.End A.charpoly.SplittingField _) a,
    Module.End.eigenspace (A'.mulVecLin : Module.End A.charpoly.SplittingField _) b,
    eigenspace_mulVecLin_ne hne hcp,
    finrank_eigenspace_mulVecLin_eq_one hne hcp,
    finrank_eigenspace_mulVecLin_eq_one hne.symm (by rw [hcp]; ring),
    isCompl_eigenspace_mulVecLin hne hcp, ?_, ?_, ?_⟩
  · intro v hv
    simpa [hA'] using Module.End.mem_eigenspace_iff.mp hv
  · intro v hv
    simpa [hA'] using Module.End.mem_eigenspace_iff.mp hv
  · intro W hW1 hWi
    exact eq_eigenspace_mulVecLin_of_invariant hne hcp hW1 hWi

end CFSG.FeitThompson
