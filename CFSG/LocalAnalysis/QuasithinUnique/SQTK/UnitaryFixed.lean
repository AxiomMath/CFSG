module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryMatrix
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.GraphAutomorphism

public section

namespace CFSG.QuasithinUnique.SQTK

open Matrix TauCeti

noncomputable section

section Steinberg

variable (r p k : ℕ) (A : Type) [Field A] [ExpChar A p]

@[expose] def unitarySteinberg :
    SpecialLinearGroup (Fin (r + 1)) A →* SpecialLinearGroup (Fin (r + 1)) A :=
  (SpecialLinearGroup.typeAGraphAutomorphism r A).toMonoidHom.comp
    (SpecialLinearGroup.map (iterateFrobenius A p k))

variable {r p k A}

theorem toGL_map_iterateFrobenius (g : SpecialLinearGroup (Fin (r + 1)) A) :
    SpecialLinearGroup.toGL (SpecialLinearGroup.map (iterateFrobenius A p k) g) =
      GeneralLinearGroup.map (iterateFrobenius A p k) (SpecialLinearGroup.toGL g) := by
  ext i j
  rfl

theorem mem_fixedSubgroup_unitarySteinberg_iff_GL (g : SpecialLinearGroup (Fin (r + 1)) A) :
    g ∈ fixedSubgroup (unitarySteinberg r p k A) ↔
      typeAGraphAutomorphism r A
          (GeneralLinearGroup.map (iterateFrobenius A p k) (SpecialLinearGroup.toGL g)) =
        SpecialLinearGroup.toGL g := by
  rw [mem_fixedSubgroup, ← SpecialLinearGroup.toGL_injective.eq_iff, unitarySteinberg,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    SpecialLinearGroup.toGL_typeAGraphAutomorphism, toGL_map_iterateFrobenius]

theorem mem_fixedSubgroup_unitarySteinberg_iff (g : SpecialLinearGroup (Fin (r + 1)) A) :
    g ∈ fixedSubgroup (unitarySteinberg r p k A) ↔
      ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) A).map (· ^ p ^ k))ᵀ *
          (typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A) *
            (g : Matrix (Fin (r + 1)) (Fin (r + 1)) A) =
        (typeAGraphConjugator r A : Matrix (Fin (r + 1)) (Fin (r + 1)) A) := by
  rw [mem_fixedSubgroup_unitarySteinberg_iff_GL,
    typeAGraphAutomorphism_eq_iff_transpose_mul_conjugator_mul_eq]
  rfl

theorem entry_pow_eq_self {g : SpecialLinearGroup (Fin (r + 1)) A}
    (hg : g ∈ fixedSubgroup (unitarySteinberg r p k A)) (i j : Fin (r + 1)) :
    (g : Matrix (Fin (r + 1)) (Fin (r + 1)) A) i j ^ p ^ (2 * k) =
      (g : Matrix (Fin (r + 1)) (Fin (r + 1)) A) i j := by
  set G := SpecialLinearGroup.toGL g
  have hG : typeAGraphAutomorphism r A (GeneralLinearGroup.map (iterateFrobenius A p k) G) = G :=
    (mem_fixedSubgroup_unitarySteinberg_iff_GL g).mp hg
  have h1 : GeneralLinearGroup.map (iterateFrobenius A p k) G =
      typeAGraphAutomorphism r A (GeneralLinearGroup.map (iterateFrobenius A p k)
        (GeneralLinearGroup.map (iterateFrobenius A p k) G)) := by
    conv_lhs => rw [← hG]
    exact map_typeAGraphAutomorphism (iterateFrobenius A p k) r _
  have h2 : G = GeneralLinearGroup.map (iterateFrobenius A p k)
      (GeneralLinearGroup.map (iterateFrobenius A p k) G) :=
    hG.symm.trans ((congrArg _ h1).trans (typeAGraphAutomorphism_typeAGraphAutomorphism r _))
  have h3 := congrArg
    (fun M : GL (Fin (r + 1)) A => (M : Matrix (Fin (r + 1)) (Fin (r + 1)) A) i j) h2
  simp only [GeneralLinearGroup.map_apply, iterateFrobenius_def] at h3
  have h4 : (g : Matrix (Fin (r + 1)) (Fin (r + 1)) A) i j =
      ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) A) i j ^ p ^ k) ^ p ^ k := h3
  rw [two_mul, pow_add, pow_mul]
  exact h4.symm

end Steinberg

end

end CFSG.QuasithinUnique.SQTK
