module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXClassicalTorus

public noncomputable section

namespace CFSG.LocalAnalysis.GorensteinLyons

namespace SparePermutationLift

open Subgroup Equiv

section Torus

variable {M : Type*} [CommGroup M] {n : ℕ}

theorem torusVec_comp_perm (ζ : M) (i d : Fin n) (σ : Perm (Fin n)) :
    torusVec ζ i d ∘ σ = torusVec ζ (σ⁻¹ i) (σ⁻¹ d) := by
  funext j
  simp only [Function.comp_apply, torusVec_apply, Perm.eq_inv_iff_eq]

theorem torusVec_mul_inv (ζ : M) (a b d : Fin n) :
    torusVec ζ a d * (torusVec ζ b d)⁻¹ = torusVec ζ a b := by
  simp only [torusVec, Pi.mulSingle_inv]
  group

theorem torusVec_inv (ζ : M) (b d : Fin n) : (torusVec ζ b d)⁻¹ = torusVec ζ d b := by
  simp only [torusVec, Pi.mulSingle_inv]
  group

variable {S : Type*} [Group S]

end Torus

end SparePermutationLift

universe u v

end CFSG.LocalAnalysis.GorensteinLyons
