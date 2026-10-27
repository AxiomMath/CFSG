module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.LocalAnalysis.ComponentClassification.CoprimeAutomorphisms

public section

namespace CFSG

theorem mulAut_eq_one_of_fixes_fittingSubgroup
    (G : Type*) [Group G] [Finite G] (hsolv : Group.IsSolvable G)
    (φ : MulAut G) (m : ℕ) (hpower : φ ^ m = 1)
    (hcoprime : Nat.Coprime m (Nat.card (fittingSubgroup G)))
    (hfixed : ∀ x ∈ fittingSubgroup G, φ x = x) : φ = 1 := by
  apply ComponentClassification.CoprimeAutomorphisms.eq_one_of_fixed_displacement
    (fittingSubgroup G) φ m hpower hcoprime hfixed
  intro x
  apply centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
  apply Subgroup.mem_centralizer_iff.mpr
  intro f hf
  have hconj : x * f * x⁻¹ ∈ fittingSubgroup G :=
    (inferInstance : (fittingSubgroup G).Normal).conj_mem f hf x
  have heq := hfixed (x * f * x⁻¹) hconj
  rw [map_mul, map_mul, map_inv, hfixed f hf] at heq
  have hcomm := congrArg (fun y : G => x⁻¹ * y * φ x) heq
  calc
    f * (x⁻¹ * φ x) = x⁻¹ * (x * f * x⁻¹) * φ x := by group
    _ = x⁻¹ * (φ x * f * (φ x)⁻¹) * φ x := hcomm.symm
    _ = (x⁻¹ * φ x) * f := by group

end CFSG
