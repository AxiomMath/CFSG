module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.Chevalley

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

theorem centralQuot_equiv_of_surjective {A B : Type} [Group A] [Group B] (hA : IsQuasisimple A)
    (hB : IsQuasisimple B) (f : A →* B) (hf : Function.Surjective f) (hker : f.ker ≤ center A) :
    Nonempty (A ⧸ center A ≃* B ⧸ center B) := by
  have hc : center A = ((QuotientGroup.mk' (center B)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact (CFSG.LocalCores.comap_center_eq_of_perfect hA.1 f hf hker).symm
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hf))⟩

end CFSG.OddStandard.SmallF3.HypA2
