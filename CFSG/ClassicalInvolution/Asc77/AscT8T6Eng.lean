module

public import CFSG.ClassicalInvolution.Asc77.AscT7AFrame
public import CFSG.ClassicalInvolution.Asc77.AscT8Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8T

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem sigmaNorm_le_normalizer_alphaE (hcl : ConjInvariant Ω) {K J : Subgroup G} {z t : G}
    (hK : K ∈ Ω) (hJ : J ∈ omegaNbr Ω K) (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t)
    (hdc : ∀ {L : Subgroup G}, L ∈ dComp Ω K → L ∈ Ω ∧ ∀ L' ∈ omegaNbr Ω L, ∀ y y' : G,
      IsUniqueInvolution L y → IsUniqueInvolution L' y' →
        alphaOf (Subgroup.closure ({y', y} : Set G)) =
          alphaOf (Subgroup.closure ({t, z} : Set G))) :
    sigmaNorm Ω K ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
  intro n hn
  have hKn : conjSub n K ∈ dComp Ω K := (T8.mem_sigmaNorm_iff hcl hK).1 hn
  obtain ⟨-, hP⟩ := hdc hKn
  have h := hP (conjSub n J) (omegaNbr_conj hcl hJ n) (n * z * n⁻¹)
    (n * t * n⁻¹) (hz.conj n) (ht.conj n)
  rw [← conjSub_closure_pair, alphaOf_conjSub] at h
  exact mem_normalizer_iff_conjSub_eq.mpr h

end T8T

end CFSG.ClassicalInvolution.Asc77
