module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrComp
public import CFSG.Assembly.ComponentTypeDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec4FD_exists_component_lift {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (ρ : A →* B) (hρ : OddCentralCover ρ) {K : Subgroup B} (hK : IsComponentIn K ⊤)
    (hoc : oddCore ↥K = ⊥) :
    ∃ K' : Subgroup A, IsComponentIn K' ⊤ ∧ Nonempty (↥K' ⧸ oddCore ↥K' ≃* ↥K) := by
  have hXq : CFSG.IsQuasisimple ↥K := hK.isQuasisimple
  have htopB : centralizer ({(1 : B)} : Set B) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Subgroup.one_mem _
  have hKc : IsComponentIn K (centralizer ({(ρ (1 : A))} : Set B)) := by
    rw [map_one, htopB]
    exact hK
  have hKcomp : IsComponentIn (coverDerived ρ K) (centralizer ({(1 : A)} : Set A)) :=
    hρ.isComponentIn_coverDerived (w := (1 : A)) (one_mul 1) hKc
  have htopA : centralizer ({(1 : A)} : Set A) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Subgroup.one_mem _
  refine ⟨coverDerived ρ K, ?_, ?_⟩
  · rw [← htopA]
    exact hKcomp
  · have hcov := hρ.oddCentralCover_coverDerivedHom hXq
    have hker : oddCore ↥(coverDerived ρ K) = (coverDerivedHom ρ K).ker :=
      hcov.oddCore_eq_ker hoc
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hcov.surjective)⟩

end CFSG.OddStandard.SmallF3.Omega
