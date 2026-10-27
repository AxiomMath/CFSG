module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ISetup
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IPocket
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2PocketLift
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34b

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] {L : Subgroup G}

theorem sec4I_isI4PlusIn_iff [Finite G] (hL : IsOmega7Group L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) {w : G} :
    IsI4PlusIn L w ↔ ∃ hw : w ∈ L, orderOf w = 2 ∧
      HasType ((e (QuotientGroup.mk (⟨w, hw⟩ : ↥L)) : Sec4IOmega) : ProjOrth Sec4IQ) 4 1 := by
  have hcen := sec4I_center_eq_oddCore hL
  let E : ↥L ⧸ oddCore ↥L ≃* Sec4IOmega :=
    (QuotientGroup.quotientMulEquivOfEq hcen.symm).trans e
  constructor
  · intro hI
    obtain ⟨hw, f, hf, hfw⟩ := exists_quaternion_quotient_of_le (le_refl L) hI
    have h1 := hasType_of_quaternion_seven sec4IQ_nondegenerate sec4IQ_finrank
      (f := E.toMonoidHom.comp f) (E.injective.comp hf)
    refine ⟨hw, hI.1, ?_⟩
    have h2 : (E.toMonoidHom.comp f) (QuaternionGroup.a 2) = e (QuotientGroup.mk ⟨w, hw⟩) := by
      change E (f (QuaternionGroup.a 2)) = _
      rw [hfw]
      rfl
    rwa [h2] at h1
  · rintro ⟨hw, hord, hty⟩
    have h1 := isI4PlusIn_top_of_hasType_seven sec4IQ_nondegenerate sec4IQ_finrank hty
    have h2 := isI4PlusIn_top_map_mulEquiv E.symm h1
    have h3 : E.symm (e (QuotientGroup.mk (⟨w, hw⟩ : ↥L))) =
        QuotientGroup.mk (⟨w, hw⟩ : ↥L) := by
      apply E.injective
      rw [E.apply_symm_apply]
      rfl
    rw [h3] at h2
    exact isI4PlusIn_of_quotient hw hord h2

end CFSG.OddStandard.SmallF3.Omega
