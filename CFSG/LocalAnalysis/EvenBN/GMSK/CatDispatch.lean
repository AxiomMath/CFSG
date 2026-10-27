module

public import CFSG.LocalAnalysis.EvenBN.GMSK.Selector
import CFSG.LocalAnalysis.EvenBN.GMSK.SL2Facts
import CFSG.Milestones.CT_catalog_nonabelian_type_partition

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open CFSG.Blueprint

theorem exists_mul_ne_of_sl2 {D : Type} [Group D] {S : Subgroup D} {K : Type} [Field K]
    (φ : S ≃* Matrix.SpecialLinearGroup (Fin 2) K) : ∃ a b : D, a * b ≠ b * a := by
  obtain ⟨x, y, hxy⟩ := sl2_exists_mul_ne (K := K)
  refine ⟨φ.symm x, φ.symm y, fun h => hxy ?_⟩
  have h' : φ.symm x * φ.symm y = φ.symm y * φ.symm x := Subtype.ext h
  simpa using congrArg φ h'

theorem catalog_selector
    (hAlt : FixedRootSelector fun D _ => ∃ m : ℕ, 5 ≤ m ∧ Nonempty (D ≃* alternatingGroup (Fin m)))
    (hOdd : FixedRootSelector fun D _ => OddLieType D)
    (hEven : FixedRootSelector fun D _ => EvenLieType D)
    (hSpor : FixedRootSelector fun D _ => NativeSporadic.SporadicRep D) :
    FixedRootSelector fun D _ => Catalog D := by
  intro D _ _ hD hcat n hn K _ _ hK α hα S hSα hSn ⟨φ⟩ hr
  rcases (Milestones.ct_catalog_nonabelian_type_partition D (exists_mul_ne_of_sl2 φ)).1 hcat with
    h | h | h | h
  · exact hAlt D hD h n hn K hK α hα S hSα hSn ⟨φ⟩ hr
  · exact hOdd D hD h n hn K hK α hα S hSα hSn ⟨φ⟩ hr
  · exact hEven D hD h n hn K hK α hα S hSα hSn ⟨φ⟩ hr
  · exact hSpor D hD h n hn K hK α hα S hSα hSn ⟨φ⟩ hr

end CFSG.LocalAnalysis.EvenBN.GMSK
