module

public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreDatum
public import CFSG.Milestones.CT_catalog_nonabelian_type_partition

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint

theorem qFixedRootSelector_catalog
    (hAlt : QFixedRootSelector fun D _ =>
      ∃ m : ℕ, 5 ≤ m ∧ Nonempty (D ≃* alternatingGroup (Fin m)))
    (hOdd : QFixedRootSelector fun D _ => OddLieType D)
    (hEven : QFixedRootSelector fun D _ => EvenLieType D)
    (hSpor : QFixedRootSelector fun D _ => NativeSporadic.SporadicRep D) :
    QFixedRootSelector fun D _ => Catalog D := by
  intro D _ _ hD hcat n α J d
  rcases (Milestones.ct_catalog_nonabelian_type_partition D d.nonabelian_ambient).1 hcat with
    h | h | h | h
  · exact hAlt D hD h n α J d
  · exact hOdd D hD h n α J d
  · exact hEven D hD h n α J d
  · exact hSpor D hD h n α J d

end CFSG.LocalAnalysis.EvenBN.GMSK
