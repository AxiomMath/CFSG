module

public import Certificates.Certificate55107
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7Loc.U33Cent

open CFSG Subgroup


theorem card_P : Nat.card KGroups.U33.QP.originalSubgroup = 6048 :=
  Certificates.certificate55107.1

theorem centralizer_eq_bot :
    centralizer (KGroups.U33.QP.originalSubgroup : Set (Equiv.Perm (Fin 28))) = ⊥ :=
  Certificates.certificate55107.2.1

theorem outer_facts : ∃ u : Equiv.Perm (Fin 28), u ^ 2 = 1 ∧ u ∉ KGroups.U33.QP.originalSubgroup ∧
    (∀ p ∈ KGroups.U33.QP.originalSubgroup, u * p * u⁻¹ ∈ KGroups.U33.QP.originalSubgroup) ∧
    ∀ t ∈ KGroups.U33.QP.originalSubgroup ⊔ zpowers u, orderOf t = 2 →
      CFSG.oddCore ↥(KGroups.U33.QP.originalSubgroup ⊓
        centralizer ({t} : Set (Equiv.Perm (Fin 28)))) = ⊥ :=
  Certificates.certificate55107.2.2

end CFSG.GH74.Generic.BProg.B3.S3T2A7Loc.U33Cent
