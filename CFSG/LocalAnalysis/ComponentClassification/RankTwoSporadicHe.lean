module

public import CFSG.Sporadic.HeldB.AutModel
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.He

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Sporadic.HeldB
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem heAutModel :
    AutModel (Blueprint.NativeSporadic.Carrier .He) ↥heAutGroup (heP.subgroupOf heAutGroup) := by
  obtain ⟨hbij, -⟩ := ctbh_full_automorphism_permutation_model
  exact autModel_of_conj heP_le_heAutGroup heEquivP.symm (MulEquiv.ofBijective heConjR hbij)
    fun x p => heConjR_apply x p

theorem he_commutator_le :
    ⁅(⊤ : Subgroup ↥heAutGroup), ⊤⁆ ≤ heP.subgroupOf heAutGroup :=
  commutator_le_of_index_two heP_relIndex_heAutGroup

end CFSG.ComponentClassification.RankTwoSporadic.He
