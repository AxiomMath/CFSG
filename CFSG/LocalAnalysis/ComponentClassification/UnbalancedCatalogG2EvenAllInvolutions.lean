module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenInnerInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenOuterInvolutions
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951
public import CFSG.LieType.Chevalley.SignKernelComponentPerfect

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem even_G2_all_involution_full_centralizer_odd_core {f : ℕ} (hf : 2 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = 2 ^ f) (H : Subgroup (MulAut (adjointGroup .G2 K)))
    (hIH : inner (adjointGroup .G2 K) ≤ H) {α : MulAut (adjointGroup .G2 K)}
    (hα : orderOf α = 2) : CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥ := by
  by_cases hαI : α ∈ inner (adjointGroup .G2 K)
  · exact even_G2_inner_involution_full_centralizer_odd_core hf K hK H hIH hαI hα
  · exact even_G2_outer_involution_full_centralizer_odd_core hf K hK H hIH hαI hα

end CFSG.ComponentClassification.UnbalancedCatalog
