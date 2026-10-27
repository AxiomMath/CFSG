
module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHSCheckBase
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicConjWY
public import CFSG.RankThree.Native.HSMcLAut
public import CFSG.RankThree.Native.HSMcLAuxData
public import CFSG.Sporadic.Schreier.PairHSCert
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.RankThree.Native.HSMcLSmallCheckInputs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHSTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicConjW
public import CFSG.Sporadic.Schreier.PairHSCheckInputs
public meta import CFSG.Sporadic.Schreier.PairHSCert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.Schreier.PairMcLCertInputs
public import CFSG.Sporadic.Schreier.PairMcLCheckInputs
public meta import CFSG.Sporadic.Schreier.PairMcLCert
public import CFSG.Sporadic.Schreier.PairMcLCheck
public import Certificates.Data.CFSGNative.PairSchreier.Counts
public meta import CFSG.Sporadic.Schreier.PairMcLCheck
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts
public import CFSG.Sporadic.SmallOddCore.HSCheckInputs
public import CFSG.Sporadic.SmallOddCore.HSWordBoundInputs
public meta import CFSG.Sporadic.Schreier.PairHSCheck
public import CFSG.Sporadic.SmallOddCore.McLCheckInputs
public meta import CFSG.Sporadic.SmallOddCore.McLData
public import CFSG.Sporadic.SmallOddCore.McLWords
public meta import CFSG.Sporadic.SmallOddCore.McLWords
public import CFSG.Sporadic.SmallOddCore.McL
public import CFSG.Sporadic.SmallOddCore.AutCount
public import CFSG.Sporadic.SmallOddCore.CountSplit
public import CFSG.Sporadic.SmallOddCore.McLCountA
public import CFSG.Sporadic.Schreier.PairMcLPairs
public import CFSG.Sporadic.Schreier.PairHSCertInputs
public import Certificates.Data.CFSGNative.HS.Data
public import CFSG.Sporadic.Schreier.PairHSFaithfulInputs
public meta import CFSG.Sporadic.Schreier.PairF2Sep
public meta import Certificates.Data.CFSGNative.HS.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.Monster.Code.Weights

@[expose] public section

namespace CFSG.ComponentClassification.RankTwoSporadic.HS

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem hsInP_iff (a : Array ℕ) (g : Equiv.Perm (Fin 100)) (h : Rep 100 a g) :
    hsInP a = true ↔ g ∈ hs100P := by
  rw [hs100P_eq_original]
  exact siftA_iff_mem_originalSubgroup hs100ChainArrays (by norm_num) hs100_chain_check.1 h

theorem hsAutModel :
    AutModel (Blueprint.NativeSporadic.Carrier .HS) ↥hs100R (hs100P.subgroupOf hs100R) := by
  obtain ⟨-, -, -, -, -, ⟨e, he, -⟩, -⟩ := CTUC_HS_McL_full_automorphism_permutation_models.1
  exact autModel_of_conj hs100P_le_R hs100Equiv.symm e he

end CFSG.ComponentClassification.RankTwoSporadic.HS
