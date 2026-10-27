module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.SignSound
public import CFSG.RankThree.PartOne.S11c.HNInvQ6
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HSData
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public noncomputable section

namespace CFSG.EvenSporadicStandard.TwoHS

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore CFSG.RankThree.PartOne.HNRed
  CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section HN


theorem Dsub_noncomm : ∃ a b : Dsub, a * b ≠ b * a := by
  refine ⟨⟨aD, Subgroup.subset_closure (Set.mem_insert _ _)⟩,
    ⟨bD, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩, fun h => ?_⟩
  exact abD_ne_ba (congrArg (fun x : Dsub => (x : Equiv.Perm (Fin 1100))) h)

theorem coverData_aux
    (t : C6) (h1 : t ∈ phi6.ker) (h2 : t ≠ 1) (h3 : ∀ x : C6, x * t = t * x) :
    CoverData phi6 Dsub t where
  card_ker := card_ker_phi6
  mem_ker := h1
  ne_one := h2
  central := h3
  le_range := Dsub_le_range
  normalizes := range_le_normalizer_D
  index_two := index_Dr
  simple := Dsub_simple
  noncomm := Dsub_noncomm
  centralizer_trivial := fun _ hz => centralizer_Dsub_trivial hz
  quotient := nonempty_Dsub_mulEquiv_HS

theorem orderOf_aJ : orderOf aJ = 2 := orderOf_eq_prime aJ_sq aJ_ne_one

theorem hnCentralizerFacts_aux
    (t : C6) (htJ : (t : JH) = aJ)
    (h1 : t ∈ phi6.ker) (h2 : t ≠ 1) (h3 : ∀ x : C6, x * t = t * x) : HNCentralizerFacts :=
  have hs := sign_core_aux t htJ (MonoidHom.mem_ker.1 h1) h3
  @hnCentralizerFacts_of_coverData JH inferInstance (@hnEquivJ) aJ orderOf_aJ
    (Equiv.Perm (Fin 1100)) inferInstance phi6 Dsub t (coverData_aux t h1 h2 h3) hs.2 hs.1

theorem hnCentralizerFacts :
    HNCentralizerFacts :=
  hnCentralizerFacts_aux t6C coe_t6C t6C_mem_ker t6C_ne_one t6C_central

end HN

end CFSG.EvenSporadicStandard.TwoHS
