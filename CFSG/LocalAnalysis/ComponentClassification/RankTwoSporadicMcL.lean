module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicMcLCheck
public import CFSG.RankThree.Native.HSMcLAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensusW

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.McL

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native CFSG.Sporadic.Schreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem mcl275P_le_R : mcl275P ≤ mcl275R := mcl275R_eq_sup ▸ le_sup_left

theorem mcl275U_mem_R : mcl275U ∈ mcl275R := mcl275R_eq_sup ▸ mem_sup_right (mem_zpowers _)

theorem rep_mclUArr : Rep 275 mclUArr mcl275U :=
  (rep_permOfArr mcl275R_chain_check.2.2.2.2.2).1

theorem mclInP_iff (a : Array ℕ) (g : Equiv.Perm (Fin 275)) (h : Rep 275 a g) :
    mclInP a = true ↔ g ∈ mcl275P := by
  rw [mcl275P_eq, mclP_eq_original]
  exact siftA_iff_mem_originalSubgroup mclChainArrays (by norm_num) PairMcL.chain_check.1 h

theorem mclAutModel :
    AutModel (Blueprint.NativeSporadic.Carrier .McL) ↥mcl275R (mcl275P.subgroupOf mcl275R) := by
  obtain ⟨-, -, -, -, -, ⟨e, he, -⟩, -⟩ := CTUC_HS_McL_full_automorphism_permutation_models.2
  exact autModel_of_conj mcl275P_le_R mcl275Equiv.symm e he

theorem mcl_normal : (mcl275P.subgroupOf mcl275R).Normal := by
  obtain ⟨-, -, -, -, -, -, h, -⟩ := CTUC_HS_McL_full_automorphism_permutation_models.2
  exact h

theorem card_mcl275R : Nat.card mcl275R = 1796256000 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h⟩ := CTUC_HS_McL_full_automorphism_permutation_models.2
  exact h

theorem mcl_yCensus : YCensus (mcl275P.subgroupOf mcl275R) (fun _ => False) := by
  have h := mcl_check
  simp only [mclCheckW, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hc, hgen⟩, hsize⟩ := h
  exact yCensus_pair_of_checkW (k := 8) (m := 7016625) mcl275P_le_R mcl_normal mclPS_lt
    mclInP_iff rep_mclUArr mcl275U_mem_R hc hgen hsize (by norm_num [card_mcl275R]) (by decide)

theorem sporadicCaseOdd_McL (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) :
    SporadicCaseOdd .McL :=
  sporadicCaseOdd_of_yCensus h32 h33 mclAutModel mcl_yCensus

end CFSG.ComponentClassification.RankTwoSporadic.McL
