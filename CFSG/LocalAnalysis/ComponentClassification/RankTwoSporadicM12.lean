module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12W
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M12

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.ComponentClassification.M12Cover
open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.PartOne
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

theorem rep_m12A1Arr : Rep 24 m12A1Arr m12A1 := by
  intro x
  revert x
  decide

theorem rep_m12B1Arr : Rep 24 m12B1Arr m12B1 := by
  intro x
  revert x
  decide

theorem rep_m12SigArr : Rep 24 m12SigArr m12Sigma := by
  intro x
  revert x
  decide

theorem m12Base_nodup : m12Base.Nodup := by decide

theorem blockGroup_eq_closure : blockGroup = closure {m12A1, m12B1} := by
  rw [blockGroup, m12D_eq_closure]
  congr 1
  ext g
  simp

theorem m12InP_iff {S : Array (Array ℕ)} {Wd : Array (List ℤ)} (hk : 2 ≤ S.size)
    (hch : caseChainOK2P 24 S m12BaseArr Wd m12A1Arr m12B1Arr = true) (a : Array ℕ)
    (g : Equiv.Perm (Fin 24)) (h : Rep 24 a g) : m12InP S a = true ↔ g ∈ blockGroup := by
  obtain ⟨hc, e0, e1⟩ := caseChainOK2P_parts hch
  have hA : ChainArrays
      (RawSchreierDatum.ofArrays 24 (by norm_num) S 2 hk m12Base m12Base_nodup Wd)
      (S.extract 0 2) S (m12Base.map Fin.val).toArray Wd :=
    chainArrays_ofArrays (chainCheckFacts hc).strong_inv
  rw [m12InP, m12BaseArr, siftA_iff_mem_originalSubgroup hA (by norm_num) hc h,
    originalSubgroup_ofArrays_twoP hc rep_m12A1Arr rep_m12B1Arr e0 e1, blockGroup_eq_closure]

theorem autModelConj_bijective :
    Function.Bijective autModelConj := by
  have h : (autModelConj : ↥autModel → MulAut ↥blockGroup) =
      (MulAut.congr m12EquivD.symm).symm ∘ autModelHom := by
    funext δ
    show autModelConj δ =
      (MulAut.congr m12EquivD.symm).symm ((MulAut.congr m12EquivD.symm) (autModelConj δ))
    rw [MulEquiv.symm_apply_apply]
  rw [h]
  exact (MulAut.congr m12EquivD.symm).symm.bijective.comp autModelHom_bijective

theorem m12AutModel :
    AutModel (Blueprint.NativeSporadic.Carrier .M12) ↥autModel (blockGroup.subgroupOf autModel) :=
  autModel_of_conj blockGroup_le_autModel m12EquivD.symm
    (MulEquiv.ofBijective autModelConj autModelConj_bijective) fun _ _ => rfl

theorem m12_normal : (blockGroup.subgroupOf autModel).Normal :=
  normal_of_index_eq_two index_blockGroup

theorem m12_yCensusExc {S : Array (Array ℕ)} {Wd : Array (List ℤ)}
    {e0 : Array (Array ℕ)} {sG roots : Array ℕ} {nodes : Array CFSG.KC.Census.NodeP}
    {cS : CFSG.KC.Census.ArrCertP} {wcs : Array (Array CFSG.KC.Census.ArrCertP)}
    {excs : List CFSG.KC.Census.ExcRefP}
    (h : m12CheckW S Wd e0 sG roots nodes cS wcs excs = true) :
    YCensus (blockGroup.subgroupOf autModel) (ExcClass autModel (closure (permsA 24 e0))) := by
  simp only [m12CheckW, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hk, hch⟩, hc⟩, hgen⟩, hsize⟩ := h
  exact yCensusExc_pair_of_checkW (k := 7) (m := 1485) blockGroup_le_autModel m12_normal m12PS_lt
    (m12InP_iff hk hch) rep_m12SigArr sigma_mem_autModel hc hgen hsize
    (by rw [card_autModel]; norm_num) (by decide)

end CFSG.ComponentClassification.RankTwoSporadic.M12
