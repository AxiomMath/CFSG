module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverU42Check
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicYCriterion
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutTables
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelBorel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.Monster.Code.Weights
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.ComponentClassification.RankTwoHypIICover.U42

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.ComponentClassification.CatFactsSmall.PSp43

theorem rep_arr45 (g : Equiv.Perm (Fin 45)) : Rep 45 (arr45 g) g := fun x => by
  rw [arr45, getElem!_ofFn_nat _ x.2]

theorem u42S_getElem! {i : ℕ} (hi : i < 2) : u42S[i]! = u42Gens[i]! :=
  CFSG.EvenSmallLie.OmegaEight.pushWords_getElem! _ _ (by simp [u42Gens]; omega)

@[expose] noncomputable def u42Q : RawSchreierDatum 45 :=
  RawSchreierDatum.ofArrays 45 (by norm_num) u42S 2 (by simp [u42S, u42Gens,
    CFSG.EvenSmallLie.OmegaEight.size_pushWords]) u42BaseL (by decide)
    (CFSG.EvenSmallLie.OmegaEight.wordsOf 2 u42Words)

theorem u42Q_originalSubgroup : u42Q.originalSubgroup = QP45.originalSubgroup := by
  rw [u42Q, J2Cover.ofArrays_originalSubgroup, QP45_closure]
  refine congrArg Subgroup.closure (Set.ext fun g => ?_)
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  have h0 : permOfArr 45 u42S[0]! = x45 := by
    rw [u42S_getElem! (by norm_num)]
    exact permOfArr_eq_of_rep (rep_arr45 x45)
  have h1 : permOfArr 45 u42S[1]! = y45 := by
    rw [u42S_getElem! (by norm_num)]
    exact permOfArr_eq_of_rep (rep_arr45 y45)
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact Or.inl h0
    · exact Or.inr h1
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, h0⟩
    · exact ⟨1, by norm_num, h1⟩

theorem u42InX_iff (hch : rawChainOK 45 (u42S.extract 0 2) u42S u42Base
      (CFSG.EvenSmallLie.OmegaEight.wordsOf 2 u42Words) 4 = true)
    (a : Array ℕ) (g : Equiv.Perm (Fin 45)) (h : Rep 45 a g) :
    u42InX a = true ↔ g ∈ QP45.originalSubgroup := by
  rw [← u42Q_originalSubgroup]
  exact J2Cover.ofArrays_mem_iff (by norm_num) hch h

theorem QP45_le_QA45 : QP45.originalSubgroup ≤ QA45.originalSubgroup := by
  rw [QP45_closure, QA45_closure, closure_le]
  rintro g (rfl | rfl)
  · exact subset_closure (Set.mem_insert _ _)
  · exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

theorem f45_mem_QA45 : f45 ∈ QA45.originalSubgroup := by
  rw [QA45_closure]
  exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem card_QA45 : Nat.card QA45.originalSubgroup = 51840 := by
  rw [← QA45.orderCertificate_eq_card QA45_ok, QA45_valid.2]

theorem u42AutModel :
    AutModel ↥QP45.originalSubgroup ↥QA45.originalSubgroup
      (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup) := by
  obtain ⟨M, hMP, hMA⟩ := exists_model (MulEquiv.refl QP45.originalSubgroup)
  obtain ⟨P, A, e, Φ, spec⟩ := M
  simp only at hMP hMA
  subst hMP hMA
  refine autModel_of_conj QP45_le_QA45 e.symm (Φ.symm.trans (MulAut.congr e)) fun σ x => ?_
  have h := spec (Φ.symm σ) (e.symm x)
  simp only [MulEquiv.apply_symm_apply] at h
  simp only [MulEquiv.trans_apply, MulAut.congr_apply]
  exact h

theorem statedClassicalModel_PSp43 :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel CFSG.GH74.Exceptional.PSp43 .PSp 2 3 1 :=
  ⟨⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩, ZMod 3, inferInstance, inferInstance,
    by simp, ⟨MulEquiv.refl _⟩⟩

end CFSG.ComponentClassification.RankTwoHypIICover.U42
