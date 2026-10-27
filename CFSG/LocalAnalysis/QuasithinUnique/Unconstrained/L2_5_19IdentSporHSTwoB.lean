module

public import CFSG.Sporadic.SmallOddCore.HSData
public import CFSG.Sporadic.SmallOddCore.LocalSpec
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentSporGlue
public meta import CFSG.Sporadic.SmallOddCore.HSData
public meta import CFSG.Sporadic.SmallOddCore.LocalCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentSporHSTwoBInputs
public import Certificates.Certificate4150
public import CFSG.Assembly.OrderReductions.CharacterInflation
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.ClassicalGroups
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdGen
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Rank2
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Schreier.M23
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate8026Base

public section

namespace CFSG.QuasithinUnique.Id2519.SporHS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open scoped commutatorElement

theorem twoB_check : twoBCheck = true :=
  Certificates.certificate4150

theorem commOK_spec {n : ℕ} (hn : n < 2 ^ 32) {cap m : ℕ} {gs cs : List Table}
    (hg : ∀ g ∈ gs, permOK n g = true) (hK : enumOK n cap m gs = true)
    (hc : ∀ c ∈ cs, permOK n c = true ∧ invOK n c (invT n c) = true)
    (h : commOK n cap gs cs = true) :
    ∀ c ∈ cs, ∀ c' ∈ cs, ⁅tp n c, tp n c'⁆ ∈ genOf n gs := by
  obtain ⟨-, hrep, -, -⟩ := enumOK_spec hn hg hK
  intro c hc' c' hcc'
  simp only [commOK, List.all_eq_true] at h
  have h1 := h c hc' c' hcc'
  have hrc := rep_tp (hc c hc').1
  have hrc' := rep_tp (hc c' hcc').1
  have hx : Rep n (compT n (compT n (compT n c c') (invT n c)) (invT n c'))
      (tp n c * tp n c' * (tp n c)⁻¹ * (tp n c')⁻¹) :=
    Rep.compT (Rep.compT (Rep.compT hrc hrc') (rep_invT hrc (hc c hc').2))
      (rep_invT hrc' (hc c' hcc').2)
  obtain ⟨k, hk, hkeq⟩ := memT_spec (fun k hk => (hrep k hk).1) hx h1
  rw [commutatorElement_def, hkeq]
  exact (hrep k hk).2

theorem commutator_genOf_le {n : ℕ} (hn : n < 2 ^ 32) {cap m : ℕ} {gs cs : List Table}
    (hg : ∀ g ∈ gs, permOK n g = true) (hK : enumOK n cap m gs = true)
    (hc : ∀ c ∈ cs, permOK n c = true ∧ invOK n c (invT n c) = true)
    (hnorm : normOK n cap gs cs = true) (hcomm : commOK n cap gs cs = true) :
    ⁅genOf n cs, genOf n cs⁆ ≤ genOf n gs := by
  have hN := normOK_spec hn hg hK hc hnorm
  have hC := commOK_spec hn hg hK hc hcomm
  refine commutator_closure_le (tp n '' {x | x ∈ cs.toArray}) (genOf n gs) ?_ ?_
  · rintro _ ⟨c, hcm, rfl⟩ a ha
    have hcm' : c ∈ cs := by simpa using hcm
    have hmem : tp n c ∈ normalizer (genOf n gs : Set (Equiv.Perm (Fin n))) :=
      hN (subset_closure ⟨c, hcm, rfl⟩)
    have h1 := (mem_normalizer_iff.1 hmem a).1 ha
    have hinv : (tp n c)⁻¹ ∈ normalizer (genOf n gs : Set (Equiv.Perm (Fin n))) :=
      (normalizer _).inv_mem hmem
    have h2 := (mem_normalizer_iff.1 hinv a).1 ha
    exact ⟨h1, h2⟩
  · rintro _ ⟨c, hcm, rfl⟩ _ ⟨c', hcm', rfl⟩
    exact hC c (by simpa using hcm) c' (by simpa using hcm')

theorem twoB_gens_ok :
    ∀ c ∈ twoBGens, permOK 3850 c = true ∧ invOK 3850 c (invT 3850 c) = true := by
  have h := twoB_check
  simp only [twoBCheck, Bool.and_eq_true, List.all_eq_true] at h
  intro c hc
  have := h.1.1.1.1 c hc
  simpa [Bool.and_eq_true] using this

theorem twoB_y_ok : ∀ g ∈ twoBY, permOK 3850 g = true := by
  have h := twoB_check
  simp only [twoBCheck, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1.1.1.2

theorem twoB_enum : enumOK 3850 400 360 twoBY = true := by
  have h := twoB_check
  simp only [twoBCheck, Bool.and_eq_true] at h
  exact h.1.1.2

theorem twoB_norm : normOK 3850 400 twoBY twoBGens = true := by
  have h := twoB_check
  simp only [twoBCheck, Bool.and_eq_true] at h
  exact h.1.2

theorem twoB_comm : commOK 3850 400 twoBY twoBGens = true := by
  have h := twoB_check
  simp only [twoBCheck, Bool.and_eq_true] at h
  exact h.2

theorem commutator_le_twoBY :
    ⁅genOf 3850 twoBGens, genOf 3850 twoBGens⁆ ≤ genOf 3850 twoBY :=
  commutator_genOf_le (by norm_num) twoB_y_ok twoB_enum twoB_gens_ok twoB_norm twoB_comm

theorem card_genOf_twoBY : Nat.card ↥(genOf 3850 twoBY) = 360 :=
  (enumOK_spec (by norm_num) twoB_y_ok twoB_enum).1

theorem card_commutator_twoB_le :
    Nat.card ↥⁅genOf 3850 twoBGens, genOf 3850 twoBGens⁆ ≤ 360 :=
  (Subgroup.card_le_of_le commutator_le_twoBY).trans card_genOf_twoBY.le

end CFSG.QuasithinUnique.Id2519.SporHS
