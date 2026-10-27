module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Lattice
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoKernel
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3A314Red
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Listed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Aut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.RankThree.Asc83Table.M23
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.Sporadic.Schreier.M23
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat

theorem card_eq_of_isSylowTwoOf {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) {a m : ℕ} (hm : ¬ 2 ∣ m) (hcard : Nat.card X = 2 ^ a * m) :
    Nat.card T = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hs⟩ := hT.2.1.exists_card_eq
  have hidx : Nat.card X = Nat.card T * T.index := (Subgroup.card_mul_index T).symm
  have hodd : ¬ 2 ∣ T.index := by
    have h1 : (T.subgroupOf (⊤ : Subgroup X)).index = T.index := Subgroup.relIndex_top_right T
    have := hT.2.2
    rwa [h1] at this
  have hi0 : T.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 2)
  rw [hs] at hidx ⊢
  have h12 : 2 ^ s * T.index = 2 ^ a * m := hidx.symm.trans hcard
  have e1 : padicValNat 2 (2 ^ s * T.index) = s := by
    rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) hi0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hodd, add_zero]
  have e2 : padicValNat 2 (2 ^ a * m) = a := by
    rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm, add_zero]
  have : s = a := e1.symm.trans ((congrArg (padicValNat 2) h12).trans e2)
  rw [this]

theorem noDelta5In_of_rows {X : Type} [Group X] [Finite X] (hX : IsSimpleGroup X) {a m : ℕ}
    (hm : ¬ 2 ∣ m) (hcard : Nat.card X = 2 ^ a * m) (mems : List Mem)
    (hmems : ∀ r ∈ mems, r.order = 15 * 2 ^ a → r.quot2 * 64 < 2 ^ a)
    (hover : ∀ T Y : Subgroup X, IsSylowTwoOf T ⊤ → T ≤ Y → Y = ⊤ ∨
      ∃ r ∈ mems, Nat.card Y = r.order ∧ Nat.card (pCoreOf 2 Y) = r.o2 ∧
        ∀ (N : Subgroup Y) [N.Normal], IsPGroup 2 (Y ⧸ N) → Nat.card (Y ⧸ N) ≤ r.quot2) :
    NoDelta5In X := by
  refine noDelta5In_of_overgroups hX (t₂ := 2 ^ a)
    (fun T hT => card_eq_of_isSylowTwoOf hT hm hcard) ?_
  intro T Y hT hTY
  rcases hover T Y hT hTY with h | ⟨r, hr, hord, -, hq⟩
  · exact Or.inl h
  · refine Or.inr fun hY => ?_
    rw [hord] at hY
    exact ⟨r.quot2, hmems r hr hY, fun N _ hN => hq N hN⟩

end CFSG.QuasithinUnique.A5.G3
