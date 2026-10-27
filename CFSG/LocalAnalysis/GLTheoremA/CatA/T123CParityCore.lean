module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Compl123
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.ScpQuot
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123C

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

@[expose] def Type167JAt (p : ℕ) (J : Type) [Group J] : Prop :=
  (p = 3 ∧ ∃ n : ℕ, Odd n ∧ 5 ≤ n ∧ catalogIs J (isLnA n 2)) ∨
  (p = 3 ∧ ∃ n : ℕ, Even n ∧ 6 ≤ n ∧ catalogIs J (isOmMA n 2)) ∨
  (∃ n k : ℕ, Odd n ∧ 3 ≤ n ∧ (k = 1 → 5 ≤ n) ∧ 1 ≤ k ∧ p ∣ 2 ^ k + 1 ∧
    catalogIs J (isOmPA n (2 ^ k)))

@[expose] def ParityCoreAt (p : ℕ) (J : Type) [Group J] : Prop :=
  ∀ A : Subgroup (MulAut J), IsPGroup p ↥A →
    ∃ U : Subgroup J, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ α ∈ A, ∀ u ∈ U, α u ∈ U

@[expose] def Aut167JCore : Prop :=
  ∀ (p : ℕ) (J : Type) [Group J] [Finite J], p.Prime → p ≠ 2 → Type167JAt p J →
    ParityCoreAt p J

@[expose] def ParityCoreLinA : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K], Odd n → 5 ≤ n → Nat.card K = 2 →
    ParityCoreAt 3 (projectiveSL n K)

@[expose] def ParityCoreL4 : Prop :=
  ∀ (p k : ℕ) (K : Type) [Field K] [Finite K], p.Prime → p ≠ 2 → 2 ≤ k → p ∣ 2 ^ k + 1 →
    Nat.card K = 2 ^ k → ParityCoreAt p (projectiveSL 4 K)

@[expose] def ParityCoreOmMinus : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] (b c : K), Even n → 6 ≤ n → Nat.card K = 2 →
    (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      ParityCoreAt 3 (StatedProj (StatedOmega (StatedQuadMinus n K b c)))

@[expose] def ParityCoreOmPlus : Prop :=
  ∀ (p n k : ℕ) (K : Type) [Field K] [Finite K], p.Prime → p ≠ 2 → Odd n → 5 ≤ n → 1 ≤ k →
    p ∣ 2 ^ k + 1 → Nat.card K = 2 ^ k →
      ParityCoreAt p (StatedProj (StatedOmega (StatedQuadPlus n K)))

theorem parityCoreAt_of_mulEquiv {p : ℕ} {J J' : Type} [Group J] [Group J'] (e : J ≃* J')
    (h : ParityCoreAt p J') : ParityCoreAt p J := by
  intro A hA
  let φ : MulAut J ≃* MulAut J' := MulAut.congr e
  obtain ⟨U', hU', hU'2, hinv⟩ := h (A.map φ.toMonoidHom) (hA.map φ.toMonoidHom)
  refine ⟨U'.map e.symm.toMonoidHom, ?_, hU'2.map e.symm.toMonoidHom, ?_⟩
  · intro hbot
    apply hU'
    rw [Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective] at hbot
    exact hbot
  · rintro α hα _ ⟨u, hu, rfl⟩
    have hφ : φ α ∈ A.map φ.toMonoidHom := Subgroup.mem_map_of_mem _ hα
    refine ⟨φ α u, hinv _ hφ u hu, ?_⟩
    simp [φ, MulAut.congr_apply]

theorem type167JAt_of_type167J {G : Type} [Group G] {p : ℕ} {K : Subgroup G}
    (h : Type167J p K) : Type167JAt p (PSimple p K) := by
  rcases h with ⟨rfl, n, hn, h5, hc⟩ | ⟨rfl, n, hn, h6, hc⟩ | ⟨n, k, hn, h3, hk, h1, hdvd, hc⟩
  · exact Or.inl ⟨rfl, n, hn, h5, hc⟩
  · exact Or.inr (Or.inl ⟨rfl, n, hn, h6, hc⟩)
  · exact Or.inr (Or.inr ⟨n, k, hn, h3, hk, h1, hdvd, hc⟩)

end CFSG.LocalAnalysis.GLTheoremA.T123C

end
