module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundBase
import CFSG.LocalAnalysis.GLTheoremA.S11.Lemma119
import CFSG.Certificates.Kernel.LocalCompTits.Span
import CFSG.CharacterTheory.Blocks.Defs
import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
import CFSG.Dihedral.DihedralFusionPrefixes
import CFSG.GH74.GLS.Bg.Statements
import CFSG.GH74.GLS.Defs
import CFSG.Goldschmidt.Statements
import CFSG.Goldschmidt.StatementsG
import CFSG.Goldschmidt.StatementsG2
import CFSG.Goldschmidt.StatementsH
import CFSG.Holt.Fixed
import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
import CFSG.LocalAnalysis.ComponentClassification.KProper
import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
import CFSG.LocalAnalysis.SignalizerFunctor
import CFSG.Open.SplitBNPair
import CFSG.Quasithin.Background.A3Structure318Red
import CFSG.Quasithin.Background.A3Structure36A
import CFSG.Quasithin.Background.A3Structure36BAction
import CFSG.Quasithin.Background.A3Structure36BBase
import CFSG.Quasithin.Background.A3Structure36BCase3Base
import CFSG.Quasithin.Background.A3Structure36BCasesBase
import CFSG.Quasithin.Background.A3Structure36BCommonBase
import CFSG.Quasithin.Background.A3Structure36BFrattini
import CFSG.Quasithin.Background.A3Structure36BHeisBase
import CFSG.Quasithin.Background.A3Structure36BHomocyclic
import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
import CFSG.Quasithin.Background.A3Structure36BStarBase
import CFSG.Quasithin.Background.A3Structure36Base
import CFSG.Quasithin.Background.A3Structure37Base
import CFSG.Quasithin.Background.A3Structure37Comm
import CFSG.Quasithin.Background.A3Structure37Frattini
import CFSG.Quasithin.Background.A3Structure37KeyBase
import CFSG.Quasithin.Background.A3Structure37Schur
import CFSG.Quasithin.Background.A3Structure38Part3
import CFSG.Quasithin.Background.B1MoreElevenE
import CFSG.Quasithin.Background.B1MoreNineG
import CFSG.Quasithin.Background.B2FactorizationResidual
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Quasithin.Background.B4ModelsIso
import CFSG.Quasithin.Background.C2Basic
import CFSG.Quasithin.Background.C2Inputs
import CFSG.Quasithin.Background.E1
import CFSG.Quasithin.Background.E1Sec4
import CFSG.Quasithin.Background.E1Sec5
import CFSG.Quasithin.Background.E1Sec8
import CFSG.Quasithin.Background.E1Solv
import CFSG.Quasithin.Background.E1Twelve
import CFSG.Quasithin.Background.E3Cent
import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
import CFSG.Quasithin.H13.StatementsL1
import CFSG.Quasithin.Vol2.Ch10StatementsE
import CFSG.Quasithin.Vol2.Ch10StatementsInputs
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
import CFSG.Quasithin.Vol2.Ch1Local
import CFSG.RankThree.PartTwo.Sec20.OneSteps
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.Sporadic.Schreier.J4SProfileNode
import CFSG.Walter.Bender1970.S1
import CFSG.Walter.Bender1970.S2
import CFSG.Walter.Bender1970.S3.PGroupFStar
import CFSG.Walter.PSL2Facts
import Certificates.Certificate1
import Certificates.Certificate10
import Certificates.Certificate100
import Certificates.Certificate101
import Certificates.Certificate102
import Certificates.Certificate103
import Certificates.Certificate104
import Certificates.Certificate105
import Certificates.Certificate106
import Certificates.Certificate107
import Certificates.Certificate108
import Certificates.Certificate109
import Certificates.Certificate11
import Certificates.Certificate12
import Certificates.Certificate2
import Certificates.Certificate3
import Certificates.Certificate4
import Certificates.Certificate42
import Certificates.Certificate44
import Certificates.Certificate5
import Certificates.Certificate6
import Certificates.Certificate7
import Certificates.Certificate8
import Certificates.Certificate9
import Certificates.Certificate96
import Certificates.Certificate97
import Certificates.Certificate98
import Certificates.Certificate99
import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
import Certificates.Kernel.J4Count.FixCE
import Certificates.Kernel.J4Count.FixCPairBase1
import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L J A : Subgroup G} {d b : G} {n : ℕ}

theorem card_le_three_cube_of_u6 (hm : U6Marking) (ht : U6Type9) (hs : U6SizeModel)
    (hsetup : Setup 3 L J A d b)
    (hcat : catalogIs (PSimple 3 L) (S10.isU6n n)) (hn : Odd n) (h3 : 3 ∣ 2 ^ n + 1) :
    Nat.card A ≤ 3 ^ 3 := by
  classical
  obtain ⟨K, hK, hKfin, hUF, θ, hact⟩ := hm G L J A d b n hsetup hcat hn
  let R := LargeEvenProj (unitarySU 2 n K 6)
  let I := LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
    (LargeEvenGUSet (Fin 6) K (2 ^ n))
  let Φ0 : ↥A → MulAut R := fun a => Classical.choose (hact a.1 a.2)
  have hΦ0mem : ∀ a : ↥A, Φ0 a ∈ I := fun a =>
    (Classical.choose_spec (hact a.1 a.2)).1
  have hΦ0ind : ∀ a : ↥A, LargeEvenInduces θ (conjRel a.1) (Φ0 a) := fun a =>
    (Classical.choose_spec (hact a.1 a.2)).2
  have hAnorm : A ≤ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S11.le_normalizer_of_innerDiag hsetup.idiag
  have hΦ0_one : Φ0 1 = 1 := by
    have h1 : LargeEvenInduces θ (conjRel (1 : G)) (1 : MulAut R) :=
      largeEvenInduces_one (rel := conjRel (1 : G)) fun l l' hl => by
        have hl' : (l' : G) = (l : G) := by simpa [conjRel] using hl
        exact Subtype.ext hl'.symm
    exact largeEvenInduces_unique (hΦ0ind 1) h1 (conjRel_total (Subgroup.one_mem _))
  have hΦ0_mul : ∀ a b : ↥A, Φ0 (a * b) = Φ0 a * Φ0 b := by
    intro a b
    have hab : (a : G) * (b : G) = (b : G) * (a : G) :=
      IsElemAbelian.comm hsetup.elem a.2 b.2
    have h1 : LargeEvenInduces θ (conjRel ((a : G) * (b : G))) (Φ0 a * Φ0 b) :=
      largeEvenInduces_mul (hAnorm a.2) (hAnorm b.2) hab (hΦ0ind a) (hΦ0ind b)
    exact largeEvenInduces_unique (hΦ0ind (a * b)) h1
      (conjRel_total (hAnorm (Subgroup.mul_mem A a.2 b.2)))
  let Φ : ↥A →* MulAut R :=
    { toFun := Φ0
      map_one' := hΦ0_one
      map_mul' := hΦ0_mul }
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    have hg : (a : G) * (b : G)⁻¹ ∈ A :=
      Subgroup.mul_mem A a.2 (inv_mem b.2)
    have hgN : (a : G) * (b : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) := hAnorm hg
    have hmap : Φ (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have hzero : LargeEvenInduces θ (conjRel ((a : G) * (b : G)⁻¹))
        (1 : MulAut R) := hmap ▸ hΦ0ind (a * b⁻¹)
    have hcent : (a : G) * (b : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) :=
      centralizes_of_conjRel_center hgN
        (exists_center_of_largeEvenInduces_one hgN hzero)
        (Group.isPerfect_def.mpr hsetup.qs.1)
    have hinf : (a : G) * (b : G)⁻¹ ∈ A ⊓ Subgroup.centralizer (L : Set G) :=
      Subgroup.mem_inf.mpr ⟨hg, hcent⟩
    rw [hsetup.faithful] at hinf
    have hgone : (a : G) * (b : G)⁻¹ = 1 := Subgroup.mem_bot.mp hinf
    apply Subtype.ext
    calc (a : G) = (a : G) * (b : G)⁻¹ * (b : G) := by group
      _ = 1 * (b : G) := by rw [hgone]
      _ = (b : G) := one_mul _
  have hAbel : IsElemAbelian 3 Φ.range := by
    have hcomm : ∀ a ∈ (Φ.range : Set (MulAut R)), ∀ b ∈ (Φ.range : Set (MulAut R)),
        a * b = b * a := by
      intro x hx y hy
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hy
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (IsElemAbelian.comm hsetup.elem a.2 b.2)
    have hpow : ∀ a ∈ (Φ.range : Set (MulAut R)), a ^ 3 = 1 := by
      intro x hx
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
      have ha3 : a ^ 3 = 1 := by
        apply Subtype.ext
        simpa using hsetup.elem.2 a.1 a.2
      rw [← map_pow, ha3, map_one]
    have h := IsElemAbelian.closure_of_commute (s := (Φ.range : Set (MulAut R))) hcomm hpow
    rwa [Subgroup.closure_eq] at h
  have hAbmem : ∀ x ∈ Φ.range, x ∈ I := by
    intro x hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    exact hΦ0mem a
  have hfield : ∃ x ∈ Φ.range, FieldType hUF x := by
    refine ⟨Φ ⟨d, hsetup.d_mem⟩, ⟨⟨d, hsetup.d_mem⟩, rfl⟩, ?_⟩
    exact ht G L J A d b n K hUF θ hsetup h3 hact (Φ ⟨d, hsetup.d_mem⟩)
      (hΦ0ind ⟨d, hsetup.d_mem⟩)
  have hsize : Nat.card Φ.range ≤ 3 ^ 3 :=
    hs n K hUF h3 Φ.range hAbel hAbmem hfield
  have hinj : Function.Injective (fun a : ↥A => (⟨Φ a, ⟨a, rfl⟩⟩ : Φ.range)) := by
    intro a b hab
    exact hΦinj (Subtype.ext_iff.mp hab)
  have hcard : Nat.card A ≤ Nat.card Φ.range :=
    Nat.card_le_card_of_injective _ hinj
  exact hcard.trans hsize

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
