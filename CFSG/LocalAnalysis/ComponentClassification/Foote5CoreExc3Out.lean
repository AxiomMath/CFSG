module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreLieDefs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverUniqueOuter
public import CFSG.LieType.Chevalley.C2E6StdMatrixModel
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
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
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LocalAnalysis.ComponentClassification.CatalogSchreierCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesC
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.SporadicWitnesses
public import CFSG.Monster.B.TwoA.Base.FourNorm
public import CFSG.Monster.SteinbergMY443SimpleIsomorphism
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Co1.Module.Involutions
public import CFSG.Sporadic.Co1.Module.TwoBCertBase
public import CFSG.Sporadic.HeldB.OuterFixed
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.InvCentralizerBounds
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import Certificates.Certificate3085Base
public import Certificates.Certificate8026Base

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem card_outer_le_of_ker_eq {G C : Type*} [Group G] [Group C] [Finite C]
    (Θ : MulAut G →* C) (hker : Θ.ker = (MulAut.conj : G →* MulAut G).range) :
    Nat.card (Outer G) ≤ Nat.card C := by
  have e : Outer G ≃* Θ.range :=
    (QuotientGroup.quotientMulEquivOfEq
      (show OuterAutomorphisms.inner G = Θ.ker from hker.symm)).trans
      (QuotientGroup.quotientKerEquivRange Θ)
  rw [Nat.card_congr e.toEquiv]
  exact Subgroup.card_le_card_group _

theorem chevalleyExceptionalModel_of_lieModel {S : Type} [Group S] {t : StatedLieTag} {p f : ℕ}
    (ht : t ∉ classicalTags) (htr : t ∉ reeTitsTags) (hts : t ≠ .twistedB2)
    (hm : LieModel S t 0 p f) : ChevalleyExceptionalModel S t p f :=
  CFSG.Blueprint.LieModel.chevalleyExceptionalModel hm (by revert ht htr hts; cases t <;> decide)

theorem card_outer_stdGroup_le_six :
    Nat.card (Outer LieType.Chevalley.C2E6Std.stdGroup) ≤ 6 := by
  obtain ⟨Θ, hΘ⟩ := EvenSmallLie.TwoE6.exists_outer_hom
  have : Finite (RingAut LieType.Chevalley.C2E6Overlap.K) :=
    Nat.finite_of_card_ne_zero (by rw [EvenSmallLie.TwoE6.natCard_ringAut_K]; norm_num)
  have h1 : Nat.card Θ.ker ≤ 3 :=
    (Subgroup.card_le_of_le hΘ).trans EvenSmallLie.TwoE6.card_range_diagOut_le_three
  have h2 : Nat.card Θ.range ≤ 2 :=
    (Subgroup.card_le_card_group _).trans EvenSmallLie.TwoE6.natCard_ringAut_K.le
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup Θ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange Θ).toEquiv] at hc
  calc Nat.card (Outer LieType.Chevalley.C2E6Std.stdGroup)
      = Nat.card Θ.range * Nat.card Θ.ker := hc
    _ ≤ 2 * 3 := Nat.mul_le_mul h2 h1
    _ = 6 := rfl

theorem evenLieExceptionalOuterInput_holds :
    EvenLieExceptionalOuterInput := by
  intro S _ _ t n f ht hm
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ht
  rcases ht with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  ·
    obtain ⟨-, hu⟩ := chevalleyExceptionalModel_of_lieModel (by decide) (by decide) (by decide) hm
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hu
    obtain ⟨-, Θ, -, -, hker, -⟩ :=
      UnbalancedCatalog.even_G2_exact_automorphism_normal_form le_rfl K hK
    have hR := LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK
    have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hR.1]; norm_num)
    rw [Nat.card_congr (OuterAutomorphisms.equivalence e).toEquiv]
    exact (card_outer_le_of_ker_eq Θ hker).trans (by rw [hR.1]; norm_num)
  ·
    obtain ⟨-, hu⟩ := chevalleyExceptionalModel_of_lieModel (by decide) (by decide) (by decide) hm
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LieType.Chevalley.nonempty_mulEquiv_adjointGroup .F4 hu
    have : CharP K 2 :=
      LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        le_rfl hK
    obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ :=
      LieType.Chevalley.even_F4_exact_automorphism_normal_form le_rfl K hK
    rw [Nat.card_congr (OuterAutomorphisms.equivalence e).toEquiv]
    refine (card_outer_le_of_ker_eq Θ hker).trans ?_
    simp
  ·
    obtain ⟨e⟩ := LieType.Chevalley.C2E6Std.MatrixModel.nonempty_mulEquiv_stdGroup_of_lieModel hm
    rw [Nat.card_congr (OuterAutomorphisms.equivalence e).toEquiv]
    exact card_outer_stdGroup_le_six.trans (by norm_num)

end CFSG.ComponentClassification.Foote5
