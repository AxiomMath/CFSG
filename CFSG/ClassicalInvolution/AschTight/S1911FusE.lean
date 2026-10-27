module

public import Mathlib
public import CFSG.ClassicalInvolution.AschTight.S1911FusD
public import CFSG.ClassicalInvolution.ModelFacts.LinearAutFrame
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
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.AschTight.S1911C8c
public import CFSG.ClassicalInvolution.AschTight.S1911Case2a
public import CFSG.ClassicalInvolution.AschTight.S1911E2c
public import CFSG.ClassicalInvolution.AschTight.S1911Facts
public import CFSG.ClassicalInvolution.AschTight.Sec19Targets3
public import CFSG.ClassicalInvolution.AschTight.Thm6Tight3
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Outer
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers CFSG.GorensteinWalter
open scoped MatrixGroups

theorem five_le_pow_of_ne_nine {p e₀ : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he₀ : 0 < e₀)
    (h9 : p ^ (2 * e₀) ≠ 9) : 5 ≤ p ^ e₀ := by
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hm3 : 3 ≤ p ^ e₀ := hp3.trans (Nat.le_self_pow he₀.ne' p)
  have hodd : Odd (p ^ e₀) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  by_contra h
  have h34 : p ^ e₀ = 3 ∨ p ^ e₀ = 4 := by omega
  rcases h34 with h3 | h4
  · apply h9
    rw [pow_mul', h3]
    norm_num
  · rw [h4] at hodd
    exact absurd hodd (by decide)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

theorem exists_quotEquiv_perfectCore_of_mem_centralizer (hF0 : FactF0)
    (hd : Sec19Data p f K z S W) (h9 : p ^ f ≠ 9) {a : G}
    (haz : a ∈ Subgroup.centralizer ({z} : Set G)) (ha2 : a * a = 1)
    (haX : a ∉ sec19X K z ⊔ centralizerModOdd ⊤ K) :
    ∃ e₀ : ℕ, f = 2 * e₀ ∧ 5 ≤ p ^ e₀ ∧
      Nonempty (↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) ⧸
        classicalInvolutionOddCore ↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)))
          ≃* SL(2, GaloisField p e₀)) := by
  have hNC := normalizer_eq_centralizer_of_tight hd.tight.toTightBranch
  have haN : a ∈ Subgroup.normalizer (K : Set G) := hNC ▸ haz
  obtain ⟨⟨e⟩, hFcard, hF, h3⟩ := Hall196.exists_data_of_tightBranchD hd.tight
  obtain ⟨e₀, rfl⟩ := two_dvd_of_not_mem hd e hFcard hF h3 ⟨a, haN⟩ ha2 haX
  have hp2 : p ≠ 2 := hd.tight.branch.odd
  have he₀ : 0 < e₀ := by
    rcases Nat.eq_zero_or_pos e₀ with h | h
    · subst h
      rw [hFcard] at h3
      simp at h3
    · exact h
  have h5 := five_le_pow_of_ne_nine hp2 he₀ h9
  refine ⟨e₀, rfl, h5, ?_⟩
  obtain ⟨hσ1, hσ2⟩ := fieldPart_of_not_mem hd e hFcard hF h3 ⟨a, haN⟩ ha2 haX
  obtain ⟨g, hg⟩ := exists_semilinHom_of_mem e hFcard hF h3 ⟨a, haN⟩
  have hinv : ∀ b, semilinHom g (normalizerToPGammaL2Mod e hFcard hF h3 ⟨a, haN⟩).right
      (semilinHom g (normalizerToPGammaL2Mod e hFcard hF h3 ⟨a, haN⟩).right b) = b := by
    intro b
    rw [← hg, ← hg]
    exact slAut_slAut_of_mul_self e ⟨a, haN⟩ ha2 b
  obtain ⟨φ⟩ := hF0 p e₀ hp2 he₀ _ hσ1 hσ2 g hinv
  have hfix : slFix e ⟨a, haN⟩ = MonoidHom.eqLocus
      (semilinHom g (normalizerToPGammaL2Mod e hFcard hF h3 ⟨a, haN⟩).right)
      (MonoidHom.id SL(2, GaloisField p (2 * e₀))) := by
    ext b
    change slAut K e ⟨a, haN⟩ b = b ↔ _ = b
    rw [hg]
  let φ' : ↥(slFix e ⟨a, haN⟩) ≃* SL(2, GaloisField p e₀) := (MulEquiv.subgroupCongr hfix).trans φ
  have hcardm : Nat.card (GaloisField p e₀) = p ^ e₀ := GaloisField.card p e₀ he₀.ne'
  have : Fintype (GaloisField p e₀) := Fintype.ofFinite _
  have h4 : ∃ s : Finset (GaloisField p e₀), s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (GaloisField p e₀))) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcardm]; omega)
    exact ⟨s, hs⟩
  have : Group.IsPerfect SL(2, GaloisField p e₀) :=
    CFSG.LinearGroups.special_linear_isPerfect (K := GaloisField p e₀) (n := 2) le_rfl (Or.inr h4)
  have hperf : Group.IsPerfect ↥(slFix e ⟨a, haN⟩) :=
    Group.IsPerfect.ofSurjective (f := φ'.symm.toMonoidHom) φ'.symm.surjective
  have h2ne : (2 : GaloisField p e₀) ≠ 0 :=
    Ring.two_ne_zero (by rw [ringChar.eq (GaloisField p e₀) p]; exact hp2)
  have hO : classicalInvolutionOddCore ↥(slFix e ⟨a, haN⟩) = ⊥ := by
    have h1 : (classicalInvolutionOddCore SL(2, GaloisField p e₀)).map φ'.symm.toMonoidHom =
        classicalInvolutionOddCore ↥(slFix e ⟨a, haN⟩) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant φ'.symm
    rw [ModelFacts.LinearAut.oddCore_sl2_eq_bot h2ne (by rw [hcardm]; omega),
      Subgroup.map_bot] at h1
    exact h1.symm
  obtain ⟨ψ⟩ := nonempty_quotEquiv_perfectResidualOf e haN ha2 hperf hO
  exact ⟨ψ.trans φ'⟩

theorem exists_quotEquiv_perfectCore (hF0 : FactF0) (hd : Sec19Data p f K z S W)
    (h9 : p ^ f ≠ 9) {a : G} (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1)
    (haX : a ∉ sec19X K z ⊔ centralizerModOdd ⊤ K) :
    ∃ e₀ : ℕ, f = 2 * e₀ ∧ 5 ≤ p ^ e₀ ∧
      Nonempty (↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) ⧸
        classicalInvolutionOddCore ↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)))
          ≃* SL(2, GaloisField p e₀)) :=
  exists_quotEquiv_perfectCore_of_mem_centralizer hF0 hd h9 (hd.hSz haS) ha2 haX

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
