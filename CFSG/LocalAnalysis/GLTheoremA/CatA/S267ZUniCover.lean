module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniBlock
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverBase
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverClassical
import CFSG.HardMathSupport.Solomon.Coordinator.I19_10FiCover
import CFSG.Quasithin.Background.F6CatSLEps3Cover
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank
import CFSG.Quasithin.Background.F6CatRecogOut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem SG_eq_statedSU [Finite K] (h : UnitaryFieldData ℓ f K) : SG h = StatedSU 3 (ℓ ^ f) K := by
  have hK : Nat.card K = (ℓ ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  ext g
  have hc := (CFSG.LinearGroups.unitary_scalar_kernel h.prime hK (n := 3) (by norm_num)).1
  have hmem : g ∈ StatedSU 3 (ℓ ^ f) K ↔ ((g : Matrix (Fin 3) (Fin 3) K)).det = 1 ∧
      (((g : Matrix (Fin 3) (Fin 3) K)).map (· ^ ℓ ^ f))ᵀ * (g : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← SetLike.mem_coe, hc]
    rfl
  rw [hmem, mem_gramSU, Units.val_one, Matrix.mul_one]
  have hbar : ((g : Matrix (Fin 3) (Fin 3) K)).map h.bar =
      ((g : Matrix (Fin 3) (Fin 3) K)).map (· ^ ℓ ^ f) := by
    ext i j
    rfl
  rw [hbar]
  exact And.comm


theorem exists_mulEquiv_SG_of_cover {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : TauCeti.PrimePower}
    (hQ2 : Q.p ≠ 2) {M : Type} [Group M] [Finite M] (hM : CFSG.Open.IsQuasisimple M)
    (hO : GLAPPrimeCore p M = ⊥) (hZ : Subgroup.center M ≠ ⊥)
    (hcat : catalogIs (M ⧸ Subgroup.center M) (onLie (· = .twistedA 2 Q))) :
    p = 3 ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (h : UnitaryFieldData Q.p Q.exponent K),
      3 ∣ Q.p ^ Q.exponent + 1 ∧ Nonempty (M ≃* ↥(SG h)) := by
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  obtain ⟨i, hi, ⟨e₀⟩⟩ := hcat
  rcases i with _ | _ | ⟨⟨d, hv⟩⟩ | _
  · exact absurd hi id
  · exact absurd hi id
  swap
  · exact absurd hi id
  change d = .twistedA 2 Q at hi
  subst hi
  obtain ⟨-, K, _, _, hK, ⟨e₁⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 Q hv e₀
  have h : UnitaryFieldData Q.p Q.exponent K :=
    ⟨Q.prime_p, Q.exponent_pos, by rw [hK, ← pow_mul, mul_comm]⟩
  haveI : CharP K Q.p := h.charP
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hperf : Group.IsPerfect M := ⟨hM.1⟩
  have hZp : IsPGroup p (Subgroup.center M) :=
    CFSG.HardMathSupport.Solomon.Coordinator.isPGroup_center_of_pPrimeCore_eq_bot hp hO
  have hodd : Odd (Nat.card (Subgroup.center M)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hZp
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hq : (3, Q.p ^ Q.exponent) ≠ (3, 2) := fun he =>
    not_three_two_of_ne_two (f := Q.exponent) Q.prime_p hQ2 ⟨rfl, (Prod.ext_iff.1 he).2⟩
  obtain ⟨φ, hφ, hker, hmap⟩ := CFSG.QuasithinUnique.Ch1.exists_cover_map_of_odd_splitting hodd e₁
    fun E _ _ π hπ hC _ =>
      CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central hK
        Q.exponent_pos (n := 3) (le_refl 3) (by decide) hq hπ hC
  have hbij := CFSG.Quasithin.F6.bijective_of_scalar_cover_of_map_ne_bot hφ hker
    (CFSG.QuasithinUnique.Ch1.card_scalars_dvd_three (p := Q.p) (f := Q.exponent)
      (Or.inr ⟨hK, rfl⟩)) (by rw [hmap]; exact hZ)
  have hcardZ : Nat.card (Subgroup.center M) = Nat.gcd 3 (Q.p ^ Q.exponent + 1) := by
    rw [← hmap, Subgroup.card_map_of_injective hbij.1,
      (CFSG.LinearGroups.unitary_scalar_kernel Q.prime_p hK (n := 3) (by norm_num)).2.2]
  have hZ1 : Nat.card (Subgroup.center M) ≠ 1 := fun h1 =>
    hZ (Subgroup.eq_bot_of_card_eq _ h1)
  have hg3 : Nat.gcd 3 (Q.p ^ Q.exponent + 1) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_left 3 (Q.p ^ Q.exponent + 1)) with
      h1 | h3
    · exact absurd (hcardZ.trans h1) hZ1
    · exact h3
  have h3q : 3 ∣ Q.p ^ Q.exponent + 1 := hg3 ▸ Nat.gcd_dvd_right 3 _
  have hp3 : p = 3 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hZp
    rw [hcardZ, hg3] at hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      norm_num at hn
    have : p ∣ 3 := by
      rw [hn]
      exact dvd_pow_self p hn0
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this
  refine ⟨hp3, K, inferInstance, inferInstance, h, h3q, ⟨?_⟩⟩
  exact (MulEquiv.ofBijective φ hbij).symm.trans (MulEquiv.subgroupCongr (SG_eq_statedSU h).symm)

end CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

end
