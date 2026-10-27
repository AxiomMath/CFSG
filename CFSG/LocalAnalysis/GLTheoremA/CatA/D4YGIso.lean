module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YEEven
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XFIso
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldD4
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms
public import CFSG.Blueprint.LieModelAPI
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel
public import CFSG.HardMathSupport.Solomon.Coordinator.C25D44
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Two
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LargeExtraspecial.OfFStar
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.Models.Transport
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.RankThree.PartTwo.Census.Spin.Main
public import CFSG.RankThree.PartTwo.Sec4.Census.RankOmegaF4
public import Certificates.Certificate8171

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4Y

open scoped Matrix
open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.StandardType CFSG.StandardType.Triality

theorem matrixDerivedScalars_eq_bot_charTwo {K₀ : Type} [Field K₀] [CharP K₀ 2] {d : ℕ}
    (Q : QuadraticForm K₀ (Fin d → K₀)) (hQ : ∃ v, Q v ≠ 0) :
    matrixDerivedScalars Q = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨c, hc⟩ := (mem_matrixDerivedScalars_iff Q A).1 hA
  rw [Subgroup.mem_bot]
  obtain ⟨v, hv⟩ := hQ
  have hiso : (A : GL (Fin d) K₀) ∈ matrixIsometries Q := matrixDerived_le_isometries _ A.2
  have h1 := (mem_matrixIsometries_iff Q A).1 hiso v
  have h2 : (matrixLinearEquiv (A : GL (Fin d) K₀)) v = (c : K₀) • v := by
    rw [matrixLinearEquiv_apply, ← hc]
    ext i
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.mulVec_diagonal]
  rw [h2, QuadraticMap.map_smul] at h1
  have h3 : (c : K₀) * c = 1 := by
    have : ((c : K₀) * c - 1) * Q v = 0 := by
      rw [sub_mul, one_mul]
      simpa [smul_eq_mul] using sub_eq_zero.2 h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hv)
  have h2K : (2 : K₀) = 0 := CharP.cast_eq_zero K₀ 2
  have h4 : ((c : K₀) - 1) * ((c : K₀) - 1) = 0 := by
    linear_combination h3 - ((c : K₀) - 1) * h2K
  have h5 : (c : K₀) = 1 := sub_eq_zero.1 (mul_self_eq_zero.1 h4)
  apply Subtype.ext
  rw [← hc]
  have : c = 1 := Units.ext h5
  rw [this, map_one]
  rfl

theorem exists_om8_of_isD4pow2 {K : Type} [Group K] {n : ℕ} (hn : 2 ≤ n)
    (h : catalogIs K (isD4pow2 n)) :
    ∃ (K₀ : Type) (_ : Field K₀) (_ : Finite K₀) (_ : CharP K₀ 2), Nat.card K₀ = 2 ^ n ∧
      Nonempty (K ≃* Om8 K₀) := by
  obtain ⟨i, ⟨q, hv, hp2, hex, rfl⟩, ⟨e⟩⟩ := h
  have hm := CFSG.Models.lieModel_D 4 q hv e
  have hsc : StatedClassicalModel K .POmegaPlus 4 q.p q.exponent :=
    hm.statedClassicalModel (by decide)
  obtain ⟨-, K₀, _, _, hK₀, ⟨eK⟩⟩ := hsc
  have hK₀' : Nat.card K₀ = 2 ^ n := by rw [hK₀, hp2, hex]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K₀ := Fintype.ofFinite K₀
  haveI : CharP K₀ 2 := charP_of_card_eq_prime_pow (f := n)
    (by rw [← Nat.card_eq_fintype_card, hK₀'])
  have hS := matrixDerivedScalars_eq_bot_charTwo (coordinateQuadPlus 4 K₀)
    ⟨CFSG.RankThree.PartOne.KCOrthogonalSubfield.stdU K₀, by
      rw [CFSG.RankThree.PartOne.KCOrthogonalSubfield.coordinateQuadPlus_stdU]
      exact one_ne_zero⟩
  exact ⟨K₀, inferInstance, inferInstance, inferInstance, hK₀',
    ⟨(coordinatePlusWitnessEquiv K₀ eK).trans
      ((QuotientGroup.quotientMulEquivOfEq hS).trans QuotientGroup.quotientBot)⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.D4Y
