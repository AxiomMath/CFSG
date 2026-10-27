module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6A6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Mult
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.RankThree.PartOne.KF.ClsPOmegaMinus
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.ClassicalInvolution.Upgrade
  CFSG.Assembly.LowTwoRank

section Finite


variable {f : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
  {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [IsAlgClosed Ω] [CharP Ω 2]
  {Fr : Ω →+* Ω}

theorem finite_twE6JStar (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (hFr : ∀ c, Fr c = c ^ (2 ^ f)) {q : ℕ}
    (hq : q.Prime) (hqdvd : q ∣ 2 ^ f + 1) {ζ : Ωˣ}
    (i : KernelComponent (rootCharHom (twE6omega1Tuple ζ))) :
    Finite ↥(twE6JStar (Fr := Fr) (q := q) (ζ := ζ) i) := by
  haveI : Finite (twE6EnnolaSetup (Fr := Fr) hf hK hσ hFr hq hqdvd).Γ :=
    (twE6EnnolaSetup (Fr := Fr) hf hK hσ hFr hq hqdvd).finite_Γ
  have hle : twE6JStar (Fr := Fr) (q := q) (ζ := ζ) i ≤
      (twE6EnnolaSetup (Fr := Fr) hf hK hσ hFr hq hqdvd).Γ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.rationalComponent_le_Γ
      (twE6EnnolaSetup (Fr := Fr) hf hK hσ hFr hq hqdvd) i
  exact Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

end Finite

section Six


variable {f : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
  {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [IsAlgClosed Ω] [CharP Ω 2]
  {Fr : Ω →+* Ω}

theorem twE6_center_eq_bot_and_trivialMultiplierT (hf : 2 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (hFr : ∀ c, Fr c = c ^ (2 ^ f)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqdvd : q ∣ 2 ^ f + 1) {ζ : Ωˣ}
    (hζq : ζ ^ q = 1) (hζ1 : ζ ≠ 1)
    (i : KernelComponent (rootCharHom (twE6omega1Tuple ζ))) :
    Subgroup.center ↥(twE6JStar (Fr := Fr) (q := q) (ζ := ζ) i) = ⊥ ∧
      TrivialMultiplierT ↥(twE6JStar (Fr := Fr) (q := q) (ζ := ζ) i) := by
  haveI : Finite ↥(twE6JStar (Fr := Fr) (q := q) (ζ := ζ) i) :=
    finite_twE6JStar hf hK hσ hFr hq hqdvd i
  have hSM := twE6_dStrongModel_omega1 hf hK hσ hFr hq hq2 hqdvd hζq hζ1 i
  have hmM : CFSG.Models.LieModel
      (↥(twE6JStar (Fr := Fr) (q := q) (ζ := ζ) i) ⧸
        Subgroup.center ↥(twE6JStar (Fr := Fr) (q := q) (ζ := ζ) i)) .POmegaMinus 5 2 f :=
    CFSG.Models.LieModel.of_blueprint_of_ne_zero (by norm_num) hSM.1
  have h1 : Nat.card (CFSG.Blueprint.Multiplier.generic .POmegaMinus 5 2 f ×
      CFSG.Blueprint.Multiplier.exceptional .POmegaMinus 5 2 f) = 1 :=
    CFSG.RankThree.PartOne.KFU.card_multiplier_pOmegaMinus (n := 5) (f := f) (by omega) (by omega)
  exact center_eq_bot_and_trivialMultiplierT_of_quotient_center hSM.2.1.1.commutator_eq_top
    (trivialMultiplierT_of_lieModel
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds hmM h1)

end Six

end CFSG.LocalAnalysis.GLTheoremA.Y10F
