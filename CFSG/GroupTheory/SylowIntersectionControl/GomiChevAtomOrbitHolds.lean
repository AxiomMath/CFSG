module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevReduceQuotient
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevOrbitSwapAltSix
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevOrbitSwapU33
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevOrbitSwapTits
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParFamily
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevNodeOrbit
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParSuzuki
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6LargeRee
import CFSG.RankThree.PartOne.K133X.F4

public section

namespace CFSG.GroupTheory

open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

theorem gomiAtomsFixed_of_lie_suzuki {K : Type} [Group K]
    [Finite K] {d : TauCeti.ValidLieTypeIndex} {m : ℕ} (hd : d.1 = .suzuki m)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : GomiAtomsFixed K := by
  obtain ⟨dd, hv⟩ := d
  obtain rfl : dd = .suzuki m := hd
  exact gomiAtomsFixed_of_isCoatom_normalizer fun T hT => (MinPar.suzuki_cat m hv e hT).2.coatom

theorem gomiAtomsFixed_of_lie_reeF4
    {K : Type} [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex} {m : ℕ}
    (hd : d.1 = .reeF4 m) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : GomiAtomsFixed K := by
  obtain ⟨dd, hv⟩ := d
  obtain rfl : dd = .reeF4 m := hd
  obtain ⟨-, hmodel⟩ := CFSG.RankThree.PartOne.K133X.reeTitsModel_twistedF4_of_isoLie
    (X := K) (m := m) ⟨hv, ⟨e⟩⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hU⟩ := CFSG.ABGLocalTools.exists_isSylowOf (G := K) 2 ⊤
  have hU' := CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2 hU
  obtain ⟨P₁, P₂, hcov, -, -, -, h₁, h₂⟩ :=
    (CFSG.QuasithinUnique.Setup.X6.large_Ree_model_two_extensions hmodel).2.2.2 U hU'
  refine gomiAtomsFixed_of_covBy_relIndex_ne hU' hcov ?_
  rw [h₁, h₂]
  have hlt : 2 ^ (2 * m + 1) < 2 ^ (2 * (2 * m + 1)) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem gomiAtomOrbitTop_of_isChevTwo
    {K : Type} [Group K] [Finite K] [IsSimpleGroup K] (hnab : ∃ a b : K, a * b ≠ b * a)
    (h : AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsChevTwo K) : GomiAtomOrbitTop K := by
  rcases MinPar.hasBQ_or_residual h with hbq | hres
  · exact gomiAtomOrbitTop_of_hasBQ hnab hbq
  · rcases hres with he | ⟨d, ⟨q, hq, hd⟩, he⟩ | ⟨d, hd, he⟩
    · exact gomiAtomOrbitTop_of_mulEquiv_alternatingGroup_six he.some
    · exact (gomiAtomsFixed_of_lie_twistedA_three hq hd he.some).gomiAtomOrbitTop
    · rcases hd with ⟨m, hm⟩ | ⟨m, hm⟩ | hm
      · exact (gomiAtomsFixed_of_lie_suzuki hm he.some).gomiAtomOrbitTop
      · exact (gomiAtomsFixed_of_lie_reeF4 hm he.some).gomiAtomOrbitTop
      · exact (gomiAtomsFixed_of_lie_tits hm he.some).gomiAtomOrbitTop

theorem gomiChevAtomOrbit_holds :
    GomiChevAtomOrbit :=
  gomiChevAtomOrbit_of_top fun _ _ _ _ hnab h => gomiAtomOrbitTop_of_isChevTwo hnab h

end CFSG.GroupTheory
