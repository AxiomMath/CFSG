module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.MPairTables
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.M13Gmat

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.Monster.Generated CFSG.AGLEmbedding.Norton
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.Gen13
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.ComponentClassification.OuterAutomorphisms

theorem sporPair_M_thirteen_of_centGen
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) (hBM : SporadicBMData)
    (hOne : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
      Nonempty (S ≃* NativeSporadic.Carrier .M) → Nat.card (Outer S) = 1)
    (hCG : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
      Nonempty (S ≃* NativeSporadic.Carrier .M) → CentGen 13 S) : SporPair .M 13 :=
  sporPair_M_of_centGen (by norm_num) (by norm_num) (by decide) hSpM hBr hBM hOne hCG

theorem sporPair_M_thirteen
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) (hBM : SporadicBMData)
    (hG : (Nat.card Gmat).factorization 13 = 3)
    (hGenD : Subgroup.closure (Set.range fun i : Fin genD13Gens.size => gw genD13Gens[i]) = ⊤)
    (hGen13 : Subgroup.closure (Set.range fun i : Fin gen13Gens.size => gw gen13Gens[i]) = ⊤)
    (hOne : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
      Nonempty (S ≃* NativeSporadic.Carrier .M) → Nat.card (Outer S) = 1)
    (hGm : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
      Nonempty (S ≃* NativeSporadic.Carrier .M) → Nonempty (S ≃* Gmat)) : SporPair .M 13 :=
  sporPair_M_thirteen_of_centGen hSpM hBr hBM hOne fun S _ _ _ e => by
    obtain ⟨φ⟩ := hGm S e
    exact (M13.centGen_Gmat_thirteen hG hGenD hGen13).of_mulEquiv φ.symm

end CFSG.HardMathSupport.Dickson.I271
