module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.MElevenCentGen
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.MPairTables

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.Monster.Generated CFSG.AGLEmbedding.Norton
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.Gen11
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.ComponentClassification.OuterAutomorphisms

theorem sporPair_M_eleven
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) (hBM : SporadicBMData)
    (hG : (Nat.card Gmat).factorization 11 = 2)
    (hGen : Subgroup.closure (Set.range fun i : Fin gen11Gens.size => gw gen11Gens[i]) = ⊤)
    (hOne : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
      Nonempty (S ≃* NativeSporadic.Carrier .M) → Nat.card (Outer S) = 1)
    (hGm : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
      Nonempty (S ≃* NativeSporadic.Carrier .M) → Nonempty (S ≃* Gmat)) : SporPair .M 11 :=
  sporPair_M_of_centGen (by norm_num) (by norm_num) (by decide) hSpM hBr hBM hOne
    fun S _ _ _ e => by
      obtain ⟨φ⟩ := hGm S e
      exact (centGen_Gmat_eleven hG hGen).of_mulEquiv φ.symm

end CFSG.HardMathSupport.Dickson.I271
