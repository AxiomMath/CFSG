module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOneLieSylowCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAut

public section

namespace CFSG.AGLEmbedding.KFactProofs.OneLieSylow

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model

theorem card_sylow_unitary {L : Type} [Group L] [Finite L] {p : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (hd : IsUnitaryIndex p d) (h : Nonempty (L ≃* CatGroup d)) (U : Sylow p L) :
    Nat.card (U : Subgroup L) = (p ^ d.1.fieldExponent) ^ 3 ∧
      Nat.card (Sylow p L) = (p ^ d.1.fieldExponent) ^ 3 + 1 := by
  obtain ⟨hp, hf, hq, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd h)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_map_eq e U S
  have hU : (U : Subgroup L).map e'.toMonoidHom = rootGroup J hJ := he'.trans hS
  have h2 := isMultiplyPretransitive_two J hJ (p ^ d.1.fieldExponent) hK hfix
  have : MulAction.IsPretransitive (ProjectiveSpecialUnitaryMatrixGroup J) (IsoPoint J) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  refine ⟨?_, ?_⟩
  · rw [card_eq_of_map_eq e' hU, UnitaryModel.card_rootGroup_eq J hJ hK hfix, ← pow_mul,
      mul_comm]
  · rw [card_sylow_eq_index e' U hU,
      UnitaryModel.normalizer_rootGroup_eq_stabilizer J hJ hK hfix hq,
      MulAction.index_stabilizer_of_transitive,
      card_isoPoint J hJ (p ^ d.1.fieldExponent) hK hfix]

end CFSG.AGLEmbedding.KFactProofs.OneLieSylow
