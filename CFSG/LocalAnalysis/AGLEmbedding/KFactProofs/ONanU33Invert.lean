module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaKFacts
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU33InvertModel

public section

namespace CFSG.AGLEmbedding

open CFSG.UnitaryThreeRecognition.Model (rootGroup)

theorem kFactU33SylowInvert : KFactU33SylowInvert := by
  intro K _ _ h T t ht _
  obtain ⟨d, ⟨q, hqp, -, hdq⟩, ⟨e⟩⟩ := h
  have hd : IsUnitaryIndex 3 d := ⟨q, hqp, hdq⟩
  obtain ⟨-, hf, -, K', _, _, J, hJ, hK, hfix, ⟨e0⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd ⟨e⟩)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_map_eq e0 T S
  have hT : (T : Subgroup K).map e'.toMonoidHom = rootGroup J hJ := he'.trans hS
  have hN : (Subgroup.normalizer ((T : Subgroup K) : Set K)).map e'.toMonoidHom =
      Subgroup.normalizer (rootGroup J hJ : Set _) := by
    rw [Subgroup.map_equiv_normalizer_eq, hT]
  obtain ⟨n, hn, hnt⟩ := UnitaryModel.exists_inverting_rootGroup J hJ hK hfix
    (t := e' t) (by rw [← hT]; exact ⟨t, ht, rfl⟩)
  refine ⟨e'.symm n, ?_, ?_⟩
  · rw [← hN] at hn
    exact (UnitaryModel.mem_map_iff e' _ _).1 (by simpa using hn)
  · apply e'.injective
    simpa using hnt

end CFSG.AGLEmbedding
