module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SurvivorsAll
import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L2Survivor

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.AGLEmbedding CFSG.LocalAnalysis.ComponentInitial

theorem d2XSurvivorAt_altSix : D2XSurvivorAt (.alternating 6 (by norm_num)) fun p => p = 3 := by
  intro X _ _ p hp3 R A X₀ K hK hRA ⟨e⟩
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 2) = 9 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 3 2 (by norm_num)]
    norm_num
  obtain ⟨e'⟩ :=
    unique_field_nine_projective_linear_alternating_six_isomorphism (GaloisField 3 2) hcard
  have f : K ≃* PSL2GF 3 2 := e.trans e'.symm
  exact ⟨fun W hW hWn => hK.dichotomy_of_psl2 f hW hWn,
    fun x hx => hRA ▸ hK.centralizer_A_le_of_psl2 f hx.2⟩

end CFSG.AGLEmbeddingD2
