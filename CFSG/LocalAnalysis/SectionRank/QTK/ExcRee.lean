module

public import CFSG.RankThree.Chevalley.SteinbergCFSmallReeCentralCover
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.RankThree.PartTwo.Census.Criteria

public section

namespace CFSG.SectionRank.QTK

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.PartTwo.Census


theorem three_le_localRank_of_smallReeModel {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : ReeTitsModel S .twistedG2 p f) : 3 ≤ localRank 3 S := by
  obtain ⟨-, -, hp, -, hiso⟩ := small_Ree_model_Schreier S p f h
  subst hp
  obtain ⟨⟨-, -, -, -, -, hf3⟩, a, hfa, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ReeTag.G2.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hiso a K hfa hK ⟨e⟩
  have : Finite (ReeTag.G2.reeGamma K a) := Finite.of_equiv S E.toEquiv
  have hK' : Nat.card K = 3 ^ (2 * a + 1) := by rw [hK, hfa]
  let ε : (⊤ : Subgroup (ReeTag.G2.reeGamma K a)) ≃* ReeTag.G2.reeGamma K a :=
    Subgroup.topEquiv
  have h := (CFSG.RankThree.Chevalley.small_Ree_actual_central_cover_two_local_three_rank
    (X := ReeTag.G2.reeGamma K a) ⊤ a K hK' ε.toMonoidHom ε.surjective (by
      rw [(MonoidHom.ker_eq_bot_iff _).2 ε.injective]
      exact bot_le)).2
  rw [localRank_eq_of_mulEquiv E Nat.prime_three]
  omega

end CFSG.SectionRank.QTK
