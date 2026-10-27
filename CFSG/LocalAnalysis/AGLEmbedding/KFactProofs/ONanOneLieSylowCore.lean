module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbedding.KFactProofs.OneLieSylow

theorem card_sylow_eq_index {L G : Type*} [Group L] [Finite L] [Group G] {p : ℕ} [Fact p.Prime]
    (e : L ≃* G) (U : Sylow p L) {P : Subgroup G} (hUP : (U : Subgroup L).map e.toMonoidHom = P) :
    Nat.card (Sylow p L) = (Subgroup.normalizer (P : Set G)).index := by
  have h1 : (Subgroup.normalizer ((U : Subgroup L) : Set L)).map e.toMonoidHom =
      Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.map_equiv_normalizer_eq, hUP]
  rw [U.card_eq_index_normalizer, ← h1]
  exact (Subgroup.index_map_equiv _ e).symm

theorem card_eq_of_map_eq {L G : Type*} [Group L] [Group G] (e : L ≃* G) {U : Subgroup L}
    {P : Subgroup G} (hUP : U.map e.toMonoidHom = P) : Nat.card U = Nat.card P := by
  rw [← hUP]
  exact (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).symm

end CFSG.AGLEmbedding.KFactProofs.OneLieSylow
