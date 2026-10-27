module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Transport

public section

namespace CFSG.AGLEmbedding.KFactProofs.M12Cover

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

variable {G G' : Type} [Group G] [Group G']

@[expose] def KHyp (B X : Subgroup G) : Prop :=
  CFSG.Assembly.IsElemAbelian 3 B ∧ Nat.card B = 9 ∧
    Nonempty (autIn ⊤ B ≃* Equiv.Perm (Fin 3)) ∧ Group.IsPerfect ↥X ∧ X ≠ ⊥ ∧
    B ≤ Subgroup.normalizer (X : Set G)

theorem KHyp.map (φ : G ≃* G') {B X : Subgroup G} (h : KHyp B X) :
    KHyp (B.map φ.toMonoidHom) (X.map φ.toMonoidHom) := by
  obtain ⟨⟨hcomm, hexp⟩, hcard, ⟨e⟩, hperf, hX, hN⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_, ⟨(Sporadic.autInTopCongr φ B).symm.trans e⟩, ?_, ?_, ?_⟩
  · have := hcomm
    rw [isMulCommutative_iff]
    rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
    refine Subtype.ext ?_
    change φ x * φ y = φ y * φ x
    rw [← map_mul, ← map_mul]
    exact congrArg φ (setLike_mul_comm hx hy)
  · rintro _ ⟨x, hx, rfl⟩
    change φ x ^ 3 = 1
    rw [← map_pow, hexp x hx, map_one]
  · rw [Subgroup.card_map_of_injective φ.injective, hcard]
  · have := hperf
    exact Group.IsPerfect.map φ.toMonoidHom
  · exact fun h => hX ((Subgroup.map_eq_bot_iff_of_injective X
      (show Function.Injective φ.toMonoidHom from φ.injective)).1 h)
  · rw [← Subgroup.map_equiv_normalizer_eq X φ]
    exact fun _ ⟨b, hb, hbe⟩ => ⟨b, hN hb, hbe⟩

theorem eq_top_of_map_eq_top (φ : G ≃* G') {X : Subgroup G}
    (h : X.map φ.toMonoidHom = ⊤) : X = ⊤ := by
  rw [← Subgroup.comap_map_eq_self_of_injective
    (show Function.Injective φ.toMonoidHom from φ.injective) X, h, Subgroup.comap_top]

end CFSG.AGLEmbedding.KFactProofs.M12Cover
