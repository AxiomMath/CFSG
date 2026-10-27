module

public import CFSG.Fischer.Classification.Basic.Transitivity
public import CFSG.Fischer.Classification.SRG.Conference
public import CFSG.Fischer.Classification.Skeleton

public section

open CFSG.Blueprint.Fischer CFSG.Fischer SimpleGraph

namespace CFSG.Fischer.Classification

variable {X : Type} [Group X] {E : Set X}

namespace SRG

theorem card_eq_ncard_image_val {α : Type*} {E : Set α} (S : Set E) [Fintype S] :
    Fintype.card S = (Subtype.val '' S).ncard := by
  rw [Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq,
    Nat.card_eq_fintype_card]

theorem image_commonNeighbors (a b : E) :
    Subtype.val '' (commGraph E).commonNeighbors a b = LocalClass E a ∩ LocalClass E b := by
  rw [commonNeighbors, Set.image_inter Subtype.val_injective, image_neighborSet,
    image_neighborSet]

end SRG

open SRG

theorem Pair.isSRGWith_commGraph (hH : Hyp X E) (hna : NonabelianCommutator X) [Fintype E]
    [DecidableRel (commGraph E).Adj] {d e x : X} (hd : d ∈ E) (he : e ∈ LocalClass E d)
    (hx : x ∈ E) (hxd : x * d ≠ d * x) :
    (commGraph E).IsSRGWith E.ncard (LocalClass E d).ncard
      (LocalClass E d ∩ LocalClass E e).ncard (muSet E d x).ncard where
  card := by rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  regular a := by
    rw [← card_neighborSet_eq_degree, card_eq_ncard_image_val, image_neighborSet,
      Pair.ncard_localClass_eq hH.pair a.2 hd]
  of_adj a b hab := by
    obtain ⟨g, hga, hgb⟩ := Pair.exists_conj_pair_of_commute hH.pair hH.center hH.simple a.2 b.2
      hd he.1 (commGraph_adj_iff.1 hab).1 (commGraph_adj_iff.1 hab).2 he.2.1.symm he.2.2.symm
    rw [card_eq_ncard_image_val, image_commonNeighbors,
      ← Set.ncard_image_of_injective _ (conj_injective g), Set.image_inter (conj_injective g),
      Pair.image_conj_localClass hH.pair, Pair.image_conj_localClass hH.pair, hga, hgb]
  of_not_adj a b hab hnadj := by
    have hc : (a : X) * b ≠ b * a := fun h => hnadj ⟨hab, h⟩
    obtain ⟨g, hga, hgb⟩ := Pair.exists_conj_pair_of_not_commute hH.pair hH.center hH.simple hna
      a.2 b.2 hd hx hc fun h => hxd h.symm
    rw [card_eq_ncard_image_val, image_commonNeighbors, ← muSet,
      ← Set.ncard_image_of_injective _ (conj_injective g), Pair.image_conj_muSet hH.pair, hga, hgb]

theorem Pair.even_and_conference_of_not_isSquare (hH : Hyp X E) (hna : NonabelianCommutator X)
    {d e x : X} {k ℓ μ : ℕ} (hd : d ∈ E) (he : e ∈ LocalClass E d) (hx : x ∈ E)
    (hxd : x * d ≠ d * x) (hk : (LocalClass E d).ncard = k)
    (hℓ : (LocalClass E d ∩ LocalClass E e).ncard = ℓ) (hμ : (muSet E d x).ncard = μ)
    (hsq : ¬ IsSquare (((ℓ : ℤ) - μ) ^ 2 + 4 * ((k : ℤ) - μ))) :
    Even (E.ncard - 1) ∧ 2 * (k : ℤ) + ((E.ncard : ℤ) - 1) * ((ℓ : ℤ) - μ) = 0 := by
  classical
  have := Pair.finite hH.pair
  have : Fintype E := Fintype.ofFinite E
  subst hk hℓ hμ
  exact (Pair.isSRGWith_commGraph hH hna hd he hx hxd).conference_of_not_isSquare
    ((Set.ncard_pos (Set.toFinite E)).2 ⟨d, hd⟩) hsq

theorem Pair.exists_multiplicities_of_roots (hH : Hyp X E) (hna : NonabelianCommutator X)
    {d e x : X} {k ℓ μ : ℕ} (hd : d ∈ E) (he : e ∈ LocalClass E d) (hx : x ∈ E)
    (hxd : x * d ≠ d * x) (hk : (LocalClass E d).ncard = k)
    (hℓ : (LocalClass E d ∩ LocalClass E e).ncard = ℓ) (hμ : (muSet E d x).ncard = μ)
    {r s : ℤ} (hrs : r ≠ s) (hsum : r + s = (ℓ : ℤ) - μ) (hprod : r * s = (μ : ℤ) - k) :
    ∃ f g : ℕ, f + g = E.ncard - 1 ∧ (k : ℤ) + f * r + g * s = 0 := by
  classical
  have := Pair.finite hH.pair
  have : Fintype E := Fintype.ofFinite E
  subst hk hℓ hμ
  exact (Pair.isSRGWith_commGraph hH hna hd he hx hxd).exists_multiplicities_of_roots
    ((Set.ncard_pos (Set.toFinite E)).2 ⟨d, hd⟩) hrs hsum hprod

end CFSG.Fischer.Classification
