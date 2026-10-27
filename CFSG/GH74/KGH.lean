module

public import CFSG.GH74.Conclusion
public import CFSG.GH74.SectionalRank
public import CFSG.Milestones.LR_rank_two_isomorphism_types
public import CFSG.Milestones.LR_nonabelian_simple_two_rank_lower_bound

public section

namespace CFSG.GH74

open Subgroup Blueprint Assembly.LowTwoRank

theorem even_card_of_nonabelian_simple {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) : Even (Nat.card X) := by
  by_contra hodd
  have hsolv : Group.IsSolvable X :=
    CFSG.Milestones.odd_order_solvable (Nat.not_even_iff_odd.mp hodd)
  obtain ⟨a, b, hab⟩ := hnonab
  exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hsolv a b)

theorem lieModel_of_statedClassicalModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ classicalTags) (h : StatedClassicalModel X t n p f) : LieModel X t n p f :=
  Or.inl ⟨ht, h⟩

theorem isSporadic_M11_of_mulEquiv_statedM11 {X : Type} [Group X]
    (e : X ≃* StatedM11) : NativeSporadic.IsSporadic X .M11 :=
  ⟨e.trans (MulEquiv.subgroupCongr
    CFSG.Semidihedral.GL2Recognition.lowTwoRankStatedM11_eq_nativeM11)⟩

theorem ghList_of_twoRank_eq_two
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hrank : Open.twoRank X = 2) : GHList X := by
  rcases CFSG.Milestones.lr_rank_two_isomorphism_types X hnonab hrank with
    ⟨p, f, hp, hp2, hf, h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | h | h | h
  · exact Or.inr (Or.inr ⟨p, f, hp, hf, Or.inl ⟨hp2,
      Or.inl (lieModel_of_statedClassicalModel (by decide) h)⟩⟩)
  · exact Or.inr (Or.inr ⟨p, f, hp, hf, Or.inl ⟨hp2,
      Or.inr (Or.inl (lieModel_of_statedClassicalModel (by decide) h))⟩⟩)
  · exact Or.inr (Or.inr ⟨p, f, hp, hf, Or.inl ⟨hp2,
      Or.inr (Or.inr (Or.inl (lieModel_of_statedClassicalModel (by decide) h)))⟩⟩)
  · exact Or.inr (Or.inr ⟨2, 2, Nat.prime_two, by norm_num, Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl
        (lieModel_of_statedClassicalModel (by decide) h))))⟩)))))⟩)
  · exact Or.inl ⟨7, le_rfl, by norm_num, h⟩
  · obtain ⟨e⟩ := h
    exact Or.inr (Or.inl (Or.inl (isSporadic_M11_of_mulEquiv_statedM11 e)))

theorem card_quotient_le {H : Type*} [Group H] [Finite H] (N : Subgroup H) [N.Normal] :
    Nat.card (H ⧸ N) ≤ Nat.card H := by
  rw [← N.card_mul_index, Subgroup.index] at *
  exact Nat.le_mul_of_pos_left _ Nat.card_pos

theorem kgh_of_smaller
    {G : Type} [Group G] [Finite G] (hgen : Gen4 G)
    (ih : ∀ (X : Type) [Group X] [Finite X], Nat.card X < Nat.card G → IsSimpleGroup X →
      (∃ a b : X, a * b ≠ b * a) → 3 ≤ Open.twoRank X → Gen4 X → GH74Conclusion X) :
    KGH G := by
  intro H hH N hN hsimple hnonab
  have hlt : Nat.card (H ⧸ N) < Nat.card G :=
    lt_of_le_of_lt (card_quotient_le N)
      ((Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hH)).trans_eq Subgroup.card_top)
  have hgen' : Gen4 (H ⧸ N) := (hgen.subgroup H).quotient N
  have heven := even_card_of_nonabelian_simple hnonab
  have h2 : 2 ≤ Open.twoRank (H ⧸ N) :=
    CFSG.Milestones.lr_nonabelian_simple_two_rank_lower_bound (H ⧸ N) hnonab heven
  rcases h2.eq_or_lt with h2 | h3
  · exact ghList_of_twoRank_eq_two hnonab h2.symm
  · exact (ih (H ⧸ N) hlt hsimple hnonab h3 hgen').ghList

end CFSG.GH74
