module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelOuterTwoPart
public import CFSG.LieType.Chevalley.OrdinaryExceptionalOuterTwoPart
public import CFSG.LieType.Ree.SuzukiReeOuterTwoPart

public section

namespace CFSG.ComponentClassification.CatalogueOuterTwoPart

open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def OuterTwoPartBound (T : Type) [Group T] : Prop :=
  4 ≤ ordProj[2] (Nat.card T) ∧ ordProj[2] (Nat.card (Outer T)) < ordProj[2] (Nat.card T)

theorem classical_model_outer_two_part_bound {T : Type} [Group T] {t : StatedLieTag} {n p f : ℕ}
    (h : StatedClassicalModel T t n p f) : OuterTwoPartBound T := by
  cases t with
  | PSL =>
    obtain ⟨-, h4, hlt, -⟩ :=
      LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound T n p f h
    exact ⟨h4, hlt⟩
  | PSU =>
    obtain ⟨-, -, -, h4, hlt⟩ :=
      LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound T n p f h
    exact ⟨h4, hlt⟩
  | PSp =>
    obtain ⟨-, -, h4, hlt, -⟩ :=
      LocalAnalysis.ComponentInitial.symplectic_model_outer_two_part_bound T n p f h
    exact ⟨h4, hlt⟩
  | POmegaOdd =>
    obtain ⟨h4, hlt, -⟩ := LocalAnalysis.ComponentInitial.orthogonal_model_outer_two_part_bound T _
      (.inl rfl) n p f h
    exact ⟨h4, hlt⟩
  | POmegaPlus =>
    obtain ⟨h4, hlt, -⟩ := LocalAnalysis.ComponentInitial.orthogonal_model_outer_two_part_bound T _
      (.inr (.inl rfl)) n p f h
    exact ⟨h4, hlt⟩
  | POmegaMinus =>
    obtain ⟨h4, hlt, -⟩ := LocalAnalysis.ComponentInitial.orthogonal_model_outer_two_part_bound T _
      (.inr (.inr rfl)) n p f h
    exact ⟨h4, hlt⟩
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
    exact h.2.elim

theorem exceptional_rep_outer_two_part_bound {T : Type} [Group T]
    (hTits : ∀ p f : ℕ, ReeTitsModel T .Tits p f → OuterTwoPartBound T)
    (h : ExceptionalRep T) : OuterTwoPartBound T := by
  rcases h with ⟨t, p, f, ht, hm⟩ | ⟨t, p, f, ht, hm⟩ | ⟨p, f, hm⟩
  · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨-, h4, hlt, -⟩ :=
        LieType.Chevalley.ordinary_exceptional_model_outer_two_part_bound T _ p f (.inl rfl) hm
      exact ⟨h4, hlt⟩
    · obtain ⟨-, h4, hlt, -⟩ := LieType.Chevalley.ordinary_exceptional_model_outer_two_part_bound
        T _ p f (.inr (.inl rfl)) hm
      exact ⟨h4, hlt⟩
    · obtain ⟨-, h4, hlt, -⟩ := LieType.Chevalley.ordinary_exceptional_model_outer_two_part_bound
        T _ p f (.inr (.inr (.inl rfl))) hm
      exact ⟨h4, hlt⟩
    · obtain ⟨-, h4, hlt, -⟩ := LieType.Chevalley.ordinary_exceptional_model_outer_two_part_bound
        T _ p f (.inr (.inr (.inr (.inl rfl)))) hm
      exact ⟨h4, hlt⟩
    · obtain ⟨-, h4, hlt, -⟩ := LieType.Chevalley.ordinary_exceptional_model_outer_two_part_bound
        T _ p f (.inr (.inr (.inr (.inr rfl)))) hm
      exact ⟨h4, hlt⟩
    · obtain ⟨-, -, -, -, h4, hlt⟩ :=
        LieType.Chevalley.graph_twisted_exceptional_model_outer_two_part_bound T _ p f 2 hm
          (.inl ⟨rfl, rfl⟩)
      exact ⟨h4, hlt⟩
    · obtain ⟨-, -, -, -, h4, hlt⟩ :=
        LieType.Chevalley.graph_twisted_exceptional_model_outer_two_part_bound T _ p f 3 hm
          (.inr ⟨rfl, rfl⟩)
      exact ⟨h4, hlt⟩
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · obtain ⟨-, -, -, h4, hlt⟩ :=
        (LieType.Ree.suzuki_ree_model_outer_two_part_bound T p f).2.2 hm
      exact ⟨h4, hlt⟩
    · obtain ⟨-, -, -, h4, hlt⟩ :=
        (LieType.Ree.suzuki_ree_model_outer_two_part_bound T p f).2.1 hm
      exact ⟨h4, hlt⟩
    · exact hTits p f hm
  · obtain ⟨-, -, h4, hlt⟩ := (LieType.Ree.suzuki_ree_model_outer_two_part_bound T p f).1 hm
    exact ⟨h4, hlt⟩

theorem catalog_simple_outer_two_part_bound_of_tits_sporadic {T : Type} [Group T]
    (hnonab : ∃ a b : T, a * b ≠ b * a)
    (hTits : ∀ p f : ℕ, ReeTitsModel T .Tits p f → OuterTwoPartBound T)
    (hspor : NativeSporadic.SporadicRep T → OuterTwoPartBound T)
    (hcat : Catalog T) : OuterTwoPartBound T := by
  rcases hcat with ⟨p, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, hm⟩ | hexc | hsp
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · obtain ⟨hlt, h4⟩ :=
      LocalAnalysis.ComponentInitial.alternating_simple_outer_two_part_bound hn e
    exact ⟨h4, hlt⟩
  · exact classical_model_outer_two_part_bound hm
  · exact exceptional_rep_outer_two_part_bound hTits hexc
  · exact hspor hsp

end CFSG.ComponentClassification.CatalogueOuterTwoPart
