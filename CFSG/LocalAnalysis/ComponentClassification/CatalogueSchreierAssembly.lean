module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternating
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherClassicalSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointSchreier
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LieType.Chevalley.ExceptionalChevalleyModelSchreier
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Ree.LargeReeModelSchreier

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueSchreierAssembly

open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open OuterAutomorphisms (Outer)

theorem classical_model_outer_solvable {S : Type} [Group S] {t : StatedLieTag} {n p f : ℕ}
    (h : StatedClassicalModel S t n p f) : Group.IsSolvable (Outer S) := by
  cases t with
  | PSL =>
    have hn : 2 ≤ n := h.1.2.2.1
    rcases Nat.lt_or_ge n 3 with hlt | hge
    · obtain rfl : n = 2 := by omega
      exact (LocalAnalysis.ComponentInitial.UnitaryHigher.linear_two_classical_model_schreier h).2
    · exact (LocalAnalysis.ComponentInitial.UnitaryHigher.linear_higher_classical_model_schreier
        hge h).2
  | PSU => exact (LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_classical_model_schreier h).2
  | PSp =>
    have hn : 2 ≤ n := h.1.2.2.1
    rcases Nat.lt_or_ge n 3 with hlt | hge
    · obtain rfl : n = 2 := by omega
      exact (CatalogueBSymplecticTwo.classical_model_two_schreier h).2
    · exact (LocalAnalysis.ComponentInitial.SymplecticHigher.classical_model_schreier hge h).2
  | POmegaOdd =>
    exact (CatalogueBOrthogonalPointSchreier.orthogonal_geometry_classical_model_Schreier _
      (.inl rfl) h).2.2
  | POmegaPlus =>
    exact (CatalogueBOrthogonalPointSchreier.orthogonal_geometry_classical_model_Schreier _
      (.inr (.inl rfl)) h).2.2
  | POmegaMinus =>
    exact (CatalogueBOrthogonalPointSchreier.orthogonal_geometry_classical_model_Schreier _
      (.inr (.inr rfl)) h).2.2
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
    exact h.2.elim

theorem exceptional_rep_outer_solvable {S : Type} [Group S]
    (hTits : ∀ p f : ℕ, ReeTitsModel S .Tits p f → Group.IsSolvable (Outer S))
    (h : ExceptionalRep S) : Group.IsSolvable (Outer S) := by
  rcases h with ⟨t, p, f, ht, hm⟩ | ⟨t, p, f, ht, hm⟩ | ⟨p, f, hm⟩
  · exact (LieType.Chevalley.exceptional_Chevalley_model_Schreier S t p f ht hm).1
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact (LieType.Ree.small_Ree_model_Schreier S p f hm).2.1
    · exact (LieType.Ree.ReeTag.large_Ree_model_Schreier S p f hm).2.2.1
    · exact hTits p f hm
  · exact (LocalAnalysis.ComponentInitial.Suzuki_model_Schreier S p f hm).2

theorem catalog_schreier_of_tits_sporadic {S : Type} [Group S]
    (hnonab : ∃ a b : S, a * b ≠ b * a)
    (hTits : ∀ p f : ℕ, ReeTitsModel S .Tits p f → Group.IsSolvable (Outer S))
    (hspor : NativeSporadic.SporadicRep S → Group.IsSolvable (Outer S))
    (hcat : Catalog S) : Group.IsSolvable (Outer S) := by
  rcases hcat with ⟨p, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, hm⟩ | hexc | hsp
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exact CatalogueSchreierAlternating.alternating_schreier_of_equiv n hn e
  · exact classical_model_outer_solvable hm
  · exact exceptional_rep_outer_solvable hTits hexc
  · exact hspor hsp

end CFSG.ComponentClassification.CatalogueSchreierAssembly
