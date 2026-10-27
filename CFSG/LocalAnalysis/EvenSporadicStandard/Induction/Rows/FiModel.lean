module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiCoverLocal
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Transport

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

section StdBare

variable {A B : Type} [Group A] [Group B]

theorem fiCentralizer_map_mulEquiv (e : A ≃* B) (K : Subgroup A) :
    centralizer ((K.map e.toMonoidHom : Subgroup B) : Set B) =
      (centralizer (K : Set A)).map e.toMonoidHom :=
  centralizer_map_mulEquiv e K

theorem fiStdBare_map_mulEquiv (e : A ≃* B) {K : Subgroup A} (h : StdBare K) :
    StdBare (K.map e.toMonoidHom) :=
  stdBare_map_mulEquiv e h

end StdBare

section Model

variable {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]

omit [Finite X] [Finite Y] in
theorem centralizer_singleton_map_mulEquiv (e : X ≃* Y) (t : X) :
    centralizer ({e t} : Set Y) = (centralizer ({t} : Set X)).map e.toMonoidHom := by
  ext y
  rw [Subgroup.mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply e.injective
    simpa using h
  · intro h
    have := congrArg e h
    simpa using this

theorem CentralizerModel.of_mulEquiv (e : X ≃* Y) {tX : X} (h : CentralizerModel X tX) :
    CentralizerModel Y (e tX) := by
  have hc := centralizer_singleton_map_mulEquiv e tX
  refine ⟨?_, ?_, ?_, ?_, ?_, OutTwo.of_mulEquiv e h.outTwo⟩
  · obtain ⟨S, d, hSq⟩ := h.squareFacts
    refine ⟨S.map e.toMonoidHom, e d, ?_⟩
    have := hSq.map e.toMonoidHom e.injective
    rw [← hc] at this
    exact this
  · rw [hc]
    exact (e.mapSubgroup.isCoatom_iff _).2 h.coatom
  · have h1 := h.twoAdic_lt
    rw [hc]
    unfold twoAdic at h1 ⊢
    rw [Subgroup.card_top] at h1
    rw [Subgroup.card_map_of_injective e.injective, Subgroup.card_top,
      ← Nat.card_congr e.toEquiv]
    exact h1
  · rw [hc]
    exact fiStdBare_map_mulEquiv e h.stdBare
  · have h1 := h.card_centralizer
    have h2 := fiCentralizer_map_mulEquiv e (centralizer ({tX} : Set X))
    rw [hc, h2, Subgroup.card_map_of_injective e.injective]
    exact h1

end Model

end CFSG.EvenSporadicStandard.Induction
