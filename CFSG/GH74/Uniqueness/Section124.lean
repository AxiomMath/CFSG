module

public import CFSG.GH74.Uniqueness.Section124B

public section

namespace CFSG.GH74.Uniqueness

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.lemma124
    (S : ZDSetup X Z M) : Lemma124Stmt Z M := by
  intro c n i h u hu hu2
  obtain ⟨m, j, e, hm, hq, hB⟩ := A2.benderSub_cenHull S h hu hu2
  exact ⟨A2.not_centralizer_le S c hu hu2, A2.lemma124b S h hu hu2, ⟨m, j, e, hm, hq, hB⟩,
    A2.delta_conj S h hB, A2.centralizer_eq_mul S h hu hu2⟩

end CFSG.GH74.Uniqueness
