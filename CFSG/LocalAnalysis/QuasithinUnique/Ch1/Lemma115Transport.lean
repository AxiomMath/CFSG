module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique CFSG.SectionRank

variable {X Y : Type} [Group X] [Group Y]

theorem SQTKCharTwoLie.of_mulEquiv (e : X ≃* Y) (h : SQTKCharTwoLie Y) : SQTKCharTwoLie X := by
  rcases h with (⟨f, h⟩ | h) | ⟨n, hn, h⟩
  · refine Or.inl (Or.inl ⟨f, ?_⟩)
    rcases h with h | h | h | h | h | h | h | h
    · exact Or.inl ⟨h.1, statedClassicalModel_of_mulEquiv e h.2⟩
    · exact Or.inr (Or.inl ⟨h.1, statedClassicalModel_of_mulEquiv e h.2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h.1, statedClassicalModel_of_mulEquiv e h.2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, statedClassicalModel_of_mulEquiv e h.2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1,
        chevalleyExceptionalModel_of_mulEquiv e h.2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1,
        chevalleyExceptionalModel_of_mulEquiv e h.2⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, h.2.1,
        reeTitsModel_of_mulEquiv e h.2.2⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1, h.2.1,
        suzukiModel_of_mulEquiv e h.2.2⟩))))))
  · exact Or.inl (Or.inr (reeTitsModel_of_mulEquiv e h))
  · exact Or.inr ⟨n, hn, statedClassicalModel_of_mulEquiv e h⟩

theorem Lemma115LieCharTwo.of_mulEquiv (e : X ≃* Y) (h : Lemma115LieCharTwo Y) :
    Lemma115LieCharTwo X := by
  rcases h with h | h | h
  · exact Or.inl (SQTKCharTwoLie.of_mulEquiv e h)
  · obtain ⟨e'⟩ := h
    exact Or.inr (Or.inl ⟨e.trans e'⟩)
  · exact Or.inr (Or.inr (statedClassicalModel_of_mulEquiv e h))

theorem IsL34OrG24.of_mulEquiv (e : X ≃* Y) (h : IsL34OrG24 Y) : IsL34OrG24 X := by
  rcases h with h | h
  · exact Or.inl (statedClassicalModel_of_mulEquiv e h)
  · exact Or.inr (chevalleyExceptionalModel_of_mulEquiv e h)

@[expose] def Lemma115ModelE (X : Type) [Group X] : Prop :=
  StatedClassicalModel X .PSL 3 3 1 ∨
    ∃ p : ℕ, IsFermatOrMersennePrime p ∧ StatedClassicalModel X .PSL 2 p 1

theorem Lemma115ModelE.of_mulEquiv (e : X ≃* Y) (h : Lemma115ModelE Y) : Lemma115ModelE X := by
  rcases h with h | ⟨p, hp, h⟩
  · exact Or.inl (statedClassicalModel_of_mulEquiv e h)
  · exact Or.inr ⟨p, hp, statedClassicalModel_of_mulEquiv e h⟩

end CFSG.QuasithinUnique.Ch1
