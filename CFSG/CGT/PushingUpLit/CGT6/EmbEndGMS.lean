module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndCfg

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Blueprint

section Statement

@[expose] def GMSVList (Q : Type) [Group Q] : Prop :=
  Nonempty (Q ≃* NativeSporadic.M12) ∨ Nonempty (Q ≃* NativeSporadic.J1) ∨
    Nonempty (Q ≃* NativeSporadic.J2) ∨ Nonempty (Q ≃* alternatingGroup (Fin 9)) ∨
    Nonempty (Q ≃* alternatingGroup (Fin 7)) ∨ LieModel Q .PSL 2 5 2 ∨ LieModel Q .PSL 3 5 1 ∨
    LieModel Q .PSU 3 5 1

end Statement

section Vocab

variable {Q Q' : Type} [Group Q] [Group Q']

theorem stated_psl_of_lieModel {n p f : ℕ} (hn : n ≠ 0) (h : LieModel Q .PSL n p f) :
    CFSG.Open.StatedClassicalModel Q .PSL n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero hn h

theorem stated_psu_of_lieModel {n p f : ℕ} (hn : n ≠ 0) (h : LieModel Q .PSU n p f) :
    CFSG.Open.StatedClassicalModel Q .PSU n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero hn h

theorem chevalley_g2_of_lieModel {p f : ℕ} (h : LieModel Q .G2 0 p f) :
    ChevalleyExceptionalModel Q .G2 p f :=
  CFSG.Blueprint.LieModel.chevalleyExceptionalModel h (by decide)

theorem stated_psl_congr (e : Q ≃* Q') {n p f : ℕ}
    (h : CFSG.Open.StatedClassicalModel Q .PSL n p f) :
    CFSG.Open.StatedClassicalModel Q' .PSL n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e h

theorem stated_psu_congr (e : Q ≃* Q') {n p f : ℕ}
    (h : CFSG.Open.StatedClassicalModel Q .PSU n p f) :
    CFSG.Open.StatedClassicalModel Q' .PSU n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e h

theorem chevalley_g2_congr (e : Q ≃* Q') {p f : ℕ} (h : ChevalleyExceptionalModel Q .G2 p f) :
    ChevalleyExceptionalModel Q' .G2 p f := by
  obtain ⟨hadm, hm⟩ := h
  refine ⟨hadm, ?_⟩
  obtain ⟨K, _, _, hK, ⟨e'⟩⟩ := hm
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e.symm.trans e'⟩⟩

theorem smallList_of_gmsVList (e : Q ≃* Q') (h : GMSVList Q) : SmallList Q' := by
  rcases h with ⟨⟨e'⟩⟩ | ⟨⟨e'⟩⟩ | ⟨⟨e'⟩⟩ | ⟨⟨e'⟩⟩ | ⟨⟨e'⟩⟩ | h | h | h
  · exact Or.inl ⟨e.symm.trans e'⟩
  · exact Or.inr (Or.inl ⟨e.symm.trans e'⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e.symm.trans e'⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.symm.trans e'⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.symm.trans e'⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (stated_psl_congr e (stated_psl_of_lieModel (by norm_num) h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (stated_psl_congr e (stated_psl_of_lieModel (by norm_num) h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (stated_psu_congr e (stated_psu_of_lieModel (by norm_num) h))))))))

end Vocab

end CFSG.CGT.PushingUpLit.CGT6
