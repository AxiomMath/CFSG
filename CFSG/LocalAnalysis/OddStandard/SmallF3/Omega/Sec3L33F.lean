module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Lemma33F : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    ∀ X : Subgroup G, InCStar X → InF X →
      ∀ S : Sylow 2 (centralizer (X : Set G)), IsCyclic (S : Subgroup (centralizer (X : Set G)))

theorem asc82Lemma33F_of_lemma33 (h : Asc82Lemma33) : Asc82Lemma33F :=
  fun G _ _ t L hS X hX hXF S => h G t L hS X hX (Or.inl hXF) S

end CFSG.OddStandard.SmallF3.Omega
