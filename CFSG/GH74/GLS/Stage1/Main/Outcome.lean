module

public import CFSG.GH74.GLS.Stage1.Main.Basic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Statements
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Statements
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Rank3

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage1.Thm3.Sec8

variable {G : Type} [Group G] [Finite G]

theorem thm3_outcome (hthm2 : S_stage1_thm2_Std) (h61 : Prop6_1) (h71 : Prop7_1) (h81 : Prop8_1)
    (hStd : Std0 G) (hx : ∃ (x : G) (K : Subgroup G), IsTwoTerminal x K ∧ pRank 2 ↥K = 1) :
    ∃ (z : G) (S : Subgroup G), Cen2 G z S ∧ ZCen z S ∧
      (∀ K : Subgroup G, IsRigidRankOneComp z K → Cond6a S K) ∧ RigidData G z S ∧ TermCtx G z S := by
  obtain ⟨z, hcl, t, htC, htz, htn⟩ := hthm2 G hStd hx
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf (p := 2) (centralizer ({z} : Set G))
  have hthm : ∃ t ∈ centralizer ({z} : Set G), IsConj z t ∧ t ∉ zStar (rigidProduct z) :=
    ⟨t, htC, htz, htn⟩
  have h6 : Std6 G z S := ⟨hStd.kps, hStd.rank.1, hStd.rank.2, hStd.gen4, hcl, hthm, hS, hStd.kgh⟩
  have hc := (hcl.2 t htC htz htn).1
  have hcen : Cen2 G z S := Cen2.of_classical hStd hcl hthm hS
  have hc6 := h61 G z S h6
  refine ⟨z, S, hcen, zcen_of_classical hcl hthm hS, hc6.1, ?_⟩
  rcases hc with h1 | h2
  · obtain ⟨K, hK⟩ := Set.ncard_eq_one.1 h1
    exact ⟨Or.inr ⟨K, ⟨h6, hK⟩, hc6.2.2.1 K hK⟩, Or.inl (G2Term.of_G2Concl (hc6.2.2.1 K hK))⟩
  · obtain ⟨K₁, K₂, hne, hset⟩ := Set.ncard_eq_two.1 h2
    have h4 : Std4 G z S K₁ K₂ := ⟨hStd.kps, hStd.rank.1, hStd.rank.2, hStd.gen4, hcl, hthm, hS, hset, hne, hStd.kgh⟩
    refine ⟨Or.inl ⟨K₁, K₂, h4⟩, ?_⟩
    by_cases hf : ∃ u ∈ Pz S z, IsConj z u ∧ u ≠ z
    · rcases h81 G z S K₁ K₂ h4 hf with hg | hl
      · exact Or.inl (G2Term.of_G2TermType hg)
      · exact Or.inr (Or.inr (L4U4TermType.exists_eps hl))
    · have hnf : ∀ u ∈ Pz S z, IsConj z u → u = z := by
        intro u hu hz
        by_contra hne
        exact hf ⟨u, hu, hz, hne⟩
      obtain ⟨q, w, hq, hq5, h₁, h₂, ht7⟩ := h71 G z S K₁ K₂ h4 hnf
      exact Or.inr (Or.inl ⟨q, w, K₁, K₂, h4, hq, hq5, h₁, h₂, ht7⟩)

theorem thm3_outcome_three (hthm2 : S_stage1_thm2_Std) (h61 : Prop6_1) (h71 : Prop7_1)
    (h81r : Prop8_1Rank3) (hStd : Std0 G) (hrank : pRank 2 G = 3)
    (hx : ∃ (x : G) (K : Subgroup G), IsTwoTerminal x K ∧ pRank 2 ↥K = 1) :
    ∃ (z : G) (S : Subgroup G), Cen2 G z S ∧ ZCen z S ∧
      (∀ K : Subgroup G, IsRigidRankOneComp z K → Cond6a S K) ∧ RigidData G z S ∧
      (G2Term G z S ∨ ∃ (q : ℕ) (w : G), Term7Out G z S q w) := by
  obtain ⟨z, hcl, t, htC, htz, htn⟩ := hthm2 G hStd hx
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf (p := 2) (centralizer ({z} : Set G))
  have hthm : ∃ t ∈ centralizer ({z} : Set G), IsConj z t ∧ t ∉ zStar (rigidProduct z) :=
    ⟨t, htC, htz, htn⟩
  have h6 : Std6 G z S := ⟨hStd.kps, hStd.rank.1, hStd.rank.2, hStd.gen4, hcl, hthm, hS, hStd.kgh⟩
  have hc := (hcl.2 t htC htz htn).1
  have hcen : Cen2 G z S := Cen2.of_classical hStd hcl hthm hS
  have hc6 := h61 G z S h6
  refine ⟨z, S, hcen, zcen_of_classical hcl hthm hS, hc6.1, ?_⟩
  rcases hc with h1 | h2
  · obtain ⟨K, hK⟩ := Set.ncard_eq_one.1 h1
    exact ⟨Or.inr ⟨K, ⟨h6, hK⟩, hc6.2.2.1 K hK⟩, Or.inl (G2Term.of_G2Concl (hc6.2.2.1 K hK))⟩
  · obtain ⟨K₁, K₂, hne, hset⟩ := Set.ncard_eq_two.1 h2
    have h4 : Std4 G z S K₁ K₂ := ⟨hStd.kps, hStd.rank.1, hStd.rank.2, hStd.gen4, hcl, hthm, hS, hset, hne, hStd.kgh⟩
    refine ⟨Or.inl ⟨K₁, K₂, h4⟩, ?_⟩
    by_cases hf : ∃ u ∈ Pz S z, IsConj z u ∧ u ≠ z
    · exact Or.inl (G2Term.of_G2TermType (h81r G z S K₁ K₂ h4 hrank.le hf))
    · have hnf : ∀ u ∈ Pz S z, IsConj z u → u = z := by
        intro u hu hz
        by_contra hne
        exact hf ⟨u, hu, hz, hne⟩
      obtain ⟨q, w, hq, hq5, h₁, h₂, ht7⟩ := h71 G z S K₁ K₂ h4 hnf
      exact Or.inr ⟨q, w, K₁, K₂, h4, hq, hq5, h₁, h₂, ht7⟩

end CFSG.GH74.GLS.Stage1.Main
