module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDeduce
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutFieldPSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutFieldPSU
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutFieldSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutFieldOrth
import CFSG.RankThree.PartOne.S11c.Sec66Glue

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.RankThree.PartOne (centerQuotientConj)
open CFSG.RankThree.PartOne.Sec66T (innerAut)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint (LieModel)

@[expose] def DiagType (X : Type) [Group X] (p : ℕ) : Prop :=
  (∃ n f : ℕ, StatedClassicalModel X .PSL n 2 f ∧ p ∣ Nat.gcd n (2 ^ f - 1)) ∨
    (∃ n f : ℕ, StatedClassicalModel X .PSU n 2 f ∧ p ∣ Nat.gcd n (2 ^ f + 1))

structure LieOutInputs : Prop where
  psl_two : ∀ {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {p : ℕ} {x : Y}, p.Prime → 5 ≤ p →
    ∀ (hx : x ∈ Subgroup.normalizer (L : Set Y)), x ^ p = 1 →
    centerQuotientConj L ⟨x, hx⟩ ∉ innerAut (↥L ⧸ Subgroup.center ↥L) →
    [Nontrivial (↥L ⧸ Subgroup.center ↥L)] →
    StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 2 p → LieOutConcl L x
  psu_three : ∀ {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {p : ℕ} {x : Y}, p.Prime →
    5 ≤ p → ∀ (hx : x ∈ Subgroup.normalizer (L : Set Y)), x ^ p = 1 →
    centerQuotientConj L ⟨x, hx⟩ ∉ innerAut (↥L ⧸ Subgroup.center ↥L) →
    [Nontrivial (↥L ⧸ Subgroup.center ↥L)] →
    StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 2 p → LieOutConcl L x
  psp_two : ∀ {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {p : ℕ} {x : Y}, p.Prime → 5 ≤ p →
    ∀ (hx : x ∈ Subgroup.normalizer (L : Set Y)), x ^ p = 1 →
    centerQuotientConj L ⟨x, hx⟩ ∉ innerAut (↥L ⧸ Subgroup.center ↥L) →
    [Nontrivial (↥L ⧸ Subgroup.center ↥L)] →
    StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp 2 2 p → LieOutConcl L x
  g2 : ∀ {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {p : ℕ} {x : Y}, p.Prime → 5 ≤ p →
    ∀ (hx : x ∈ Subgroup.normalizer (L : Set Y)), x ^ p = 1 →
    centerQuotientConj L ⟨x, hx⟩ ∉ innerAut (↥L ⧸ Subgroup.center ↥L) →
    [Nontrivial (↥L ⧸ Subgroup.center ↥L)] →
    LieModel (↥L ⧸ Subgroup.center ↥L) .G2 0 2 p → LieOutConcl L x

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {p : ℕ} {x : Y}

theorem lieOut_of_model_psl (I : LieOutInputs) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hx : x ∈ Subgroup.normalizer (L : Set Y)) (hxp : x ^ p = 1)
    (hαinn : centerQuotientConj L ⟨x, hx⟩ ∉ innerAut (↥L ⧸ Subgroup.center ↥L))
    [Nontrivial (↥L ⧸ Subgroup.center ↥L)] {n f : ℕ}
    (h : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL n 2 f) :
    DiagType (↥L ⧸ Subgroup.center ↥L) p ∨ LieOutConcl L x := by
  have hαp := CFSG.RankThree.PartOne.Sec66T.centerQuotientConj_pow hx hxp
  by_cases hdiag : p ∣ Nat.gcd n (2 ^ f - 1)
  · exact Or.inl (Or.inl ⟨n, f, h, hdiag⟩)
  · refine Or.inr ?_
    have hn2 : 2 ≤ n := h.1.2.2.1
    have hOL := overgroupLocal_of_model_psl h
    rcases Nat.lt_or_ge n 3 with hn | hn
    · obtain rfl : n = 2 := by omega
      by_cases hfp : f = p
      · subst hfp
        exact I.psl_two hp hp5 hx hxp hαinn h
      · exact lieOutConcl_of_fixesNonLocalized hx hOL
          (fixesNonLocalized_psl_two hp hp5 h hfp hαp hαinn)
    · exact lieOutConcl_of_fixesNonLocalized hx hOL
        (fixesNonLocalized_psl_ge_three hp hp5 hn h hdiag hαp hαinn)

theorem lieOut_of_model_psu (I : LieOutInputs) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hx : x ∈ Subgroup.normalizer (L : Set Y)) (hxp : x ^ p = 1)
    (hαinn : centerQuotientConj L ⟨x, hx⟩ ∉ innerAut (↥L ⧸ Subgroup.center ↥L))
    [Nontrivial (↥L ⧸ Subgroup.center ↥L)] {n f : ℕ}
    (h : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU n 2 f) :
    DiagType (↥L ⧸ Subgroup.center ↥L) p ∨ LieOutConcl L x := by
  have hαp := CFSG.RankThree.PartOne.Sec66T.centerQuotientConj_pow hx hxp
  by_cases hdiag : p ∣ Nat.gcd n (2 ^ f + 1)
  · exact Or.inl (Or.inr ⟨n, f, h, hdiag⟩)
  · refine Or.inr ?_
    have hOL := overgroupLocal_of_model_psu h
    by_cases hspec : n = 3 ∧ f = p
    · obtain ⟨rfl, rfl⟩ := hspec
      exact I.psu_three hp hp5 hx hxp hαinn h
    · exact lieOutConcl_of_fixesNonLocalized hx hOL
        (fixesNonLocalized_psu hp hp5 h hdiag hspec hαp hαinn)

theorem lieOut_of_model_psp (I : LieOutInputs) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hx : x ∈ Subgroup.normalizer (L : Set Y)) (hxp : x ^ p = 1)
    (hαinn : centerQuotientConj L ⟨x, hx⟩ ∉ innerAut (↥L ⧸ Subgroup.center ↥L))
    [Nontrivial (↥L ⧸ Subgroup.center ↥L)] {n f : ℕ}
    (h : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp n 2 f) :
    DiagType (↥L ⧸ Subgroup.center ↥L) p ∨ LieOutConcl L x := by
  have hαp := CFSG.RankThree.PartOne.Sec66T.centerQuotientConj_pow hx hxp
  refine Or.inr ?_
  by_cases hspec : n = 2 ∧ f = p
  · obtain ⟨rfl, rfl⟩ := hspec
    exact I.psp_two hp hp5 hx hxp hαinn h
  · exact lieOutConcl_of_fixesNonLocalized hx (overgroupLocal_of_model_psp h)
      (fixesNonLocalized_psp hp hp5 h hspec hαp hαinn)

theorem lieOut_of_model_pomegaPlus (hp : p.Prime) (hp5 : 5 ≤ p)
    (hx : x ∈ Subgroup.normalizer (L : Set Y)) (hxp : x ^ p = 1)
    (hαinn : centerQuotientConj L ⟨x, hx⟩ ∉ innerAut (↥L ⧸ Subgroup.center ↥L))
    [Nontrivial (↥L ⧸ Subgroup.center ↥L)] {n f : ℕ}
    (h : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .POmegaPlus n 2 f) :
    DiagType (↥L ⧸ Subgroup.center ↥L) p ∨ LieOutConcl L x :=
  Or.inr (lieOutConcl_of_fixesNonLocalized hx (overgroupLocal_of_model_pomegaPlus h)
    (fixesNonLocalized_pomegaPlus hp hp5 h
      (CFSG.RankThree.PartOne.Sec66T.centerQuotientConj_pow hx hxp) hαinn))

theorem lieOut_of_model_pomegaMinus (hp : p.Prime) (hp5 : 5 ≤ p)
    (hx : x ∈ Subgroup.normalizer (L : Set Y)) (hxp : x ^ p = 1)
    (hαinn : centerQuotientConj L ⟨x, hx⟩ ∉ innerAut (↥L ⧸ Subgroup.center ↥L))
    [Nontrivial (↥L ⧸ Subgroup.center ↥L)] {n f : ℕ}
    (h : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .POmegaMinus n 2 f) :
    DiagType (↥L ⧸ Subgroup.center ↥L) p ∨ LieOutConcl L x :=
  Or.inr (lieOutConcl_of_fixesNonLocalized hx (overgroupLocal_of_model_pomegaMinus h)
    (fixesNonLocalized_pomegaMinus hp hp5 h
      (CFSG.RankThree.PartOne.Sec66T.centerQuotientConj_pow hx hxp) hαinn))

end CFSG.AGLEmbedding.LieOut
