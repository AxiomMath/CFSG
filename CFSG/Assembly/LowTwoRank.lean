module

public import CFSG.Assembly.LowTwoRankDefs
import CFSG.Milestones.LR_rank_two_isomorphism_types
import CFSG.Adapters.ClassicalCatalogLinearUnitary
import CFSG.Adapters.ClassicalCatalogReverse
import CFSG.Walter.TwoRank

public section

namespace CFSG.Assembly
namespace LowTwoRank
open Matrix

theorem two_le_twoRank (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (heven : Even (Nat.card G)) :
    2 ≤ twoRank G := CFSG.Walter.two_le_twoRank G hnonab heven

theorem rank_two_isomorphism_types
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hrank : twoRank G = 2) :
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSL 2 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSL 3 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSU 3 p f) ∨
    StatedClassicalModel G .PSU 3 2 2 ∨
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (G ≃* StatedM11) :=
  _root_.CFSG.Milestones.lr_rank_two_isomorphism_types G hnonab hrank

set_option linter.unusedSectionVars false in
theorem inCatalog_of_classicalModel (G : Type) [Group G] (t : StatedLieTag) (n p f : ℕ)
    (h : StatedClassicalModel G t n p f) : InCatalog G :=
  CFSG.ClassicalModels.inCatalog_of_statedClassicalModel G t n p f h

theorem _root_.CFSG.Milestones.fam_classical_model_membership_catalog (G : Type) [Group G]
    (t : StatedLieTag) (n p f : ℕ) (h : StatedClassicalModel G t n p f) : InCatalog G :=
  inCatalog_of_classicalModel G t n p f h

theorem inCatalog_of_mulEquiv_m11 (G : Type) [Group G] (h : Nonempty (G ≃* StatedM11)) :
    InCatalog G := by
  have hM : StatedM11 = Blueprint.NativeSporadic.M11 := by
    unfold StatedM11 Blueprint.NativeSporadic.M11
    congr 1
  obtain ⟨e⟩ := h
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  exact ⟨.sporadic .M11, ⟨(e.trans (MulEquiv.subgroupCongr hM)).trans b⟩⟩

end LowTwoRank

open LowTwoRank in
theorem low_two_rank
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (heven : Even (Nat.card G))
    (hrank : twoRank G ≤ 2) : InCatalog G := by
  have h2 : twoRank G = 2 := le_antisymm hrank (two_le_twoRank G hnonab heven)
  rcases rank_two_isomorphism_types G hnonab h2 with
    ⟨p, f, -, -, -, h⟩ | ⟨p, f, hp, hp2, -, h⟩ | ⟨p, f, -, -, -, h⟩ | h | h | h
  · exact ClassicalModels.statedClassicalModel_PSL_two_inCatalog G p f h
  · refine ClassicalModels.statedClassicalModel_PSL_inCatalog G 3 p f le_rfl h ?_ (by simp)
    intro he
    have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    rw [(Prod.mk.inj he).2] at hodd
    exact (by decide : ¬ Odd 2) hodd
  · exact ClassicalModels.statedClassicalModel_PSU_inCatalog G 3 p f h
  · exact ClassicalModels.statedClassicalModel_PSU_inCatalog G 3 2 2 h
  · have h7 : 5 ≤ 7 := by norm_num
    exact ⟨.alternating 7 h7, h⟩
  · exact inCatalog_of_mulEquiv_m11 G h

end CFSG.Assembly
