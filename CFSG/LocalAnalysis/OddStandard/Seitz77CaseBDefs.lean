module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseBNorm

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.RankThreeCoreUniqueness.Helpers

structure CaseB {G : Type} [Group G] [Finite G] (A R : Subgroup G) (t : G) where
  X : Subgroup G
  O : Subgroup G
  Sy : Subgroup G
  Wt : Subgroup G
  P : Subgroup G
  H : Setup27 A R X O Sy Wt P t
  B : Out27B (Ntil27 (Sy ⊓ Wt)) H.X27 H.ttilde27

namespace CaseB

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {t : G} (c : CaseB A R t)

abbrev W : Subgroup G := c.Sy ⊓ c.Wt

abbrev N : Subgroup G := normalizer (c.W : Set G)

abbrev Ninf : Subgroup G := perfectResidualOf c.N

theorem W_elem : IsElemAbelian 2 c.W := c.H.sit.S.elem_inf_Wt c.H.sit.hSy c.H.sit.hWt

theorem W_card : Nat.card c.W = 2 ^ 8 := c.H.sit.S.card_inf_Wt c.H.sit.hSy c.H.sit.hWt

theorem R_le_W : R ≤ c.W := c.H.sit.S.W_le_inf_Wt c.H.sit.hSy c.H.sit.hWt

include c in
theorem t_mul_self : t * t = 1 := c.H.sit.S.t_sq

theorem t_mem_N : t ∈ c.N := c.H.sit.S.t_mem_normalizer_inf_Wt c.H.sit.hSy c.H.sit.hWt

theorem W_inf_centralizer_t : c.W ⊓ centralizer ({t} : Set G) = R :=
  c.H.sit.S.inf_Wt_inf_centralizer_t c.H.sit.hSy c.H.sit.hWt

theorem commutator_W_t : ⁅c.W, zpowers t⁆ = R :=
  c.H.sit.S.commutator_inf_Wt c.H.sit.hSy c.H.sit.hWt

theorem P_le_N : c.P ≤ c.N := c.H.le_normalizer_W

theorem normalizer_A_R_le_N : A ⊓ normalizer (R : Set G) ≤ c.N :=
  c.H.normalizer_A_R_le_normalizer_W

theorem normalizer_E_le_N : normalizer ((R ⊔ zpowers t : Subgroup G) : Set G) ≤ c.N :=
  c.H.W_normalized_by_NE

theorem Ninf_perfect : ⁅c.Ninf, c.Ninf⁆ = c.Ninf :=
  Subgroup.isPerfect_iff.mp (finite_perfectResidualOf_isPerfect c.N)

end CaseB

theorem caseB_of_forall {G : Type} [Group G] [Finite G] {A V₁ V₂ : Subgroup G} {d : Datum A}
    (hyp : ∀ W : Subgroup G, W = V₁ ∨ W = V₂ → ∃ (X O Sy Wt P : Subgroup G)
      (H : Setup27 A W X O Sy Wt P d.t), (∃ w : WData d W, w.S = Sy ∧ w.W = Sy ⊓ Wt) ∧
        Out27B (Ntil27 (Sy ⊓ Wt)) H.X27 H.ttilde27) :
    Nonempty (CaseB A V₁ d.t) ∧ Nonempty (CaseB A V₂ d.t) := by
  obtain ⟨X, O, Sy, Wt, P, H, -, B⟩ := hyp V₁ (Or.inl rfl)
  obtain ⟨X', O', Sy', Wt', P', H', -, B'⟩ := hyp V₂ (Or.inr rfl)
  exact ⟨⟨⟨X, O, Sy, Wt, P, H, B⟩⟩, ⟨⟨X', O', Sy', Wt', P', H', B'⟩⟩⟩

end CFSG.OddStandard.Seitz77
