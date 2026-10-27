module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.Open.StatedAPI

theorem isSimpleGroup_of_statedClassicalModel_psl_two {X : Type} [Group X] {p f : ℕ}
    (h : StatedClassicalModel X .PSL 2 p f) : IsSimpleGroup X := by
  obtain ⟨⟨hp, hf, -, h22, h23⟩, F, _, _, hF, ⟨e⟩⟩ := h
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    have h2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    by_contra hlt
    interval_cases hpf : p ^ f
    · exact h22 rfl
    · exact h23 rfl
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact (e.trans
    (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm).isSimpleGroup

theorem statedClassicalModel_psl_two_of_mulEquiv_zmod {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r)
    {Y : Type} [Group Y] (e : Y ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod r)) :
    StatedClassicalModel Y .PSL 2 r 1 := by
  have := Fact.mk hr
  refine ⟨⟨hr, le_rfl, le_rfl, ?_, ?_⟩, ZMod r, inferInstance, inferInstance, ?_,
    ⟨e.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 (ZMod r))⟩⟩
  · intro h
    simp only [Prod.mk.injEq, true_and, pow_one] at h
    omega
  · intro h
    simp only [Prod.mk.injEq, true_and, pow_one] at h
    omega
  · rw [Nat.card_zmod, pow_one]

end CFSG.Open.StatedAPI

namespace CFSG.Blueprint

theorem LieModel.isSimpleGroup_psl_two {X : Type} [Group X] {p f : ℕ}
    (h : LieModel X .PSL 2 p f) : IsSimpleGroup X :=
  Open.StatedAPI.isSimpleGroup_of_statedClassicalModel_psl_two (h.statedClassicalModel (by decide))

end CFSG.Blueprint
