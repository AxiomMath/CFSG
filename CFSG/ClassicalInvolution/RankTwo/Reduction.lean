module

public import CFSG.ClassicalInvolution.RankTwo.Exclusion
public import CFSG.Blueprint.Catalog
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.M11Order

public section

namespace CFSG.ClassicalInvolution

open CFSG.Assembly.LowTwoRank

@[expose] def RankTwoTypes (F : Type) [Group F] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel F .PSL 2 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel F .PSL 3 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel F .PSU 3 p f) ∨
    StatedClassicalModel F .PSU 3 2 2 ∨
    Nonempty (F ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (F ≃* StatedM11)

theorem isSporadic_m11_of_nonempty_mulEquiv_statedM11 {F : Type} [Group F]
    (h : Nonempty (F ≃* StatedM11)) : CFSG.Blueprint.NativeSporadic.IsSporadic F .M11 := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans (MulEquiv.subgroupCongr
    CFSG.Semidihedral.GL2Recognition.lowTwoRankStatedM11_eq_nativeM11)⟩

theorem oddLieType_or_m11_of_rankTwoTypes {F : Type} [Group F] [Finite F] [IsSimpleGroup F]
    (hnab : ∃ a b : F, a * b ≠ b * a) {K : Subgroup F}
    (hw : CFSG.Open.classicalInvolutionWitness K) (h : RankTwoTypes F) :
    CFSG.Blueprint.OddLieType F ∨ CFSG.Blueprint.NativeSporadic.IsSporadic F .M11 := by
  rcases h with ⟨p, f, hp, hp2, -, h⟩ | ⟨p, f, hp, hp2, -, h⟩ | ⟨p, f, hp, hp2, -, h⟩ | h | h | h
  · exact Or.inl ⟨.PSL, 2, p, f, hp, hp2, h.1, Or.inl ⟨by decide, h⟩⟩
  · exact Or.inl ⟨.PSL, 3, p, f, hp, hp2, h.1, Or.inl ⟨by decide, h⟩⟩
  · exact Or.inl ⟨.PSU, 3, p, f, hp, hp2, h.1, Or.inl ⟨by decide, h⟩⟩
  · exact (false_of_witness_of_statedClassicalModel_psu_three_two_two h hw).elim
  · obtain ⟨e⟩ := h
    exact (false_of_witness_of_equiv_alternatingGroup_seven hnab e hw).elim
  · exact Or.inr (isSporadic_m11_of_nonempty_mulEquiv_statedM11 h)

end CFSG.ClassicalInvolution
