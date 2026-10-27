module

public import CFSG.Milestones.CL_LIT_Fischer_three_transposition_theorem
public import CFSG.Fischer.Classification.WidthTwoSym
public import CFSG.Fischer.Classification.WidthTwoSp
public import CFSG.Fischer.Classification.WidthTwoO
public import CFSG.Fischer.Classification.O4Minus2S5
public import CFSG.Fischer.Classification.WidthTwoF3
public import CFSG.Fischer.Classification.WidthTwoSporadic

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Open CFSG.OddTranspositions CFSG.GroupTheory Matrix

theorem width_two_fischer_pair_is_S5
    {Y : Type} [Group Y] [Finite Y] {Θ : Set Y}
    (hP : Pair Y Θ) (hZ : Subgroup.center Y = ⊥) (hS : IsSimpleGroup (commutator Y))
    (hW : WidthLe Θ 2) (hns : ¬ Group.IsSolvable Y) :
    ∃ e : Y ≃* Equiv.Perm (Fin 5), e '' Θ = transpositions := by
  have h := CFSG.Milestones.cl_lit_fischer_three_transposition_theorem_pinned
    Y Θ hP.2.1 hP.2.2.1 hP.2.2.2.1 hP.2.2.2.2 hZ hS
  rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  ·
    obtain ⟨m, hm, φ, hφ⟩ := h1
    have hm5 : m = 5 := sym_width_two_m_eq_five hm φ hφ hW hns
    subst m
    refine ⟨φ, ?_⟩
    ext σ
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [transpositions] using (hφ y).1 hy
    · intro hσ
      exact ⟨φ.symm σ, (hφ _).2 (by simpa [transpositions] using hσ), by simp⟩
  ·
    exact absurd hW (width_two_false_of_sp_case h2)
  ·
    obtain ⟨m, hm2, Q, hnd, hno, hM⟩ := h3
    rcases eq_or_lt_of_le hm2 with h2 | h2
    ·
      have hm : m = 2 := h2.symm
      subst m
      let Q4 : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2) := Q
      have hnd4 : ∀ x, (∀ y, QuadraticMap.polar Q4 x y = 0) → x = 0 := hnd
      have hno4 : ¬ ∃ W : Submodule (ZMod 2) (Fin 4 → ZMod 2),
          Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q4 w = 0 := hno rfl
      have hM4 : fischerLinearModel Θ
          (fischerMatrixGroup fun A => ∀ x, Q4 (A *ᵥ x) = Q4 x)
          (fischerTransvections (QuadraticMap.polar Q4) fun v => Q4 v = 1) := hM
      obtain ⟨φ, hφ⟩ := hM4
      have himg : φ '' Θ = transvectionSet Q4 := by
        ext g
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact (hφ y).1 hy
        · intro hg
          refine ⟨φ.symm g, ?_, by simp⟩
          rw [hφ (φ.symm g), φ.apply_symm_apply]
          exact hg
      obtain ⟨e, he⟩ := o4minus2_equiv_s5 hnd4 hno4
      refine ⟨φ.trans e, ?_⟩
      rw [MulEquiv.coe_trans, Set.image_comp, himg, he]
    ·
      exact absurd hW (width_two_false_of_orthogonal_case (by omega : 3 ≤ m) Q hnd hM)
  ·
    obtain ⟨m, hm, hM⟩ := h4
    exact absurd hW (Unitary.width_two_false_of_psu_case hm hM)
  ·
    obtain ⟨m, hm, f, hsymm, hnd, hM⟩ := h5
    exact absurd hW (width_two_false_of_f3_case hm hsymm hnd hM)
  ·
    obtain ⟨φ, hpair, -⟩ := h6
    obtain ⟨-, -, hT, hDuniq, -⟩ := CFSG.Sporadic.Fi22.existence_native
    have hD := hDuniq _ hpair
    have hTY : HasType 0 Y Θ := by
      rw [← CFSG.Fischer.image_symm_image φ Θ, hD]
      exact hasType_map hT φ.symm
    exact absurd hW (width_two_false_of_hasType (k := 0) hTY)
  ·
    obtain ⟨φ, hpair, -⟩ := h7
    obtain ⟨-, -, hT, hDuniq, -⟩ := CFSG.Sporadic.Fi23.existence_native
    have hD := hDuniq _ hpair
    have hTY : HasType 1 Y Θ := by
      rw [← CFSG.Fischer.image_symm_image φ Θ, hD]
      exact hasType_map hT φ.symm
    exact absurd hW (width_two_false_of_hasType (k := 1) hTY)
  ·
    obtain ⟨φ, hpair, -⟩ := h8
    have hFF := CFSG.Sporadic.Fi22.fi22Facts CFSG.Fischer.polarFacts CFSG.Fischer.hyperovalFacts
    obtain ⟨-, -, hT, hDuniq, -⟩ := CFSG.Sporadic.Fi24.existence_native
      CFSG.Fischer.polarFacts CFSG.Fischer.hyperovalFacts hFF
      (CFSG.Sporadic.Fi23.fi23Facts hFF) CFSG.Sporadic.Fi22.card_fixed_involution_D
      CFSG.Sporadic.Fi22.eq_of_commute_centralizer CFSG.Sporadic.Fi24.edgeSwap_a
      CFSG.Sporadic.Fi23.d1_mem_localClass CFSG.Sporadic.Fi23.involution_cover
    have hD := hDuniq _ hpair
    have hTY : HasType 2 Y Θ := by
      rw [← CFSG.Fischer.image_symm_image φ Θ, hD]
      exact hasType_map hT φ.symm
    exact absurd hW (width_two_false_of_hasType (k := 2) hTY)

end CFSG.Fischer.Classification
