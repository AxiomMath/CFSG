module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4Refl
public import CFSG.GH74.Generic.BProg.B2.PuL4Inner

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial Subgroup

namespace PuL4Gen4

section Certified

theorem false_of_shape_puL4W {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (hs : ShapeInCent H t L) (hL4 : T4.PuL4W ↥H) (ht : t ∈ commutator N)
    (hG : Gen4 N) : False := by
  have hHn := hs.normal
  by_cases htH : t ∈ H
  · exact PuL4Inner.false_of_inner_shape_W hs hL4 htH
  · have ht2 : t ^ 2 = 1 := by
      have := pow_orderOf_eq_one t
      rwa [hs.inv] at this
    have hc := T4.T4OutComm.conjNormal_mem_commutator (H := H) ht
    obtain ⟨p, f, hp, hp2, hf, h3, ⟨h8, hL⟩ | ⟨h8, hU⟩⟩ := hL4
    · obtain ⟨F, _, _, e, hF, hdiag⟩ := T4.T4OutCore.exists_model_commutator_diag_psl (n := 4)
        (by norm_num) hL
      obtain ⟨A, hA⟩ := hdiag _ hc
      have hA' : MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) = LinearFlag.conjAut 4 F A := by
        rw [hA]; ext x; simp [MulAut.congr_apply]
      exact GenLocL4Refl.false_of_outerDiag_linear hs.faithful (by rw [hF]; exact h8) e htH ht2 A hA' hG
    · obtain ⟨K, _, h, e, hdiag⟩ := T4.T4OutCore.exists_model_commutator_diag_psu (n := 4)
        (by norm_num) (fun hh => absurd hh.1 (by norm_num)) hU
      obtain ⟨A, hA⟩ := hdiag _ hc
      have hA' : MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) =
          UnitaryHigher.primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) A := by
        rw [hA]; ext x; simp [MulAut.congr_apply]
      exact GenLocL4Refl.false_of_outerDiag_unitary h hs.faithful h8 e htH ht2 A hA' hG

structure OutGraphL4W : Prop where
  lin : ∀ {N : Type} [Group N] [Finite N] (H : Subgroup N) [H.Normal] {t : N} {L : Subgroup N}
    {F : Type} [Field F] [Finite F], ShapeInCent H t L → Nat.card F % 8 = 5 →
    ∀ e : ↥H ≃* LinearFlag.projectiveSL 4 F,
      (∀ A : GL (Fin 4) F, MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) ≠
        LinearFlag.conjAut 4 F A) → SectionalTwoRankLE N 4 → False
  uni : ∀ {N : Type} [Group N] [Finite N] (H : Subgroup N) [H.Normal] {t : N} {L : Subgroup N}
    {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K), ShapeInCent H t L →
    3 < p ^ f → p ^ f % 8 = 3 →
    ∀ e : ↥H ≃* UnitaryHigher.primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K),
      (∀ A : UnitaryHigher.primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K),
        MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) ≠
          UnitaryHigher.primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) A) →
      SectionalTwoRankLE N 4 → False

theorem false_of_gen4_puL4W (hOut : OutGraphL4W) {N : Type} [Group N] [Finite N] {H : Subgroup N}
    {t : N} {L : Subgroup N} (hs : ShapeInCent H t L) (hW : T4.PuL4W ↥H)
    (h4 : SectionalTwoRankLE N 4) : False := by
  have hHn := hs.normal
  by_cases htH : t ∈ H
  · exact PuL4Inner.false_of_inner_shape_W hs hW htH
  · have ht2 : t ^ 2 = 1 := by
      have := pow_orderOf_eq_one t
      rwa [hs.inv] at this
    obtain ⟨p, f, hp, hp2, hf, h3, ⟨h8, hL⟩ | ⟨h8, hU⟩⟩ := hW
    · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := T4.T4OutCore.linear_model hL
      have hF8 : Nat.card F % 8 = 5 := by rw [hF]; exact h8
      by_cases hdiag : ∃ A : GL (Fin 4) F,
          MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) = LinearFlag.conjAut 4 F A
      · obtain ⟨A, hA⟩ := hdiag
        exact GenLocL4Refl.false_of_outerDiag_linear hs.faithful hF8 e htH ht2 A hA h4
      · push Not at hdiag
        exact hOut.lin H hs hF8 e hdiag h4
    · obtain ⟨K, _, h, ⟨e⟩⟩ := T4.T4OutCore.primeForm_model (n := 4) (by norm_num)
        (fun hh => absurd hh.1 (by norm_num)) hU
      by_cases hdiag : ∃ A : UnitaryHigher.primeFormUnitary h
          ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K),
          MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) =
            UnitaryHigher.primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) A
      · obtain ⟨A, hA⟩ := hdiag
        exact GenLocL4Refl.false_of_outerDiag_unitary h hs.faithful h8 e htH ht2 A hA h4
      · push Not at hdiag
        exact hOut.uni H h hs h3 h8 e hdiag h4

end Certified

end PuL4Gen4

@[expose] def PuL4m (H : Type) [Group H] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 3 < p ^ f ∧
    ((p ^ f % 4 = 3 ∧ LieModel H .PSL 4 p f) ∨ (p ^ f % 4 = 1 ∧ LieModel H .PSU 4 p f))

section Certified

theorem puL4m_of_gen4 (hOut : PuL4Gen4.OutGraphL4W) {N : Type} [Group N] [Finite N]
    (H : Subgroup N) (t : N) (L : Subgroup N) (hs : ShapeInCent H t L)
    (h4 : SectionalTwoRankLE N 4) (hJ : PuL4 ↥H) : PuL4m ↥H := by
  rcases T4.puL4_cases hJ with hSD | hW
  · exact hSD
  · exact (PuL4Gen4.false_of_gen4_puL4W hOut hs hW h4).elim

end Certified

end CFSG.GH74.Generic.BProg.B2
