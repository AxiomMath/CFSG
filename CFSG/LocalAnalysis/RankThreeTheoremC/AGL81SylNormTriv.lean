module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SylNormSym

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

open CFSG.Open CFSG.AGLEmbedding Subgroup Equiv

@[expose] def KFactSylNormTrivSp : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (P : Subgroup A) (b : A),
    (∃ (k : ℕ) (d : TauCeti.ValidLieTypeIndex),
        (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .B k q) ∧
        Nonempty (↥P ⧸ CFSG.pCore 2 ↥P ≃* (TauCeti.CFSGIndex.lie d).Group)) →
    SylAct P b → TrivOnW P b

theorem nonempty_quotient_pCore_mulEquiv_perm {A : Type} [Group A] {P : Subgroup A} {n : ℕ}
    (h2 : CFSG.pCore 2 (Perm (Fin n)) = ⊥) (e : ↥P ≃* Perm (Fin n)) :
    Nonempty (↥P ⧸ CFSG.pCore 2 ↥P ≃* Perm (Fin n)) := by
  have hP : CFSG.pCore 2 ↥P = ⊥ := by
    have h := CFSG.pCore_map_iso 2 e.symm
    rw [h2, Subgroup.map_bot] at h
    exact h.symm
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hP).trans QuotientGroup.quotientBot).trans e⟩

theorem trivOnW_of_mulEquiv_perm {A : Type} [Group A] [Finite A] {P : Subgroup A} {b : A}
    {n : ℕ} (hn : n ≠ 5) (h2 : CFSG.pCore 2 (Perm (Fin n)) = ⊥) (e : ↥P ≃* Perm (Fin n))
    (hb : SylAct P b) : TrivOnW P b := by
  by_contra hW
  exact hn (kFactSylNormSym A P b n (nonempty_quotient_pCore_mulEquiv_perm h2 e) hb hW).2

theorem kFactSylNormTriv_of_sp (hSp : KFactSylNormTrivSp) : KFactSylNormTriv := by
  intro A _ _ P b hP hb
  rcases hP with hP | hP | hP
  · exact hSp A P b hP hb
  · obtain ⟨e⟩ := hP
    refine trivOnW_of_mulEquiv_perm (by decide) (pCore_perm_eq_bot 6 fun j hj => ?_) e hb
    rcases Nat.lt_or_ge j 3 with h | h
    · interval_cases j <;> simp at hj
    · have := Nat.pow_le_pow_right (show 0 < 2 by decide) h
      omega
  · obtain ⟨e⟩ := hP
    refine trivOnW_of_mulEquiv_perm (by decide) (pCore_perm_eq_bot 3 fun j hj => ?_) e hb
    rcases Nat.lt_or_ge j 2 with h | h
    · interval_cases j <;> simp at hj
    · have := Nat.pow_le_pow_right (show 0 < 2 by decide) h
      omega

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
