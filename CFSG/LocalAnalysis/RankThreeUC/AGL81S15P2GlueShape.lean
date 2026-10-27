module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Open

theorem ystar_eq_bot_of_gnShape_of_alt_five {Y : Type} [Group Y] [Finite Y]
    {S S₁ S₂ : Subgroup Y} (hshape : GNShape S S₁ S₂)
    (h5 : ∀ L : Subgroup (Y ⧸ gnC S), IsComponentOf L ⊤ →
      Nonempty (↥L ≃* alternatingGroup (Fin 5))) :
    Ystar S S₁ S₂ = ⊥ := by
  rw [Ystar, iSup_eq_bot]
  intro L
  rw [iSup_eq_bot]
  intro hL
  obtain ⟨e⟩ := h5 L hL.1
  obtain ⟨-, hcase⟩ := hshape L hL
  rcases hcase with ⟨-, hrk⟩ | ⟨n, hn, ⟨e'⟩⟩
  · have hZ : Subgroup.center ↥L = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
      have h1 : e z ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
        rw [Subgroup.mem_center_iff] at hz ⊢
        intro y
        simpa using congrArg e (hz (e.symm y))
      rw [alternatingGroup.center_eq_bot (α := Fin 5) (by simp), Subgroup.mem_bot] at h1
      exact e.injective (h1.trans (map_one e).symm)
    have hquot : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 5)) :=
      ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)⟩
    exact absurd (Or.inr hquot) hrk
  · have hn2 : 2 ≤ n := by
      rcases hn with rfl | ⟨h8, -⟩ <;> omega
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn2
    have hcardn : Nat.card (alternatingGroup (Fin n)) =
        Nat.card (alternatingGroup (Fin 5)) :=
      (Nat.card_congr e'.toEquiv).symm.trans (Nat.card_congr e.toEquiv)
    have h1 := two_mul_nat_card_alternatingGroup (α := Fin n)
    have h2 := two_mul_nat_card_alternatingGroup (α := Fin 5)
    rw [hcardn] at h1
    simp only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h1 h2
    have hn5 : n = 5 := (Nat.factorial_inj (by omega)).1 (h1.symm.trans h2)
    rcases hn with h7 | ⟨h8, -⟩ <;> omega

end CFSG.LocalAnalysis.RankThreeUC.S15

end
