module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentFrame
public import CFSG.RankThree.PartOne.K159.RowFourType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

open Module QuadraticMap CFSG.GroupTheory.WeirSylow CFSG.RankThree.PartOne.K159

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {m : ℕ} {U : Fin m → Submodule F V}

theorem isPlusType_comp_top_iff :
    IsPlusType (Q.comp (⊤ : Submodule F V).subtype) ↔ IsPlusType Q :=
  isPlusType_congr ⟨Submodule.topEquiv, fun _ => rfl⟩

theorem IsPlaneSystem.isPlusType_biSup_iff (hF : IsPlaneSystem Q U) (s : Finset (Fin m)) :
    IsPlusType (Q.comp (⨆ j ∈ s, U j).subtype) ↔ Even s.card := by
  induction s using Finset.induction_on with
  | empty =>
    have hbot : (⨆ j ∈ (∅ : Finset (Fin m)), U j) = (⊥ : Submodule F V) := by simp
    rw [hbot]
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · simpa using Even.zero
    · haveI : Subsingleton ↥(⊥ : Submodule F V) :=
        ⟨fun x y => Subtype.ext (by
          rw [(Submodule.mem_bot F).1 x.2, (Submodule.mem_bot F).1 y.2])⟩
      exact isPlusType_of_subsingleton _
  | insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.card_insert_of_notMem ha]
    by_cases hs : s = ∅
    · subst hs
      have hbot : (⨆ j ∈ (∅ : Finset (Fin m)), U j) = (⊥ : Submodule F V) := by simp
      rw [hbot, sup_bot_eq, Finset.card_empty, Nat.zero_add]
      exact ⟨fun h => absurd h (hF.not_isPlusType a), fun h => absurd h Nat.not_even_one⟩
    · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.2 hs
      have hcard1 : 1 ≤ s.card := by
        have := Finset.card_pos.2 hsne
        omega
      have hdisj : Disjoint (U a) (⨆ j ∈ s, U j) := hF.disjoint_biSup ha
      have horth : ∀ x ∈ U a, ∀ y ∈ (⨆ j ∈ s, U j), polar Q x y = 0 := by
        intro x hx y hy
        exact (mem_polarPerp_iff.1 (hF.biSup_le_polarPerp ha hy)) x hx
      rw [isPlusType_congr (isometryEquivSup Q (U a) (⨆ j ∈ s, U j) hdisj horth)]
      rw [isPlusType_prod_iff (hF.nondeg a) (hF.nondeg_biSup s) (d₁ := 1) (d₂ := s.card)
        le_rfl hcard1 (hF.finrank_eq a) (hF.finrank_biSup s)]
      rw [ih, Nat.even_add_one]
      exact ⟨fun h he => hF.not_isPlusType a (h.2 he),
        fun hne => ⟨fun hp => absurd hp (hF.not_isPlusType a), fun he => absurd he hne⟩⟩

theorem IsPlaneSystem.isPlusType_iff_of_finrank (hF : IsPlaneSystem Q U)
    (hdim : Module.finrank F V = 2 * m) : IsPlusType Q ↔ Even m := by
  have htop : (⨆ j ∈ (Finset.univ : Finset (Fin m)), U j : Submodule F V) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hF.finrank_biSup, Finset.card_univ, Fintype.card_fin, hdim]
  have h := hF.isPlusType_biSup_iff Finset.univ
  rw [Finset.card_univ, Fintype.card_fin, htop] at h
  exact isPlusType_comp_top_iff.symm.trans h

end CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

end
