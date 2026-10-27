module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Defs

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

theorem IsMaxAhatDeg.unique {X : Type} [Group X] {n m : ℕ} (hn : IsMaxAhatDeg X n)
    (hm : IsMaxAhatDeg X m) : n = m := by
  obtain ⟨hn8, ⟨t, L, ht, hL, hc⟩, hnmax⟩ := hn
  obtain ⟨hm8, ⟨t', L', ht', hL', hc'⟩, hmmax⟩ := hm
  exact le_antisymm (hmmax n t L hn8 ht hL hc) (hnmax m t' L' hm8 ht' hL' hc')

theorem sec6Entry_of_mcomp {X : Type} [Group X] {n : ℕ} {t : X} {M : Subgroup X}
    (ht : orderOf t = 2) (h : Sec6MComp X n (cen t) M) : Sec6Entry X n := by
  obtain ⟨hM, hty⟩ := h
  have hM' : IsMLIntr X t M := isMLIntr_iff.2 hM
  rcases hty with ⟨h8, e⟩ | ⟨h11, e⟩
  · exact Or.inl ⟨h8, t, M, ht, hM', e⟩
  · exact Or.inr ⟨h11, t, M, ht, hM', e⟩

theorem sec6Entry_of_pumpUp {X : Type} [Group X] [Finite X] {n : ℕ} (hA : ¬ HypA X)
    (hn : IsMaxAhatDeg X n) (hP : Sec6PumpUp X n) : Sec6Entry X n := by
  unfold HypA at hA
  push Not at hA
  obtain ⟨m, hm, t, L, ht, hL, hc, hnot⟩ := hA
  have hmn : m = n := IsMaxAhatDeg.unique hm hn
  rw [hmn] at hc
  have hLc : IsLComp X L := hL.isLComp ht
  have hex : ∃ M, LBelow X L M ∧ ¬ LBelow X M L := by
    by_contra hcon
    push Not at hcon
    exact hnot ⟨hLc, hcon⟩
  obtain ⟨M, hLM, hML⟩ := hex
  have key : ∀ M', LBelow X L M' → Sec6Entry X n ∨
      ((∃ s u : X, orderOf s = 2 ∧ IsIntrinsicIn X (cen s) M' u) ∧
        IsDoubleCoverOfAlt (↥M' ⧸ pPrimeCore 2 ↥M') n ∧ LBelow X M' L) := by
    intro M' h
    unfold LBelow at h
    induction h with
    | refl => exact Or.inr ⟨⟨t, t, ht, hL.isIntrinsicIn ht⟩, hc, Relation.ReflTransGen.refl⟩
    | @tail b c _ hbc ih =>
      rcases ih with hE | ⟨⟨s₁, u, hs₁, hb⟩, hbt, hbL⟩
      · exact Or.inl hE
      obtain ⟨hbL', hcL', hprec⟩ := hbc
      rcases hprec with heq | ⟨s, s', hs, hs', hcomm, hne, hbs, hcs', hs'b, hlt⟩
      · subst heq
        exact Or.inr ⟨⟨s₁, u, hs₁, hb⟩, hbt, hbL⟩
      · have hb' : IsIntrinsicIn X (cen s) b u := ⟨hb.1, hb.2.1, hbs, hb.2.2.2⟩
        rcases hP s s' u b c hs hs' hcomm hne hb' hbt hcs' hs'b hlt with
          ⟨⟨u', hu'⟩, hcc, hcb⟩ | hMc
        · exact Or.inr ⟨⟨s', u', hs', hu'⟩, hcc, Relation.ReflTransGen.head ⟨hcL', hbL', hcb⟩ hbL⟩
        · exact Or.inl (sec6Entry_of_mcomp hs' hMc)
  rcases key M hLM with hE | ⟨-, -, hML'⟩
  · exact hE
  · exact absurd hML' hML

theorem sec6Choice_exists {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : ∃ s : X, orderOf s = 2 ∧ ∃ M, Sec6MComp X n (cen s) M) : ∃ t, IsSec6Choice X n t := by
  classical
  haveI := Fintype.ofFinite X
  set I : Finset X := Finset.univ.filter fun s => orderOf s = 2 ∧ ∃ M, Sec6MComp X n (cen s) M
    with hI
  set f : X → ℕ := fun s => modOddCard (Sec6M X n (cen s)) with hf
  set g : X → ℕ := fun s => modOddCard (Sec6K X n (cen s)) with hg
  have hIne : I.Nonempty := by
    obtain ⟨s, hs⟩ := h
    exact ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ _, hs⟩⟩
  obtain ⟨t₁, ht₁I, ht₁max⟩ := I.exists_max_image f hIne
  set I₂ : Finset X := I.filter fun s => f s = f t₁ with hI₂
  have hI₂ne : I₂.Nonempty := ⟨t₁, Finset.mem_filter.2 ⟨ht₁I, rfl⟩⟩
  obtain ⟨t, htI₂, htmax⟩ := I₂.exists_max_image g hI₂ne
  obtain ⟨htI, hft⟩ := Finset.mem_filter.1 htI₂
  obtain ⟨-, ht2, htM⟩ := Finset.mem_filter.1 htI
  refine ⟨t, ht2, htM, fun s hs => ?_, fun s hs hsM hfs => ?_⟩
  · by_cases hsM : ∃ M, Sec6MComp X n (cen s) M
    · have h1 : f s ≤ f t₁ := ht₁max s (Finset.mem_filter.2 ⟨Finset.mem_univ _, hs, hsM⟩)
      exact h1.trans hft.symm.le
    · have hbot : Sec6M X n (cen s) = ⊥ := sSup_eq_bot.2 fun M hM => absurd ⟨M, hM⟩ hsM
      show modOddCard (Sec6M X n (cen s)) ≤ modOddCard (Sec6M X n (cen t))
      rw [hbot]
      calc modOddCard (⊥ : Subgroup X) ≤ Nat.card ↥(⊥ : Subgroup X) :=
            Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
        _ = 1 := Subgroup.card_bot
        _ ≤ modOddCard (Sec6M X n (cen t)) := Nat.card_pos
  · have hsI₂ : s ∈ I₂ := Finset.mem_filter.2
      ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hs, hsM⟩, hfs.trans hft⟩
    exact htmax s hsI₂

theorem Sec6Entry.exists_mcomp {X : Type} [Group X] {n : ℕ} (hE : Sec6Entry X n) :
    (n = 8 ∨ n = 11) ∧ ∃ s : X, orderOf s = 2 ∧ ∃ M, Sec6MComp X n (cen s) M := by
  rcases hE with ⟨h8, s, M, hs, hM, e⟩ | ⟨h11, s, M, hs, hM, e⟩
  · exact ⟨Or.inl h8, s, hs, M, isMLIntr_iff.1 hM, Or.inl ⟨h8, e⟩⟩
  · exact ⟨Or.inr h11, s, hs, M, isMLIntr_iff.1 hM, Or.inr ⟨h11, e⟩⟩

theorem sec6Setting_exists {X : Type} [Group X] [Finite X] (hc : SolCEx X) (hA : ¬ HypA X)
    {n : ℕ} (hn : IsMaxAhatDeg X n) (hE : Sec6Entry X n)
    (hcen : ∀ t, IsSec6Choice X n t →
      ∃ t', IsSec6Choice X n t' ∧ (K0 X n (cen t') ≠ ⊥ → t' ∈ K0 X n (cen t'))) :
    ∃ t, Sec6Setting X n t := by
  obtain ⟨hdeg, hM⟩ := hE.exists_mcomp
  obtain ⟨t₀, ht₀⟩ := sec6Choice_exists hM
  obtain ⟨t, ht, hcent⟩ := hcen t₀ ht₀
  exact ⟨t, ⟨hc, hA, hn, hdeg, ht, hcent⟩⟩

end CFSG.OddStandard.Solomon75
