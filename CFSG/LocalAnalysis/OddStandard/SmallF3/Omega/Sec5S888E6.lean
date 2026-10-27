module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

@[expose] def suppUnion (C : Finset (Fin 4 → ZMod 2)) : Finset (Fin 4) :=
  Finset.univ.filter fun i => ∃ c ∈ C, c i ≠ 0

@[expose] def fixedBound (H : Finset (Equiv.Perm (Fin 4))) (C : Finset (Fin 4 → ZMod 2)) : ℕ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin 4 => ∀ a ∈ H, i ≤ a i),
    if i ∈ suppUnion C then 2 else 4

private instance instDecidableIsEvenVec4 (v : Fin 4 → ZMod 2) : Decidable (IsEvenVec v) := by
  unfold IsEvenVec
  infer_instance

private def inv6 : Finset (Equiv.Perm (Fin 4)) :=
  Finset.univ.filter (fun a => a * a = 1)

private def closed6 (S : Finset (Equiv.Perm (Fin 4))) : Bool :=
  decide (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)

private def fixedEven6 (S : Finset (Equiv.Perm (Fin 4))) : Finset (Fin 4 → ZMod 2) :=
  Finset.univ.filter (fun x => IsEvenVec x ∧ ∀ a ∈ S, ∀ i, x (a i) = x i)

private def suppIn6 (S : Finset (Equiv.Perm (Fin 4))) (U : Finset (Fin 4)) :
    Finset (Fin 4 → ZMod 2) :=
  (fixedEven6 S).filter (fun x => ∀ i, x i ≠ 0 → i ∈ U)

private def fixedBoundU (H : Finset (Equiv.Perm (Fin 4))) (U : Finset (Fin 4)) : ℕ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin 4 => ∀ a ∈ H, i ≤ a i),
    if i ∈ U then 2 else 4

private lemma fixedBound_eq_fixedBoundU (H : Finset (Equiv.Perm (Fin 4)))
    (C : Finset (Fin 4 → ZMod 2)) :
    fixedBound H C = fixedBoundU H (suppUnion C) := rfl

private def checkSUb (S : Finset (Equiv.Perm (Fin 4))) (U : Finset (Fin 4)) : Bool :=
  decide ((U = ∅ → (S.card = 1 ∨ S.card * fixedBoundU S ∅ ≤ 2 ^ 7)) ∧
    (U ≠ ∅ → S.card * (suppIn6 S U).card * fixedBoundU S U ≤ 2 ^ 7))

private def bad6 : Finset (Finset (Equiv.Perm (Fin 4)) × Finset (Fin 4)) :=
  ((inv6.powerset.filter (fun S => closed6 S = true)) ×ˢ
      ((Finset.univ : Finset (Fin 4)).powerset)).filter
    (fun p => !(checkSUb p.1 p.2))

private lemma bad6_card : bad6.card = 0 := by
  decide +kernel

private lemma checkSUb_all :
    ∀ S ∈ inv6.powerset.filter (fun S => closed6 S = true), ∀ U : Finset (Fin 4),
      checkSUb S U = true := by
  intro S hS U
  have hU : U ∈ (Finset.univ : Finset (Fin 4)).powerset :=
    Finset.mem_powerset.mpr (Finset.subset_univ U)
  have hnotmem : (S, U) ∉ bad6 := by
    have hbad : bad6 = ∅ := Finset.card_eq_zero.mp bad6_card
    rw [hbad]
    exact Finset.notMem_empty _
  by_contra hne
  apply hnotmem
  rw [bad6, Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨hS, hU⟩, ?_⟩
  simp only [Bool.not_eq_true]
  cases hc : checkSUb S U with
  | false => rfl
  | true => exact absurd hc hne

private lemma checkSU :
    ∀ S ∈ inv6.powerset.filter (fun S => closed6 S = true), ∀ U : Finset (Fin 4),
      (U = ∅ → (S.card = 1 ∨ S.card * fixedBoundU S ∅ ≤ 2 ^ 7)) ∧
      (U ≠ ∅ → S.card * (suppIn6 S U).card * fixedBoundU S U ≤ 2 ^ 7) := by
  intro S hS U
  exact of_decide_eq_true (by simpa [checkSUb] using checkSUb_all S hS U)

theorem table71 {H : Finset (Equiv.Perm (Fin 4))} (h1 : 1 ∈ H)
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H) (hsq : ∀ a ∈ H, a * a = 1)
    {C : Finset (Fin 4 → ZMod 2)} (h0 : 0 ∈ C) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (heven : ∀ x ∈ C, IsEvenVec x) (hfix : ∀ x ∈ C, ∀ a ∈ H, ∀ i, x (a i) = x i) :
    H.card * C.card * fixedBound H C ≤ 2 ^ 7 ∨ (H.card = 1 ∧ C.card = 1) := by
  classical
  have hHsub : H ⊆ inv6 := by
    intro a ha
    rw [inv6, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hsq a ha⟩
  have hHclosed : closed6 H = true := by
    rw [closed6, decide_eq_true_eq]
    exact hmul
  have hHmem : H ∈ inv6.powerset.filter (fun S => closed6 S = true) := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hHsub, hHclosed⟩
  have hCsub : C ⊆ fixedEven6 H := by
    intro x hx
    rw [fixedEven6, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, heven x hx, fun a ha i => hfix x hx a ha i⟩
  have hCsubU : C ⊆ suppIn6 H (suppUnion C) := by
    intro x hx
    rw [suppIn6, Finset.mem_filter]
    refine ⟨hCsub hx, ?_⟩
    intro i hxi
    rw [suppUnion, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨x, hx, hxi⟩⟩
  have hCcard : C.card ≤ (suppIn6 H (suppUnion C)).card := Finset.card_le_card hCsubU
  have hcheck := checkSU H hHmem (suppUnion C)
  by_cases hU : suppUnion C = ∅
  · have hCeq : C = {0} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨h0, ?_⟩
      intro x hx
      funext i
      by_contra hxi
      have hmem : i ∈ suppUnion C := by
        rw [suppUnion, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, ⟨x, hx, hxi⟩⟩
      rw [hU] at hmem
      exact Finset.notMem_empty i hmem
    have hCcard1 : C.card = 1 := by rw [hCeq, Finset.card_singleton]
    rcases hcheck.1 hU with hScard1 | hle
    · exact Or.inr ⟨hScard1, hCcard1⟩
    · refine Or.inl ?_
      rw [fixedBound_eq_fixedBoundU, hU, hCcard1]
      simpa using hle
  · refine Or.inl ?_
    have hle := hcheck.2 hU
    calc
      H.card * C.card * fixedBound H C
          = H.card * C.card * fixedBoundU H (suppUnion C) := by
            rw [fixedBound_eq_fixedBoundU]
      _ ≤ H.card * (suppIn6 H (suppUnion C)).card * fixedBoundU H (suppUnion C) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hCcard)
      _ ≤ 2 ^ 7 := hle

end CFSG.OddStandard.SmallF3.Omega
