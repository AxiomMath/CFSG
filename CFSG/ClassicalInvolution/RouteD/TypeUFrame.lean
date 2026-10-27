module

public import CFSG.ClassicalInvolution.RouteD.TypeAFrame
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Frame

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary Module Matrix
open scoped MatrixGroups

section Columns

variable {F : Type} [Field F] {N : ℕ} {I : ℕ → Matrix (Fin N) (Fin N) F} {k : ℕ}

@[expose] def chainFamIdx (N k : ℕ) (j : Fin N) : Option (Fin (k + 1)) :=
  if h : j.val < k + 1 then some ⟨j.val, h⟩ else none

theorem IsInvChain.frame_of_chainFam_columns (h2 : (2 : F) ≠ 0) (hI : IsInvChain I k) (hk : 2 ≤ k)
    (P : Matrix (Fin N) (Fin N) F)
    (hcol : ∀ j : Fin N, (fun a => P a j) ∈ chainFam I k (chainFamIdx N k j))
    (hcol0 : ∀ j : Fin N, (fun a => P a j) ≠ 0) :
    (∀ a < k, I a * P = P * negBlock F N a) ∧
      ∀ J : Matrix (Fin N) (Fin N) F, J * J = 1 → (∀ a < k, J * I a = I a * J) →
        eigSpace J (-1) ≤ chainFix I k → finrank F (eigSpace J (-1)) = N - (k + 1) →
          J * P = P * negTail F N k := by
  obtain ⟨hkN, hfix⟩ := hI.finrank_chainFix h2 hk
  set col : Fin N → (Fin N → F) := fun j a => P a j with hcolDef
  have hact : ∀ a < k, ∀ j : Fin N, I a *ᵥ col j = chainSign F a j.val • col j := by
    intro a ha j
    by_cases hj : j.val < k + 1
    · have h1 : col j ∈ chainEig I k j.val := by
        have := hcol j
        simp only [chainFamIdx, hj, dite_true] at this
        exact this
      exact mem_chainEig.mp h1 ⟨a, ha⟩
    · have h1 : col j ∈ chainFix I k := by
        have := hcol j
        simp only [chainFamIdx, hj, dite_false] at this
        exact this
      rw [mem_chainFix.mp h1 ⟨a, ha⟩, chainSign_of_not_mem (by omega), one_smul]
  refine ⟨?_, ?_⟩
  · intro a ha
    ext x j
    have := congr_fun (hact a ha j) x
    rw [Matrix.mulVec] at this
    rw [negBlock_eq_diagonal, Matrix.mul_diagonal]
    simp only [Matrix.mul_apply]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, col] at this
    rw [this]
    unfold chainSign
    by_cases hj : (j : ℕ) = a ∨ (j : ℕ) = a + 1
    · have h1 : a ≤ (j : ℕ) ∧ (j : ℕ) < a + 2 := by omega
      simp only [hj, h1, and_self, ↓reduceIte]; ring
    · have h1 : ¬ (a ≤ (j : ℕ) ∧ (j : ℕ) < a + 2) := by omega
      simp only [hj, h1, ↓reduceIte]; ring
  · intro J hJ hcomm hneg hdim
    have hinvJ : ∀ j : Fin N, ∀ v ∈ chainFam I k (chainFamIdx N k j),
        J *ᵥ v ∈ chainFam I k (chainFamIdx N k j) := by
      intro j v hv
      by_cases hj : j.val < k + 1
      · have hv' : v ∈ chainEig I k j.val := by
          simp only [chainFamIdx, hj, dite_true] at hv
          exact hv
        have : J *ᵥ v ∈ chainEig I k j.val := by
          rw [mem_chainEig] at hv' ⊢
          intro a
          rw [mulVec_mulVec, ← hcomm a a.2, ← mulVec_mulVec, hv' a, Matrix.mulVec_smul]
        simp only [chainFamIdx, hj, dite_true]
        exact this
      · have hv' : v ∈ chainFix I k := by
          simp only [chainFamIdx, hj, dite_false] at hv
          exact hv
        have : J *ᵥ v ∈ chainFix I k := by
          rw [mem_chainFix] at hv' ⊢
          intro a
          rw [mulVec_mulVec, ← hcomm a a.2, ← mulVec_mulVec, hv' a]
        simp only [chainFamIdx, hj, dite_false]
        exact this
    have hJcol : ∀ j : Fin N, J *ᵥ col j = (if k < j.val then (-1 : F) else 1) • col j := by
      intro j
      by_cases hj : j.val < k + 1
      · have hline : finrank F (chainEig I k j.val) = 1 := hI.finrank_chainEig h2 hk (by omega)
        have hmem : col j ∈ chainEig I k j.val := by
          have := hcol j
          simp only [chainFamIdx, hj, dite_true] at this
          exact this
        have hinv : ∀ v ∈ chainEig I k j.val, J *ᵥ v ∈ chainEig I k j.val := by
          intro v hv
          have := hinvJ j v (by simp only [chainFamIdx, hj, dite_true]; exact hv)
          simp only [chainFamIdx, hj, dite_true] at this
          exact this
        rcases line_le_eigSpace hJ hline hinv with h | h
        · have h1 := mem_eigSpace_one.mp (h hmem)
          have hk' : ¬ k < j.val := by omega
          rw [h1]; simp [hk']
        · exfalso
          have h1 : col j ∈ chainFix I k := hneg (h hmem)
          obtain ⟨a, ha, hja⟩ := exists_chainNeg (k := k) (j := j.val) (by omega) (by omega)
          have e1 := mem_chainEig.mp hmem ⟨a, ha⟩
          have e2 := mem_chainFix.mp h1 ⟨a, ha⟩
          have e3 : col j = -col j := by
            have := e1
            simp only at this e2
            rw [e2, chainSign_of_mem hja, neg_one_smul] at this
            exact this
          apply hcol0 j
          have h2' : (2 : F) • col j = 0 := by
            rw [two_smul]
            nth_rewrite 1 [e3]
            exact neg_add_cancel _
          exact (smul_eq_zero.mp h2').resolve_left h2
      · have heq : eigSpace J (-1) = chainFix I k :=
          Submodule.eq_of_le_of_finrank_eq hneg (by rw [hdim, hfix])
        have hmem : col j ∈ chainFix I k := by
          have := hcol j
          simp only [chainFamIdx, hj, dite_false] at this
          exact this
        rw [← heq] at hmem
        have hk' : k < j.val := by omega
        rw [mem_eigSpace_neg_one.mp hmem]; simp [hk']
    ext x j
    have := congr_fun (hJcol j) x
    rw [Matrix.mulVec] at this
    rw [negTail, Matrix.mul_diagonal]
    simp only [Matrix.mul_apply]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, col] at this
    rw [this]
    split_ifs <;> ring

end Columns

section Orthogonality

variable {K : Type} [Field K] {σ : K ≃+* K} {N : ℕ}

theorem chainChar_cases_su (k : ℕ) (o : Option (Fin (k + 1))) (a : Fin k) :
    chainChar K k o a = 1 ∨ chainChar K k o a = -1 := by
  cases o with
  | none => exact Or.inl rfl
  | some j =>
    simp only [chainChar, chainSign]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem chainFam_mulVec_eq {I : ℕ → Matrix (Fin N) (Fin N) K} {k : ℕ}
    {o : Option (Fin (k + 1))} {v : Fin N → K} (hv : v ∈ chainFam I k o) (a : Fin k) :
    I a *ᵥ v = chainChar K k o a • v := by
  cases o with
  | none =>
    have := mem_chainFix.mp hv a
    rw [this]
    exact (one_smul K v).symm
  | some j => exact mem_chainEig.mp hv a

theorem orth_chainFam_su (h2 : (2 : K) ≠ 0) (u : ℕ → SUid σ N) {k : ℕ} (hk : 2 ≤ k)
    {o o' : Option (Fin (k + 1))} (h : o ≠ o') :
    Orth σ (chainFam (fun a => suMat (u a)) k o) (chainFam (fun a => suMat (u a)) k o') := by
  intro v hv w hw
  obtain ⟨a, ha⟩ : ∃ a : Fin k, chainChar K k o a ≠ chainChar K k o' a := by
    by_contra hcon
    push Not at hcon
    exact h (chainChar_injective h2 hk (funext hcon))
  refine herm_eq_zero_of_eigen (u a) (chainFam_mulVec_eq hv a)
    (chainFam_mulVec_eq hw a) ?_
  have hne := neg_one_ne_one_of_two_ne_zero h2
  rcases chainChar_cases_su (K := K) k o a with h1 | h1 <;>
    rcases chainChar_cases_su (K := K) k o' a with h3 | h3 <;>
    rw [h1, h3] at ha ⊢
  · exact absurd rfl ha
  · rw [map_one, one_mul]
    exact hne
  · rw [map_neg, map_one, neg_one_mul]
    exact hne
  · exact absurd rfl ha

theorem nondeg_chainFam_su (h2 : (2 : K) ≠ 0) (u : ℕ → SUid σ N) {k : ℕ}
    (hI : IsInvChain (fun a => suMat (u a)) k) (hk : 2 ≤ k) (o : Option (Fin (k + 1))) :
    Nondeg σ (chainFam (fun a => suMat (u a)) k o) :=
  nondeg_of_orth_of_iSup_eq_top _ (hI.iSup_eq_top h2 hk) (fun _ _ h => orth_chainFam_su h2 u hk h) o

end Orthogonality

section Frame

variable {K : Type} [Field K] {σ : K ≃+* K} {N : ℕ}

theorem IsInvChain.exists_su_frame (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) ≠ 0)
    {u : ℕ → SUid σ N} {k : ℕ} (hI : IsInvChain (fun a => suMat (u a)) k) (hk : 2 ≤ k) :
    k + 1 ≤ N ∧ ∃ P : SUid σ N,
      (∀ a < k, suMat (u a) * suMat P = suMat P * negBlock K N a) ∧
      ∀ J : Matrix (Fin N) (Fin N) K, J * J = 1 → (∀ a < k, J * suMat (u a) = suMat (u a) * J) →
        eigSpace J (-1) ≤ chainFix (fun a => suMat (u a)) k →
          finrank K (eigSpace J (-1)) = N - (k + 1) → J * suMat P = suMat P * negTail K N k := by
  obtain ⟨hkN, hfix⟩ := hI.finrank_chainFix h2 hk
  refine ⟨hkN, ?_⟩
  have hε : ∀ s, Nat.card {j // chainFamIdx N k j = s} =
      finrank K (chainFam (fun a => suMat (u a)) k s) := by
    rintro (_ | l)
    · have e : {j : Fin N // chainFamIdx N k j = none} ≃ {j : Fin N // k + 1 ≤ j.val} :=
        Equiv.subtypeEquivRight fun j => by
          simp only [chainFamIdx]
          split_ifs with h <;> simp <;> omega
      rw [Nat.card_congr e, card_fin_val_ge hkN]
      exact hfix.symm
    · have e : {j : Fin N // chainFamIdx N k j = some l} ≃ {j : Fin N // j.val = l.val} :=
        Equiv.subtypeEquivRight fun j => by
          simp only [chainFamIdx]
          split_ifs with h
          · simp [Fin.ext_iff]
          · simp only [false_iff]
            omega
      rw [Nat.card_congr e, card_fin_val_eq (by omega)]
      exact (hI.finrank_chainEig h2 hk (by omega)).symm
  obtain ⟨g, hg⟩ := exists_su_adapted hσ (by omega : 0 < N) (chainFam (fun a => suMat (u a)) k)
    (nondeg_chainFam_su h2 u hI hk) (fun _ _ h => orth_chainFam_su h2 u hk h) (chainFamIdx N k) hε
  have hcol : ∀ j : Fin N, (fun a => suMat g a j) ∈
      chainFam (fun a => suMat (u a)) k (chainFamIdx N k j) := by
    intro j
    have := hg j
    rw [suMat_smul, Matrix.mulVec_single_one] at this
    exact this
  have hcol0 : ∀ j : Fin N, (fun a => suMat g a j) ≠ 0 := by
    intro j h0
    have hinv := suMat_inv_mul_suMat g
    have hmv : suMat g *ᵥ (Pi.single j (1 : K)) = fun a => suMat g a j := by
      ext a
      simp
    have h1 : (suMat g⁻¹ * suMat g) *ᵥ (Pi.single j (1 : K)) = 0 := by
      rw [← mulVec_mulVec, hmv, h0, Matrix.mulVec_zero]
    rw [hinv, Matrix.one_mulVec] at h1
    have := congr_fun h1 j
    simp at this
  exact ⟨g, hI.frame_of_chainFam_columns h2 hk (suMat g) hcol hcol0⟩

end Frame

end CFSG.ClassicalInvolution.RouteD
