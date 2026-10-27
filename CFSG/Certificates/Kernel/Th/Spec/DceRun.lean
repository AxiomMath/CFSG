module

public import CFSG.Certificates.Kernel.DceLoops
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.Th.Spec.Dce

open CFSG.KC.Loop CFSG.Certificates.DceLoop

section Run

variable {rk : ℕ → Bool} {tk ak : ℕ → ℕ → Bool} {wk : ℕ → ℕ → ℕ → Bool} {fr : ℕ → ℕ}

@[expose] def FInvT (rk : ℕ → Bool) (tk ak : ℕ → ℕ → Bool) (wk : ℕ → ℕ → ℕ → Bool)
    (fr : ℕ → ℕ) (NF S : ℕ) : Prop :=
  S = 0 ∨ ∃ i nx, S = mkSG i nx ∧ i ≤ NF ∧ ∃ nxf : ℕ → ℕ, nxf 0 = 1 ∧ nxf i = nx ∧
    ∀ i' < i, FactOK rk tk ak wk fr i' (nxf i') (nxf (i' + 1))

theorem factG_invT {NF Jf S : ℕ} (hNF : NF < 2 ^ 32) (hterm : rk (fr NF) = false)
    (h : FInvT rk tk ak wk fr NF S) : FInvT rk tk ak wk fr NF (factG rk tk ak wk fr Jf S) := by
  rcases h with rfl | ⟨i, nx, rfl, hi, nxf, hn0, hnx, hf⟩
  · exact Or.inl rfl
  have hi32 : i < 2 ^ 32 := by omega
  obtain ⟨eI, eN⟩ := mkSG_dec nx hi32
  have key : factG rk tk ak wk fr Jf (mkSG i nx) = 0 ∨ ∃ nx',
      factG rk tk ak wk fr Jf (mkSG i nx) = mkSG (i + 1) nx' ∧ FactOK rk tk ak wk fr i nx nx' := by
    unfold factG
    simp only []
    rw [eI, eN]
    cases h1 : Bool.rec (motive := fun _ => Bool) false (rk (fr i))
        (Nat.blt (nat_lit 0) (mkSG i nx))
    · exact Or.inl rfl
    rw [band_iff] at h1
    dsimp only
    cases h2 : Nat.beq (Nat.land Jf (nat_lit 3)) (nat_lit 0)
    · dsimp only
      cases h3 : Nat.beq (Nat.land Jf (nat_lit 3)) (nat_lit 1)
      · dsimp only
        cases h4 : Bool.rec (motive := fun _ => Bool) false (wk i Jf (fr i))
            (Nat.beq (Nat.land Jf (nat_lit 3)) (nat_lit 2))
        · exact Or.inl rfl
        · rw [band_iff] at h4
          exact Or.inr ⟨_, rfl, h1.2, Or.inr (Or.inr ⟨rfl, Jf, h4.2⟩)⟩
      · dsimp only
        cases h4 : ak Jf (fr i)
        · exact Or.inl rfl
        · exact Or.inr ⟨_, rfl, h1.2, Or.inr (Or.inl ⟨rfl, Jf, h4⟩)⟩
    · dsimp only
      cases h4 : tk nx (fr i)
      · exact Or.inl rfl
      · exact Or.inr ⟨_, rfl, h1.2, Or.inl ⟨rfl, h4⟩⟩
  rcases key with hz | ⟨nx', e, hfr⟩
  · exact Or.inl hz
  rw [e]
  have hiNF : i + 1 ≤ NF := by
    rcases Nat.lt_or_ge i NF with h1 | h1
    · omega
    · have h2 : i = NF := by omega
      have h3 := hfr.1
      rw [h2, hterm] at h3
      exact absurd h3 Bool.false_ne_true
  refine Or.inr ⟨i + 1, nx', rfl, hiNF, fun i' => if i' ≤ i then nxf i' else nx', by simp [hn0],
    by simp, ?_⟩
  intro i' hi'
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
  · have h1 : i' ≤ i := by omega
    have h2 : i' + 1 ≤ i := by omega
    simp only [h1, h2, ↓reduceIte]
    exact hf i' hi'
  · simp only [le_refl, ↓reduceIte, Nat.not_succ_le_self]
    rw [hnx]
    exact hfr

theorem chunkG_invT {NF : ℕ} (hNF : NF < 2 ^ 32) (hterm : rk (fr NF) = false) :
    ∀ (n J S : ℕ), FInvT rk tk ak wk fr NF S →
      FInvT rk tk ak wk fr NF (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
        (fun _ ih J S => (fun L =>
          strictN (factG rk tk ak wk fr (bitsG J (nat_lit 12) L) S)
            (ih (Nat.shiftRight J (Nat.add (nat_lit 12) L))))
          (Nat.land J (nat_lit 4095))) n J S)
  | 0, _, _, h => h
  | n + 1, J, S, h => by
    change FInvT rk tk ak wk fr NF (strictN (factG rk tk ak wk fr (bitsG J (nat_lit 12)
      (Nat.land J (nat_lit 4095))) S) (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
      (fun _ ih J S => (fun L =>
        strictN (factG rk tk ak wk fr (bitsG J (nat_lit 12) L) S)
          (ih (Nat.shiftRight J (Nat.add (nat_lit 12) L))))
        (Nat.land J (nat_lit 4095))) n (Nat.shiftRight J (Nat.add (nat_lit 12)
          (Nat.land J (nat_lit 4095))))))
    rw [strictN_eq]
    exact chunkG_invT hNF hterm n _ _
      (factG_invT (Jf := bitsG J (nat_lit 12) (Nat.land J (nat_lit 4095))) hNF hterm h)

theorem factsG_invT {NF : ℕ} (hNF : NF < 2 ^ 32) (hterm : rk (fr NF) = false) :
    ∀ (Cs : List ℕ) (S : ℕ), FInvT rk tk ak wk fr NF S →
      FInvT rk tk ak wk fr NF (factsG (factG rk tk ak wk fr) Cs S)
  | [], _, h => h
  | C :: Cs, S, h => by
    change FInvT rk tk ak wk fr NF (strictN (chunkG (factG rk tk ak wk fr) C S)
      (factsG (factG rk tk ak wk fr) Cs))
    rw [strictN_eq]
    exact factsG_invT hNF hterm Cs _
      (chunkG_invT hNF hterm (Nat.land C 255) (Nat.shiftRight C 8) S h)

theorem factsT_spec {Cs : List ℕ} {S1 NF ND : ℕ} (hNF32 : NF < 2 ^ 32)
    (hterm : rk (fr NF) = false) (hrun : factsG (factG rk tk ak wk fr) Cs (mkSG 0 1) = S1)
    (hS1 : 0 < S1) (hNF : sIG S1 = NF) (hND : sXG S1 = ND) :
    ∃ nxf : ℕ → ℕ, nxf 0 = 1 ∧ nxf NF = ND ∧
      ∀ i < NF, FactOK rk tk ak wk fr i (nxf i) (nxf (i + 1)) := by
  have h0 : FInvT rk tk ak wk fr NF (mkSG 0 1) :=
    Or.inr ⟨0, 1, rfl, Nat.zero_le _, fun _ => 1, rfl, rfl, fun i' hi' => absurd hi' (by omega)⟩
  have h1 := factsG_invT hNF32 hterm Cs _ h0
  rw [hrun] at h1
  rcases h1 with h1 | ⟨i, nx, e, hi, nxf, hn0, hnx, hf⟩
  · omega
  have hi32 : i < 2 ^ 32 := by omega
  obtain ⟨d1, d2⟩ := mkSG_dec nx hi32
  rw [← e, hNF] at d1
  rw [← e, hND] at d2
  subst d1
  subst d2
  exact ⟨nxf, hn0, hnx, hf⟩

theorem factsT_of_mk {Cs : List ℕ} {NF ND : ℕ} (hNF : NF < 2 ^ 32) (hterm : rk (fr NF) = false)
    (hrun : factsG (factG rk tk ak wk fr) Cs (mkSG 0 1) = mkSG NF ND) :
    ∃ nxf : ℕ → ℕ, (0 < NF → nxf 0 = 1 ∧ nxf NF = ND) ∧
      ∀ i < NF, FactOK rk tk ak wk fr i (nxf i) (nxf (i + 1)) := by
  by_cases h0 : NF = 0
  · exact ⟨fun _ => 0, fun h => absurd h0 (Nat.pos_iff_ne_zero.1 h),
      fun i hi => absurd hi (by omega)⟩
  · have hpos : 0 < mkSG NF ND :=
      Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero h0) Nat.left_le_or
    obtain ⟨d1, d2⟩ := mkSG_dec ND hNF
    obtain ⟨nxf, e0, eN, hf⟩ := factsT_spec hNF hterm hrun hpos d1 d2
    exact ⟨nxf, fun _ => ⟨e0, eN⟩, hf⟩

theorem factsG_of_mk {Cs : List ℕ} {NF ND : ℕ} (hNF : NF < 2 ^ 32)
    (hrun : factsG (factG rk tk ak wk fr) Cs (mkSG 0 1) = mkSG NF ND) :
    ∃ nxf : ℕ → ℕ, ∀ i < NF, FactOK rk tk ak wk fr i (nxf i) (nxf (i + 1)) := by
  by_cases h0 : NF = 0
  · exact ⟨fun _ => 0, fun i hi => absurd hi (by omega)⟩
  · have hpos : 0 < mkSG NF ND :=
      Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero h0) Nat.left_le_or
    exact factsG_spec hrun hpos (mkSG_dec ND hNF).1

end Run

theorem exists_first_tree {NF ND : ℕ} {nxf : ℕ → ℕ} (h0 : nxf 0 = 1) (hN : nxf NF = ND)
    (hND : 2 ≤ ND) (hstep : ∀ i < NF, nxf (i + 1) = nxf i ∨ nxf (i + 1) = nxf i + 1) :
    ∃ i < NF, nxf i = 1 ∧ nxf (i + 1) = 2 := by
  by_contra hno
  push_neg at hno
  have key : ∀ k ≤ NF, nxf k = 1 := by
    intro k
    induction k with
    | zero => exact fun _ => h0
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      rcases hstep k (by omega) with h | h
      · omega
      · have := hno k (by omega) h1
        omega
  have := key NF le_rfl
  omega

end CFSG.KC.Th.Spec.Dce

end
