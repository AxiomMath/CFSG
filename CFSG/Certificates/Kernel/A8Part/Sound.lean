module

public import Certificates.Data.Kernel.A8Part.Defs
public import CFSG.Certificates.Kernel.CosetLat.Sound
public import CFSG.Certificates.Kernel.Misc.PermClosWSound

public section

namespace CFSG.KC.A8Part

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos

@[expose] def maskSet (S : ℕ) : Finset (Fin 8) := Finset.univ.filter fun i => S.testBit i = true

theorem bitN_eq (S a : ℕ) : bitN S a = if S.testBit a then 1 else 0 := by
  change (S >>> a) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (S / 2 ^ a) with h | h <;> simp [h]

theorem psAt_sound {S : ℕ} (g : Equiv.Perm (Fin 8))
    (h : psAt S (CFSG.KC.Misc.ClosW.wcode 4 g) = true) :
    (∀ i, g i ∈ maskSet S ↔ i ∈ maskSet S) ∨ (∀ i, g i ∈ maskSet S ↔ i ∉ maskSet S) := by
  have hw : 8 < 2 ^ 4 := by decide
  have h' : orB (allN 8 fun i => Nat.beq (bitN S (CFSG.KC.Enum.pg 4 (CFSG.KS.mask 4)
      (CFSG.KC.Misc.ClosW.wcode 4 g) i)) (bitN S i))
      (allN 8 fun i => notB (Nat.beq (bitN S (CFSG.KC.Enum.pg 4 (CFSG.KS.mask 4)
        (CFSG.KC.Misc.ClosW.wcode 4 g) i)) (bitN S i))) = true := h
  have hor : ∀ a b : Bool, orB a b = true → a = true ∨ b = true := by
    intro a b
    cases a <;> simp [orB]
  simp only [maskSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hor _ _ h' with ha | ha
  · left
    intro i
    have e := Nat.eq_of_beq_eq_true ((allN_iff _ _).1 ha i i.isLt)
    rw [CFSG.KC.Misc.ClosW.pg_wcode hw g i, bitN_eq, bitN_eq] at e
    by_cases h1 : S.testBit (g i) <;> by_cases h2 : S.testBit i <;> simp_all
  · right
    intro i
    have e := Nat.ne_of_beq_eq_false
      (CFSG.KC.CosetLat.notB_eq_true ((allN_iff _ _).1 ha i i.isLt))
    rw [CFSG.KC.Misc.ClosW.pg_wcode hw g i, bitN_eq, bitN_eq] at e
    by_cases h1 : S.testBit (g i) <;> by_cases h2 : S.testBit i <;> simp_all

variable {Γ : Type*} [Group Γ] {enc : Γ → ℕ} {M : ℕ → ℕ → ℕ} {one : ℕ}

theorem trans3_sound (henc : ClosEnc enc M one) {S H : Subgroup Γ} {r : ℕ → Γ}
    {nS nR nH nU : ℕ} {ES RC EH EU UR : ℕ → ℕ}
    (hS : ∀ k < nS, ∃ g ∈ S, enc g = ES k) (hH : ∀ k < nH, ∃ g ∈ H, enc g = EH k)
    (hR : ∀ j < nR, enc (r j) = RC j)
    (h : ∀ i < nU, trans3At M ES nS RC nR EH nH EU UR i = true) :
    ∀ i < nU, ∀ u : Γ, enc u = EU i → ∃ s ∈ S, ∃ j < nR, ∃ y ∈ H, s * u = r j * y := by
  intro i hi u hu
  have h' := h i hi
  unfold trans3At at h'
  rw [letB_eq, letB_eq, letB_eq, letB_eq] at h'
  obtain ⟨hs, h'⟩ := andB_eq_true h'
  obtain ⟨hj, h'⟩ := andB_eq_true h'
  obtain ⟨hy, h'⟩ := andB_eq_true h'
  obtain ⟨s, hsS, hse⟩ := hS _ (Nat.blt_eq.mp hs)
  obtain ⟨y, hyH, hye⟩ := hH _ (Nat.blt_eq.mp hy)
  refine ⟨s, hsS, _, Nat.blt_eq.mp hj, y, hyH, henc.inj ?_⟩
  rw [henc.enc_mul, henc.enc_mul, hse, hu, hR _ (Nat.blt_eq.mp hj), hye]
  exact Nat.eq_of_beq_eq_true h'

theorem cos_sound (henc : ClosEnc enc M one) {S T : Subgroup Γ} {x : Γ} {nS nP : ℕ}
    {TE TP CS : ℕ → ℕ} (hSx : ∀ g ∈ S, ∃ k < nS, enc g = TE k)
    (hP : ∀ m < nP, ∃ g ∈ T, enc g = TP m)
    (h : ∀ k < nS, cosAt M TE TP nP (enc x) CS k = true) : ∀ g ∈ S, g ∈ T ∨ g * x⁻¹ ∈ T := by
  intro g hg
  obtain ⟨k, hk, hke⟩ := hSx g hg
  have h' := h k hk
  unfold cosAt at h'
  rw [letB_eq, letB_eq] at h'
  obtain ⟨hm, h'⟩ := andB_eq_true h'
  obtain ⟨t, htT, hte⟩ := hP _ (Nat.blt_eq.mp hm)
  have key : ∀ (c : Bool) (a b n : ℕ), n = Bool.rec (motive := fun _ => ℕ) a b c →
      n = a ∨ n = b := by
    intro c a b n hn
    cases c
    · exact Or.inl hn
    · exact Or.inr hn
  rcases key _ _ _ _ (Nat.eq_of_beq_eq_true h') with e | e
  · right
    rw [← hke, ← hte, ← henc.enc_mul] at e
    rw [henc.inj e, mul_inv_cancel_right]
    exact htT
  · left
    rw [← hke, ← hte] at e
    rw [henc.inj e]
    exact htT

end CFSG.KC.A8Part

end
