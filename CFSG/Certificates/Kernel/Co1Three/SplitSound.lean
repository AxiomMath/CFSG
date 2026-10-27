module

public import CFSG.Certificates.Kernel.Co1Three.TermSound
public import Certificates.Data.Kernel.Co1Three.Split
public import CFSG.Certificates.Kernel.S63K.Pack
public import CFSG.Certificates.Kernel.SporSch.Co1StabSound
public import CFSG.Certificates.Kernel.SporSch.Co1BfsSound
public import CFSG.Sporadic.Schreier.Co1ElemThreeGroup

public section

set_option exponentiation.threshold 600

namespace CFSG.KC.Co1Leaf

open CFSG.KC.Loop CFSG.KLie.CT CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KC.Co1Cl

theorem andB_eq_true {a b : Bool} : CFSG.KLie.CT.andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [CFSG.KLie.CT.andB]

theorem orB_eq_true {a b : Bool} : CFSG.KLie.CT.orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> simp [CFSG.KLie.CT.orB]

theorem notB_eq_true {a : Bool} : CFSG.KLie.CT.notB a = true ↔ a = false := by
  cases a <;> simp [CFSG.KLie.CT.notB]

theorem allN_eq_true {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allN]
  | succ n ih =>
    change CFSG.KLie.CT.andB (f n) (allN n f) = true ↔ _
    rw [andB_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem strictN_loop (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem matK_powWK (M : Nat) : ∀ e : Nat, matK (powWK M e) = matK M ^ e
  | 0 => by
    rw [pow_zero]
    exact matK_oneK
  | e + 1 => by
    change matK (CFSG.KC.Loop.strictN (powWK M e) fun a => mulWK a M) = _
    rw [strictN_loop, matK_mulWK, matK_powWK M e, pow_succ]

theorem matK_pairK (X Y u : Nat) :
    matK (pairK X Y u) = matK X ^ (u % 3) * matK Y ^ (u / 3) := by
  rw [pairK, matK_mulWK, matK_powWK, matK_powWK]
  rfl

theorem matK_eq_mod {A B : Nat} (h : matK A = matK B) : A % 2 ^ 576 = B % 2 ^ 576 := by
  have hA := CFSG.KS.SporSch.M24.StabL.wf_unpack' A
  have hB := CFSG.KS.SporSch.M24.StabL.wf_unpack' B
  rw [← CFSG.KS.SporSch.M24.unpackR_eq_unpack] at hA hB
  exact CFSG.KC.S63K.unpackR_inj.1
    (CFSG.Sporadic.Co1Schreier.rowsMatrix_injective_of_wf hA hB h)

theorem commL_sound {F : List Nat} {X : Nat} (h : commL F X = true) :
    ∀ f ∈ F, matK f * matK X = matK X * matK f := by
  induction F with
  | nil => simp
  | cons f F ih =>
    change CFSG.KLie.CT.andB (Nat.beq (mulWK f X) (mulWK X f)) (commL F X) = true at h
    rw [andB_eq_true] at h
    intro g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · rw [← matK_mulWK, ← matK_mulWK, Nat.eq_of_beq_eq_true h.1]
    · exact ih h.2 g hg

theorem distK_sound {X Y : Nat} (h : distK X Y = true) :
    ∀ u < 9, ∀ v < 9, matK X ^ (u % 3) * matK Y ^ (u / 3) = matK X ^ (v % 3) * matK Y ^ (v / 3) →
      u = v := by
  intro u hu v hv huv
  have h1 := allN_eq_true.1 (allN_eq_true.1 h u hu) v hv
  rcases orB_eq_true.1 h1 with h2 | h2
  · exact Nat.eq_of_beq_eq_true h2
  · rw [notB_eq_true] at h2
    have e := matK_eq_mod (A := pairK X Y u) (B := pairK X Y v)
      (by rw [matK_pairK, matK_pairK, huv])
    have hp : pw2 (nat_lit 576) = 2 ^ 576 := by
      change 1 <<< 576 = 2 ^ 576
      rw [Nat.one_shiftLeft]
    rw [hp] at h2
    have h3 : Nat.beq (pairK X Y u % 2 ^ 576) (pairK X Y v % 2 ^ 576) = false := h2
    exact absurd e (Nat.ne_of_beq_eq_false h3)

theorem planeK_sound {F : List Nat} {X Y : Nat} (h : planeK F X Y = true) :
    matK X * matK Y = matK Y * matK X ∧ matK X ^ 3 = 1 ∧ matK Y ^ 3 = 1 ∧
      (∀ f ∈ F, matK f * matK X = matK X * matK f ∧ matK f * matK Y = matK Y * matK f) ∧
      ∀ u < 9, ∀ v < 9,
        matK X ^ (u % 3) * matK Y ^ (u / 3) = matK X ^ (v % 3) * matK Y ^ (v / 3) → u = v := by
  simp only [planeK, andB_eq_true] at h
  obtain ⟨hXY, hX, hY, hFX, hFY, hd⟩ := h
  refine ⟨?_, ?_, ?_, fun f hf => ⟨commL_sound hFX f hf, commL_sound hFY f hf⟩, distK_sound hd⟩
  · rw [← matK_mulWK, ← matK_mulWK, Nat.eq_of_beq_eq_true hXY]
  · rw [pow_three, ← matK_mulWK, ← matK_mulWK, Nat.eq_of_beq_eq_true hX, matK_oneK]
  · rw [pow_three, ← matK_mulWK, ← matK_mulWK, Nat.eq_of_beq_eq_true hY, matK_oneK]

end CFSG.KC.Co1Leaf

end
