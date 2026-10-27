module

public import Certificates.Data.Kernel.S1277K589102E16
public import CFSG.Certificates.Kernel.S1277K589102Sound
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.L34K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
open CFSG.KLie.CT (andB orB notB)

theorem anyK_iff {N : Nat} {f : Nat → Bool} : anyK N f = true ↔ ∃ i < N, f i = true := by
  unfold anyK
  rw [CFSG.KC.L34KSnd.notB_iff]
  constructor
  · intro h
    by_contra hne
    have hall : allN N (fun i => CFSG.KLie.CT.notB (f i)) = true :=
      CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => by
        rw [CFSG.KC.L34KSnd.notB_iff]
        cases e : f i
        · rfl
        · exact absurd ⟨i, hi, e⟩ hne
    rw [h] at hall
    exact Bool.false_ne_true hall
  · rintro ⟨i, hi, e⟩
    cases h : allN N (fun j => CFSG.KLie.CT.notB (f j))
    · rfl
    · have := CFSG.KC.L34KSnd.notB_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 h i hi)
      rw [e] at this
      exact absurd this (by decide)

theorem cntK_eq (N : Nat) (f : Nat → Bool) : cntK N f = ((List.range N).filter f).length := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change Nat.add (cntK N f) (Bool.rec (motive := fun _ => Nat) 0 1 (f N)) = _
    rw [List.range_succ, List.filter_append, List.length_append, ← ih]
    cases hf : f N <;> simp [hf]

private theorem allT {N : Nat} {f : Nat → Bool} (h : allN N f = true) : ∀ i < N, f i = true :=
  CFSG.KS.Raw.Orb.allN_iff.1 h

theorem e16K_sound {N NS : Nat} {E B K ST : Nat → Nat} (h : e16K N E B K NS ST = true) :
    K 0 = pidn 42 6 ∧
    (∀ i < 5, ∃ s < NS, ST s = K i) ∧
    (∀ a < N, ∃ s < NS, ST s = B a) ∧
    (∀ a < N, ∀ b < N, pc42 (B a) (B b) = pc42 (B b) (B a)) ∧
    (∀ a < N, pc42 (B a) (B a) = pidn 42 6) ∧
    ((List.range N).filter fun a => inK N E (B a)).length = 4 ∧
    (∀ b < N, ∀ e < N, ∃ y < N, pc42 (B b) (E e) = pc42 (E y) (B b)) ∧
    (∀ b < N, ∀ e < N, ∃ y < N, pc42 (E e) (B b) = pc42 (B b) (E y)) ∧
    (∀ k < 5, ∀ b < N, ∃ y < N, pc42 (K k) (B b) = pc42 (B y) (K k)) ∧
    (∀ k < 5, ∀ b < N, ∃ y < N, pc42 (B b) (K k) = pc42 (K k) (B y)) ∧
    ∀ i < 5, ∀ j < 5, i ≠ j → ∀ x < N, B x ≠ pidn 42 6 →
      (∃ a < N, pc42 (B x) (K i) = pc42 (K i) (E a)) →
      (∃ a < N, pc42 (B x) (K j) = pc42 (K j) (E a)) → False := by
  unfold e16K at h
  obtain ⟨h0, h⟩ := CFSG.KC.L34KSnd.andB_iff.1 h
  obtain ⟨h1, h⟩ := CFSG.KC.L34KSnd.andB_iff.1 h
  obtain ⟨h2, h⟩ := CFSG.KC.L34KSnd.andB_iff.1 h
  obtain ⟨h3, h⟩ := CFSG.KC.L34KSnd.andB_iff.1 h
  obtain ⟨h4, h⟩ := CFSG.KC.L34KSnd.andB_iff.1 h
  obtain ⟨h5, h⟩ := CFSG.KC.L34KSnd.andB_iff.1 h
  obtain ⟨h6, h⟩ := CFSG.KC.L34KSnd.andB_iff.1 h
  obtain ⟨h7, h⟩ := CFSG.KC.L34KSnd.andB_iff.1 h
  obtain ⟨h8, h⟩ := CFSG.KC.L34KSnd.andB_iff.1 h
  obtain ⟨h9, h10⟩ := CFSG.KC.L34KSnd.andB_iff.1 h
  refine ⟨Nat.eq_of_beq_eq_true h0, fun i hi => inK_iff.1 (allT h1 i hi),
    fun a ha => inK_iff.1 (allT h2 a ha),
    fun a ha b hb => Nat.eq_of_beq_eq_true (allT (allT h3 a ha) b hb),
    fun a ha => Nat.eq_of_beq_eq_true (allT h4 a ha), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← cntK_eq]
    exact Nat.eq_of_beq_eq_true h5
  · intro b hb e he
    obtain ⟨y, hy, ey⟩ := anyK_iff.1 (allT (allT h6 b hb) e he)
    exact ⟨y, hy, Nat.eq_of_beq_eq_true ey⟩
  · intro b hb e he
    obtain ⟨y, hy, ey⟩ := anyK_iff.1 (allT (allT h7 b hb) e he)
    exact ⟨y, hy, Nat.eq_of_beq_eq_true ey⟩
  · intro k hk b hb
    obtain ⟨y, hy, ey⟩ := anyK_iff.1 (allT (allT h8 k hk) b hb)
    exact ⟨y, hy, Nat.eq_of_beq_eq_true ey⟩
  · intro k hk b hb
    obtain ⟨y, hy, ey⟩ := anyK_iff.1 (allT (allT h9 k hk) b hb)
    exact ⟨y, hy, Nat.eq_of_beq_eq_true ey⟩
  · intro i hi j hj hij x hx hxne ⟨a, ha, ea⟩ ⟨a', ha', ea'⟩
    rcases CFSG.KC.L34KSnd.orB_iff.1 (allT (allT h10 i hi) j hj) with h11 | h11
    · exact hij (Nat.eq_of_beq_eq_true h11)
    rcases CFSG.KC.L34KSnd.orB_iff.1 (allT h11 x hx) with h12 | h12
    · exact hxne (Nat.eq_of_beq_eq_true h12)
    have hi' : inConjK N E (B x) (K i) = true := anyK_iff.2 ⟨a, ha, by rw [ea, Nat.beq_refl]⟩
    have hj' : inConjK N E (B x) (K j) = true := anyK_iff.2 ⟨a', ha', by rw [ea', Nat.beq_refl]⟩
    rw [CFSG.KC.L34KSnd.notB_iff, hi', hj'] at h12
    exact absurd h12 (by decide)

end CFSG.KC.L34K

end
