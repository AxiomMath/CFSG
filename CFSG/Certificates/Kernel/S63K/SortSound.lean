module

public import Certificates.Data.Kernel.S63K.Sorted
public import Certificates.Data.Kernel.SporSch.Co1Bfs
public import CFSG.Certificates.Kernel.SporSch.Co1MatLemmas

public section

namespace CFSG.KC.S63K

open CFSG.KS.SporSch.M24 CFSG.KC.Enum CFSG.KS

variable {P S : ℕ → ℕ} {N : ℕ}

theorem dist_parts (h : bfsDistK P S N = true) :
    (∀ k < N, S k < N) ∧ ∀ a b, a < b → b < N → P (S a) < P (S b) := by
  unfold bfsDistK at h
  rw [MatL.allN_iff] at h
  have h' : ∀ k < N, S k < N ∧ (k + 1 = N ∨ P (S k) < P (S (k + 1))) := by
    intro k hk
    have := h k hk
    simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at this
    refine ⟨this.1, ?_⟩
    have h3 := this.2.2
    by_cases hk1 : k + 1 = N
    · exact Or.inl hk1
    · right
      have hb : Nat.beq (Nat.succ k) N = false := by
        cases e : Nat.beq (Nat.succ k) N
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) hk1
      rw [hb] at h3
      simpa using h3
  refine ⟨fun k hk => (h' k hk).1, ?_⟩
  intro a b hab hb
  induction b with
  | zero => omega
  | succ b ih =>
    have step : P (S b) < P (S (b + 1)) := (h' b (by omega)).2.resolve_left (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with hab | rfl
    · exact Nat.lt_trans (ih hab (by omega)) step
    · exact step

theorem surj_of (h : bfsDistK P S N = true) : ∀ w < N, ∃ k < N, S k = w := by
  obtain ⟨hS, hst⟩ := dist_parts h
  let f : Fin N → Fin N := fun k => ⟨S k.val, hS k.val k.2⟩
  have hinj : Function.Injective f := by
    intro a b e
    have e' : S a.val = S b.val := congrArg Fin.val e
    apply Fin.ext
    rcases Nat.lt_trichotomy a.val b.val with hab | hab | hab
    · have := hst _ _ hab b.2; rw [e'] at this; omega
    · exact hab
    · have := hst _ _ hab a.2; rw [e'] at this; omega
  intro w hw
  obtain ⟨k, hk⟩ := Finite.surjective_of_injective hinj ⟨w, hw⟩
  exact ⟨k.val, k.2, congrArg Fin.val hk⟩

theorem memAt_zero (h : bfsDistK P S N = true) {y k : ℕ} (hm : memAt P S N y k = 0) :
    ∀ w < N, P w ≠ y := by
  obtain ⟨-, hst⟩ := dist_parts h
  unfold memAt at hm
  cases hc : (Nat.blt k N && Nat.ble (P (S k)) y && (Nat.beq (k + 1) N || Nat.blt y (P (S (k + 1)))))
  · rw [hc] at hm
    simp at hm
  · rw [hc] at hm
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at hc
    obtain ⟨⟨hk, hle⟩, hnx⟩ := hc
    have hne : P (S k) ≠ y := by
      intro e
      rw [e, Nat.beq_refl] at hm
      simp at hm
    intro w hw e
    obtain ⟨k', hk', rfl⟩ := surj_of h w hw
    rcases Nat.lt_trichotomy k' k with hl | rfl | hl
    · have := hst _ _ hl hk
      omega
    · exact hne e
    · rcases hnx with hn | hn
      · omega
      · have : P (S (k + 1)) ≤ P (S k') := by
          rcases Nat.lt_or_ge (k + 1) k' with h2 | h2
          · exact Nat.le_of_lt (hst _ _ h2 hk')
          · have : k + 1 = k' := by omega
            rw [this]
        omega

theorem memS_zero (h : bfsDistK P S N = true) {y : ℕ} (hm : memS P S N y = 0) :
    ∀ w < N, P w ≠ y := by
  obtain ⟨-, hst⟩ := dist_parts h
  unfold memS at hm
  cases hb : Nat.blt y (P (S 0))
  · rw [hb] at hm
    exact memAt_zero h hm
  · rw [Nat.blt_eq] at hb
    intro w hw e
    obtain ⟨k', hk', rfl⟩ := surj_of h w hw
    rcases Nat.eq_zero_or_pos k' with h0 | h0
    · rw [h0] at e
      omega
    · have := hst 0 k' h0 hk'
      omega

theorem memS_one (h : bfsDistK P S N = true) {y : ℕ} (hm : memS P S N y = 1) :
    ∃ w < N, P w = y := by
  obtain ⟨hS, -⟩ := dist_parts h
  unfold memS at hm
  cases hb : Nat.blt y (P (S 0))
  · rw [hb] at hm
    change memAt P S N y (bsK P S y 32 0 N) = 1 at hm
    generalize bsK P S y 32 0 N = k at hm
    unfold memAt at hm
    cases hc : (Nat.blt k N && Nat.ble (P (S k)) y && (Nat.beq (k + 1) N || Nat.blt y (P (S (k + 1)))))
    · rw [hc] at hm
      simp at hm
    · rw [hc] at hm
      simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq] at hc
      cases he : Nat.beq (P (S k)) y
      · rw [he] at hm
        simp at hm
      · exact ⟨S k, hS k hc.1.1, Nat.eq_of_beq_eq_true he⟩
  · rw [hb] at hm
    simp at hm

end CFSG.KC.S63K

end
