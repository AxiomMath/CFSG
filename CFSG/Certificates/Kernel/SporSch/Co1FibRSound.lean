module

public import Certificates.Data.Kernel.SporSch.Co1Full
public import CFSG.Certificates.Kernel.SporSch.Co1VOrbProved
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.VOrb

theorem atK_eq_memK {S T : Nat → Nat} {n NS L : Nat} (hn : n < 131072) (hL : n ≤ NS * L)
    (hp : ∀ s < NS, permSl S T n (s * L) L = true) {v r : Nat} (hb : brK T S n v r = true) :
    atK T S n v r = memK T S n v := by
  unfold brK at hb
  rw [Orb.bAnd_eq, Orb.bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Orb.bIf_eq, Orb.bIf_eq] at hb
  simp only [Nat.ble_eq, Nat.blt_eq, Nat.beq_eq] at hb
  obtain ⟨hrn, hlo, hhi⟩ := hb
  rw [Bool.eq_iff_iff, memK_iff hn hL hp v]
  unfold atK
  simp only [Orb.bIf_eq, Nat.blt_eq]
  constructor
  · intro h
    by_cases hr : r < n
    · rw [ite_eq_left hr] at h
      exact ⟨msK S r, (perm_at hL hp hr).1, Nat.eq_of_beq_eq_true h⟩
    · rw [ite_eq_right hr] at h
      exact absurd h Bool.false_ne_true
  · rintro ⟨i, hi, e⟩
    obtain ⟨-, hq, -, hq4, -⟩ := perm_at hL hp hi
    have hv : ptK T (msK S (invK S i)) = v := by rw [hq4, e]
    have hm := sorted_mono hL hp
    have hrq : r ≤ invK S i := by
      by_contra hc
      have h0 : r ≠ 0 := by omega
      rw [ite_eq_right h0] at hlo
      have h1 : ptK T (msK S (r - 1)) < v := Nat.blt_eq.mp hlo
      rcases Nat.lt_or_eq_of_le (Nat.le_sub_one_of_lt (Nat.lt_of_not_le hc)) with h2 | h2
      · have := hm _ _ h2 (by omega)
        omega
      · rw [← h2] at h1
        omega
    have hr : r < n := by omega
    rw [ite_eq_left hr] at hhi ⊢
    have h3 := Nat.ble_eq.mp hhi
    rcases Nat.lt_or_eq_of_le hrq with h2 | h2
    · have := hm _ _ h2 hq
      omega
    · rw [h2, hv]
      exact Nat.beq_eq.mpr rfl

theorem cntStepR_ge {T S R : Nat → Nat} {n w k c : Nat} (hc : failC ≤ c) :
    failC ≤ cntStepR T S R n w k c := by
  unfold cntStepR
  simp only [Orb.nIf_eq, Orb.strictN_eq]
  split_ifs <;> omega

theorem cntStepR_eq {S T R : Nat → Nat} {n NS L : Nat} (hn : n < 131072) (hL : n ≤ NS * L)
    (hp : ∀ s < NS, permSl S T n (s * L) L = true) {w k c : Nat}
    (h : cntStepR T S R n w k c < failC) :
    cntStepR T S R n w k c =
      nIf(Nat.blt k n, nIf(memK T S n (Nat.xor (ptK T k) w), Nat.succ c, c), c) := by
  unfold cntStepR at h ⊢
  simp only [Orb.strictN_eq] at h ⊢
  cases hk : Nat.blt k n
  · rfl
  · rw [hk] at h
    cases hb : brK T S n (Nat.xor (ptK T k) w) (msK R k)
    · rw [hb] at h
      exact absurd h (Nat.lt_irrefl _)
    · change nIf(atK T S n (Nat.xor (ptK T k) w) (msK R k), Nat.succ c, c) = _
      rw [atK_eq_memK hn hL hp hb]

theorem foldUp_of_lt (f g : Nat → Nat → Nat) (hge : ∀ d c, failC ≤ c → failC ≤ f d c)
    (heq : ∀ d c, f d c < failC → f d c = g d c) :
    ∀ len c, foldUp len f c < failC → foldUp len f c = foldUp len g c := by
  intro len c
  rw [Orb.foldUp_eq, Orb.foldUp_eq]
  induction len with
  | zero => intro _; rfl
  | succ L ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    intro h
    have hprev : (List.range L).foldl (fun s i => f i s) c < failC := by
      by_contra hc
      exact absurd (hge L _ (Nat.le_of_not_lt hc)) (Nat.not_le_of_lt h)
    rw [heq L _ h, ih hprev]

theorem cntSl_of_R {S T R : Nat → Nat} {n NS L : Nat} (hn : Nat.blt n 131072 = true)
    (hL : Nat.ble n (NS * L) = true) (hp : ∀ s < NS, permSl S T n (s * L) L = true)
    {w lo len c₀ c₁ : Nat} (h : cntSlR T S R n w lo len c₀ c₁ = true) :
    cntSl T S n w lo len c₀ c₁ = true := by
  have hn' := Nat.blt_eq.mp hn
  have hL' := Nat.ble_eq.mp hL
  unfold cntSlR at h
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have e := Nat.eq_of_beq_eq_true h2
  unfold cntSl
  rw [← foldUp_of_lt _ _ (fun d c hc => cntStepR_ge hc)
    (fun d c hc => by rw [Orb.strictN_eq]; exact cntStepR_eq hn' hL' hp hc) len c₀
    (e ▸ Nat.blt_eq.mp h1)]
  exact h2

end CFSG.KS.SporSch.M24

end
