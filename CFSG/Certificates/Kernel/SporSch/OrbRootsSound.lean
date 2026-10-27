module

public import CFSG.Certificates.Kernel.SporSch.OrbLabelsSound
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.OrbLab

open CFSG.Quasithin.RuRank3 CFSG.Sporadic.FischerOddCore.SearchSpec

variable {n : ℕ} {gens : Array (Array ℕ)} {L R P K D : ℕ → ℕ} {m : ℕ}

def ORInv (n : ℕ) (L R : ℕ → ℕ) (m s : ℕ) (st : Array ℕ × Array ℕ) : Prop :=
  (st.1.size = n ∧ st.2.size ≤ m ∧ (∀ c < m, R c < s ↔ c < st.2.size) ∧
    ∀ x < n, st.1[x]! = if R (L x) < s then L x else n) ∧ ∀ c < st.2.size, st.2[c]! = R c

theorem orbRoots_eq (n : ℕ) (gens : Array (Array ℕ)) :
    (orbLabels n gens).2 =
      (forIn (m := Id) [:n] (Array.replicate n n, (#[] : Array ℕ)) (oStep n gens)).2 := rfl

theorem orbRoots_eq_of (hm : m ≤ n) (hL : ∀ x < n, L x < m)
    (hR : ∀ c < m, R c < n ∧ L (R c) = c) (hRmin : ∀ x < n, R (L x) ≤ x)
    (hRmono : ∀ c c', c < c' → c' < m → R c < R c')
    (hcl : ∀ x < n, ∀ k < gens.size, ga gens k x < n → L (ga gens k x) = L x)
    (htree : ∀ x < n, x ≠ R (L x) → P x < n ∧ K x < gens.size ∧
      ga gens (K x) (P x) = x ∧ D (P x) < D x) :
    (orbLabels n gens).2.size = m ∧ ∀ c < m, (orbLabels n gens).2[c]! = R c := by
  rw [orbRoots_eq]
  have hRinj : ∀ c c', c < m → c' < m → R c = R c' → c = c' := fun c c' hc hc' e => by
    rcases Nat.lt_trichotomy c c' with h | h | h
    · exact absurd e (Nat.ne_of_lt (hRmono c c' h hc'))
    · exact h
    · exact absurd e.symm (Nat.ne_of_lt (hRmono c' c h hc))
  have hO := forIn_range_yield (ORInv n L R m) (oStep n gens) n
    (Array.replicate n n, #[])
    (fun s b hs hI => ?_) ⟨⟨by simp, by simp, fun c _ => by simp, fun x hx => by
      rw [if_neg (Nat.not_lt_zero _), getElem!_pos _ x (by simpa using hx)]
      simp⟩, fun c hc => absurd hc (by simp)⟩
  · obtain ⟨⟨-, hrm, hroots, -⟩, hget⟩ := hO
    generalize (forIn (m := Id) [:n] (Array.replicate n n, (#[] : Array ℕ)) (oStep n gens)) = r
      at hrm hroots hget ⊢
    have hsz : r.2.size = m := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · omega
      · have := (hroots (m - 1) (by omega)).1 (hR (m - 1) (by omega)).1
        omega
    exact ⟨hsz, fun c hc => hget c (by omega)⟩
  · obtain ⟨⟨hsz, hrm, hroots, hlab⟩, hget⟩ := hI
    have hLs := hL s hs
    have hLsn : L s ≠ n := Nat.ne_of_lt (lt_of_lt_of_le hLs hm)
    by_cases hb : (b.1[s]! == n) = true
    · refine ⟨_, oStep_yes hb, ?_⟩
      have hb' := hb
      rw [beq_iff_eq, hlab s hs] at hb'
      have hRs : R (L s) = s := by
        by_cases h : R (L s) < s
        · rw [if_pos h] at hb'
          exact absurd hb' hLsn
        · exact le_antisymm (hRmin s hs) (not_lt.1 h)
      have hc : b.2.size = L s := by
        rcases Nat.lt_trichotomy b.2.size (L s) with h | h | h
        · have h1 : ¬ R b.2.size < s := fun h' => lt_irrefl _ ((hroots _ (by omega)).1 h')
          have h2 := hRmono _ _ h hLs
          rw [hRs] at h2
          exact absurd h2 h1
        · exact h
        · have := (hroots (L s) hLs).2 h
          omega
      have hB := bfs_spec (c := L s) (s := s) (lab := b.1) (P := P) (K := K) (D := D) (L := L)
        hLsn hs rfl hsz hcl
        (fun x hx hxs hLx => htree x hx (by rw [hLx, hRs]; exact hxs))
        (fun z hz hLz => by rw [hlab z hz, hLz, hRs, if_neg (lt_irrefl _)])
      rw [← hc] at hB
      obtain ⟨hsz', hlab'⟩ := hB
      refine ⟨⟨hsz', by rw [Array.size_push]; omega, fun c hcm => ?_, fun x hx => ?_⟩,
        fun c hc' => ?_⟩
      · rw [Array.size_push]
        constructor
        · intro h
          rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
          · exact Nat.lt_succ_of_lt ((hroots c hcm).1 h)
          · have := hRinj c (L s) hcm hLs (by rw [h, hRs])
            omega
        · intro h
          rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
          · exact Nat.lt_succ_of_lt ((hroots c hcm).2 h)
          · rw [h, hc, hRs]
            exact Nat.lt_succ_self s
      · rw [hlab' x hx, hlab x hx, hc]
        by_cases hLx : L x = L s
        · rw [if_pos hLx, if_pos (by rw [hLx, hRs]; exact Nat.lt_succ_self s), hLx]
        · rw [if_neg hLx]
          by_cases h : R (L x) < s
          · rw [if_pos h, if_pos (Nat.lt_succ_of_lt h)]
          · have hne : R (L x) ≠ s := fun e => hLx (hRinj _ _ (hL x hx) hLs (by rw [e, hRs]))
            rw [if_neg h, if_neg (by omega)]
      · rw [Array.size_push] at hc'
        rcases Nat.lt_succ_iff_lt_or_eq.1 hc' with h | h
        · rw [get!_push_lt _ _ h]
          exact hget c h
        · rw [h, get!_push_eq, hc, hRs]
    · refine ⟨_, oStep_no hb, ⟨hsz, hrm, fun c hcm => ?_, fun x hx => ?_⟩, hget⟩
      · have hne : R c ≠ s := fun e => by
          apply hb
          rw [beq_iff_eq, hlab s hs, ← e, (hR c hcm).2, if_neg (lt_irrefl _)]
        rw [← hroots c hcm]
        omega
      · rw [hlab x hx]
        have hne : R (L x) ≠ s := fun e => by
          apply hb
          have hRL := (hR (L x) (hL x hx)).2
          rw [e] at hRL
          rw [beq_iff_eq, hlab s hs, hRL, e, if_neg (lt_irrefl _)]
        by_cases h : R (L x) < s
        · rw [if_pos h, if_pos (Nat.lt_succ_of_lt h)]
        · rw [if_neg h, if_neg (by omega)]

theorem orbRoots_of_K {kG : ℕ} {g : ℕ → ℕ → ℕ}
    (hs : gens.size = kG) (hg : ∀ k < kG, ∀ x < n, ga gens k x = g k x)
    (h : orbRecK n m kG g L R P K D = true) :
    (orbLabels n gens).2.size = m ∧ ∀ c < m, (orbLabels n gens).2[c]! = R c := by
  unfold orbRecK at h
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨hm, hpt⟩, hrt⟩ := h
  have hpt' : ∀ x < n, _ := fun x hx => by
    have := CFSG.KS.allN_spec hpt x hx
    unfold ptK at this
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq,
      Bool.not_eq_true'] at this
    exact this
  have hrt' : ∀ c < m, _ := fun c hc => by
    have := CFSG.KS.allN_spec hrt c hc
    unfold rootK at this
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq,
      Bool.not_eq_true'] at this
    exact this
  have hstep : ∀ c, c + 1 < m → R c < R (c + 1) := fun c hc => by
    have h3 := (hrt' c (by omega)).2
    rcases h3 with h3 | h3
    · exfalso
      have h4 : Nat.blt (c + 1) m = true := by simpa using hc
      simp_all
    · simpa using h3
  refine orbRoots_eq_of (m := m) (L := L) (R := R) (P := P) (K := K) (D := D) hm
    (fun x hx => (hpt' x hx).1.1.1) (fun c hc => ⟨(hrt' c hc).1.1, (hrt' c hc).1.2⟩)
    (fun x hx => (hpt' x hx).1.1.2) (fun c c' hcc hc' => ?_) (fun x hx k hk hkn => ?_)
    (fun x hx hxr => ?_)
  · induction c' with
    | zero => exact absurd hcc (Nat.not_lt_zero _)
    | succ c' ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hcc with h1 | rfl
      · exact lt_trans (ih h1 (by omega)) (hstep c' hc')
      · exact hstep c hc'
  · rw [hs] at hk
    have := (CFSG.KS.allN_spec (hpt' x hx).1.2 k hk)
    rw [hg k hk x hx] at hkn ⊢
    simp only [Bool.or_eq_true, Bool.not_eq_true', Nat.beq_eq] at this
    rcases this with h1 | h1
    · exfalso
      have h4 : Nat.blt (g k x) n = true := by simpa using hkn
      simp_all
    · exact h1
  · rcases (hpt' x hx).2 with h1 | h1
    · exact absurd h1 hxr
    · obtain ⟨⟨⟨hp, hk⟩, he⟩, hd⟩ := h1
      refine ⟨hp, by rw [hs]; exact hk, by rw [hg _ hk _ hp]; exact he, hd⟩

end CFSG.KS.OrbLab

end
