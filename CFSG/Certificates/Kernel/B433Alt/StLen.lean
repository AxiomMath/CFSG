module

public import CFSG.Certificates.Kernel.B433Alt.StLenWalk
public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.KC.B433Alt

open CFSG.Certificates.CosetEnumeration CFSG.KC.B4A CFSG.KC.Y333

section
variable {LP RD RW PW RJ : ℕ → ℕ}

theorem stL_foldRange_succ (a k S : ℕ) :
    foldRange LP RD RW PW RJ a (k + 1) S =
      foldRange LP RD RW PW RJ (a + 1) k (foldStep LP RD RW PW RJ a S) :=
  stL_sN _ _

theorem stL_foldRange_add (a n m S : ℕ) :
    foldRange LP RD RW PW RJ a (n + m) S =
      foldRange LP RD RW PW RJ (a + n) m (foldRange LP RD RW PW RJ a n S) := by
  induction n generalizing a S with
  | zero => rw [Nat.zero_add, Nat.add_zero]; rfl
  | succ n ih =>
    rw [Nat.add_right_comm, stL_foldRange_succ, ih, stL_foldRange_succ, Nat.add_right_comm,
      Nat.add_assoc]

theorem stL_foldStep_zero (r : ℕ) : foldStep LP RD RW PW RJ r 0 = 0 := by
  unfold foldStep
  rw [stL_sN]
  rfl

theorem stL_foldRange_zero (a n : ℕ) : foldRange LP RD RW PW RJ a n 0 = 0 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => rw [stL_foldRange_succ, stL_foldStep_zero, ih]

private theorem brec_pos {v : ℕ} {c : Bool} (h : 0 < Bool.rec (motive := fun _ => ℕ) 0 v c) :
    c = true ∧ Bool.rec (motive := fun _ => ℕ) 0 v c = v := by
  cases c
  · exact absurd h (lt_irrefl 0)
  · exact ⟨rfl, rfl⟩

theorem stL_nocarry {D j : ℕ} (hD : D < 2 ^ 64) (hj : j < 64) (hb : D.testBit j = false) :
    D + 2 ^ j < 2 ^ 64 := by
  have h1 : D % 2 ^ (j + 1) = D % 2 ^ j := by
    rw [Nat.mod_pow_succ]
    have : D / 2 ^ j % 2 = 0 := by
      rw [Nat.testBit_eq_decide_div_mod_eq] at hb
      have := Nat.mod_two_eq_zero_or_one (D / 2 ^ j)
      simp only [decide_eq_false_iff_not] at hb
      omega
    rw [this, mul_zero, add_zero]
  have h2 : D % 2 ^ j < 2 ^ j := Nat.mod_lt _ (by positivity)
  have h3 := Nat.div_add_mod D (2 ^ (j + 1))
  have h4 : (2 : ℕ) ^ 64 = 2 ^ (j + 1) * 2 ^ (63 - j) := by rw [← pow_add]; congr 1; omega
  have h5 : D / 2 ^ (j + 1) < 2 ^ (63 - j) := Nat.div_lt_of_lt_mul (h4 ▸ hD)
  have h6 : 2 ^ (j + 1) * (D / 2 ^ (j + 1)) + 2 ^ (j + 1) ≤ 2 ^ (j + 1) * 2 ^ (63 - j) := by
    rw [← mul_add_one]; exact Nat.mul_le_mul_left _ h5
  have h7 : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
  rw [h4]
  omega

theorem stL_foldStep_spec {r S : ℕ} (h : 0 < foldStep LP RD RW PW RJ r S) :
    recOK LP RD RW PW r (RJ r) = true ∧
    (dKind (RD r) = 0 → S / 2 ^ 64 ≤ dN2 (RD r) ∧ dN1 (RD r) < dN2 (RD r) ∧
      foldStep LP RD RW PW RJ r S / 2 ^ 64 = dN2 (RD r) + 1) ∧
    (dKind (RD r) ≠ 0 → foldStep LP RD RW PW RJ r S = S) := by
  unfold foldStep at h ⊢
  rw [stL_sN] at h ⊢
  obtain ⟨hc, hv⟩ := brec_pos h
  rw [hv]
  simp only [stL_andB_eq_true] at hc
  obtain ⟨-, -, htc, hrec⟩ := hc
  refine ⟨hrec, fun hk => ?_, fun hk => ?_⟩
  · rw [hk, show Nat.beq 0 0 = true from rfl] at htc ⊢
    simp only [stL_andB_eq_true, Nat.blt_eq, Nat.ble_eq] at htc
    obtain ⟨hj, hL, hlt, hnd⟩ := htc
    rw [show Nat.shiftRight S 64 = S / 2 ^ 64 from Nat.shiftRight_eq_div_pow S 64] at hL ⊢
    refine ⟨hL, hlt, ?_⟩
    have hb : S.testBit (dN2 (RD r)) = false := by
      have hnd' : nodeDef S (dN2 (RD r)) = false := by
        cases hn : nodeDef S (dN2 (RD r))
        · rfl
        · rw [hn] at hnd; exact absurd hnd (by decide)
      unfold nodeDef at hnd'
      rw [stL_andB, show Nat.blt (dN2 (RD r)) 64 = true by rw [Nat.blt_eq]; exact hj, Bool.true_and,
        show Nat.land S (Nat.shiftLeft 1 (dN2 (RD r))) = S &&& 2 ^ dN2 (RD r) from by
          rw [← Nat.one_shiftLeft]; rfl, Nat.and_two_pow] at hnd'
      cases hS : S.testBit (dN2 (RD r))
      · rfl
      · rw [hS] at hnd'
        rw [show Nat.blt 0 (true.toNat * 2 ^ dN2 (RD r)) = true by
          rw [Nat.blt_eq]; simp] at hnd'
        exact absurd hnd' (by decide)
    have hD : S % 2 ^ 64 + 2 ^ dN2 (RD r) < 2 ^ 64 :=
      stL_nocarry (Nat.mod_lt _ (by positivity)) hj
        (by rw [Nat.testBit_mod_two_pow, hb]; simp)
    show (S + (1 <<< dN2 (RD r)) + ((dN2 (RD r) + 1 - S / 2 ^ 64) <<< 64)) / 2 ^ 64 = _
    rw [Nat.one_shiftLeft, Nat.shiftLeft_eq]
    have e : S + 2 ^ dN2 (RD r) + (dN2 (RD r) + 1 - S / 2 ^ 64) * 2 ^ 64 =
        (S % 2 ^ 64 + 2 ^ dN2 (RD r)) + 2 ^ 64 * (dN2 (RD r) + 1) := by
      have := Nat.div_add_mod S (2 ^ 64)
      have h1 : (dN2 (RD r) + 1 - S / 2 ^ 64) * 2 ^ 64 + 2 ^ 64 * (S / 2 ^ 64) =
          2 ^ 64 * (dN2 (RD r) + 1) := by
        rw [Nat.mul_comm, ← Nat.mul_add]; congr 1; omega
      omega
    rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hD, zero_add]
  · have : Nat.beq (dKind (RD r)) 0 = false := by
      cases hb : Nat.beq (dKind (RD r)) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) hk
    rw [this]

theorem stL_fold_spec {N S : ℕ} (hf : foldRange LP RD RW PW RJ 0 N 1 = S) (hS : 0 < S) :
    (∀ r < N, recOK LP RD RW PW r (RJ r) = true) ∧
    (∀ t < N, dKind (RD t) = 0 → dN1 (RD t) < dN2 (RD t)) ∧
    (∀ t t', t < t' → t' < N → dKind (RD t) = 0 → dKind (RD t') = 0 →
      dN2 (RD t) < dN2 (RD t')) := by
  have hSS : ∀ r, foldRange LP RD RW PW RJ 0 (r + 1) 1 =
      foldStep LP RD RW PW RJ r (foldRange LP RD RW PW RJ 0 r 1) := by
    intro r
    rw [stL_foldRange_add 0 r 1, Nat.zero_add, stL_foldRange_succ]
    rfl
  have hpos : ∀ r ≤ N, 0 < foldRange LP RD RW PW RJ 0 r 1 := by
    intro r hr
    rcases Nat.eq_zero_or_pos (foldRange LP RD RW PW RJ 0 r 1) with h0 | h0
    · have := stL_foldRange_add (LP := LP) (RD := RD) (RW := RW) (PW := PW) (RJ := RJ) 0 r
        (N - r) 1
      rw [Nat.add_sub_cancel' hr, hf, h0, stL_foldRange_zero] at this
      omega
    · exact h0
  have hstep : ∀ r < N, 0 < foldStep LP RD RW PW RJ r (foldRange LP RD RW PW RJ 0 r 1) :=
    fun r hr => hSS r ▸ hpos (r + 1) hr
  have hmono : ∀ a b, a ≤ b → b ≤ N → foldRange LP RD RW PW RJ 0 a 1 / 2 ^ 64 ≤
      foldRange LP RD RW PW RJ 0 b 1 / 2 ^ 64 := by
    intro a b hab hb
    induction b with
    | zero => rw [Nat.le_zero.1 hab]
    | succ b ihb =>
      rcases Nat.lt_or_ge a (b + 1) with h | h
      · refine le_trans (ihb (by omega) (by omega)) ?_
        obtain ⟨-, ht, hnt⟩ := stL_foldStep_spec (hstep b (by omega))
        rw [hSS]
        by_cases hk : dKind (RD b) = 0
        · obtain ⟨h1, -, h2⟩ := ht hk
          omega
        · rw [hnt hk]
      · rw [show a = b + 1 by omega]
  refine ⟨fun r hr => (stL_foldStep_spec (hstep r hr)).1,
    fun t ht hk => ((stL_foldStep_spec (hstep t ht)).2.1 hk).2.1, ?_⟩
  intro t t' htt' ht' hk hk'
  obtain ⟨-, -, h2⟩ := (stL_foldStep_spec (hstep t (by omega))).2.1 hk
  obtain ⟨h1', -, -⟩ := (stL_foldStep_spec (hstep t' ht')).2.1 hk'
  have := hmono (t + 1) t' htt' ht'.le
  rw [hSS] at this
  omega

end

section
variable {G : Type*} [Group G] {LP RD RW PW : ℕ → ℕ} {N : ℕ} {H : Subgroup G} {x : ℕ → G}
  {u : G} {X : ℕ → G}

theorem stL_recOK_wInH {r J : ℕ} (h : recOK LP RD RW PW r J = true) : wInH (RW r) = true := by
  unfold recOK at h
  rw [stL_sB, stL_sB] at h
  exact (stL_andB_eq_true.1 h).1

theorem stL_recOK_tree {r J : ℕ} (h : recOK LP RD RW PW r J = true) (hk : dKind (RD r) = 0) :
    RW r = 0 := by
  unfold recOK at h
  rw [stL_sB, stL_sB] at h
  have h2 := (stL_andB_eq_true.1 h).2
  rw [hk] at h2
  exact Nat.eq_of_beq_eq_true h2

theorem stL_recOK_sem (hy : stL_Hyp LP RD RW PW N H x u) (hX0 : X 0 = 1) {r J : ℕ} (hr : r < N)
    (htree : dKind (RD r) = 0 → stL_rc H (X (dN1 (RD r)) * evalWord x (wList (PW (dPt (RD r)))) * u)
      (X (dN2 (RD r))))
    (h : recOK LP RD RW PW r J = true) (ih : ∀ q < r, stL_Sem H x u X RD RW PW q) :
    stL_Sem H x u X RD RW PW r := by
  unfold recOK at h
  rw [stL_sB, stL_sB] at h
  have h2 := (stL_andB_eq_true.1 h).2
  have hk16 : dKind (RD r) < 16 := by
    rw [show dKind (RD r) = (RD r) % 2 ^ 4 from Nat.and_two_pow_sub_one_eq_mod (RD r) 4]
    exact Nat.mod_lt _ (by norm_num)
  generalize hk : dKind (RD r) = k at h2 hk16 htree
  interval_cases k
  · refine stL_Sem_fact (by rw [hk]; norm_num) ?_
    rw [hy.tree0 r hr hk, stL_val_zero, mul_one]
    exact htree rfl
  · exact stL_Sem_fact (by rw [hk]; norm_num) (stL_inv_sem hy hr h2 ih)
  · exact stL_Sem_fact (by rw [hk]; norm_num) (stL_trans_sem hy hr h2 ih)
  · exact stL_Sem_fact (by rw [hk]; norm_num) (stL_dead_sem hy hr h2 ih)
  · exact stL_Sem_fact (by rw [hk]; norm_num) (stL_link_sem hy hr h2 ih)
  · exact stL_walk_sem hy hr ih h2
  · exact stL_Sem_coinc (by rw [hk]; rfl) (stL_coinc_sem hy hr h2 ih)
  · exact stL_Sem_stab (by rw [hk]; rfl) (stL_let_sem hy hX0 h2)
  · exact stL_Sem_stab (by rw [hk]; rfl) (stL_seed_sem hy hr h2 ih)
  · exact stL_Sem_stab (by rw [hk]; rfl) (stL_diff_sem hy hr h2 ih)
  · exact stL_Sem_stab (by rw [hk]; rfl) (stL_conj_sem hy hr h2 ih)
  · exact stL_walk_sem hy hr ih (stL_andB_eq_true.1 (stL_andB_eq_true.1 h2).2).2
  · exact stL_walk_sem hy hr ih (stL_andB_eq_true.1 (stL_andB_eq_true.1 h2).2).2
  · exact absurd (show false = true from h2) (by decide)
  · exact absurd (show false = true from h2) (by decide)
  · exact absurd (show false = true from h2) (by decide)

end

noncomputable def stL_X {G : Type*} [Group G] (RD : ℕ → ℕ) (N : ℕ) (g : ℕ → G) (u : G) (j : ℕ) :
    G :=
  haveI : Decidable (∃ q, q < N ∧ dKind (RD q) = 0 ∧ dN2 (RD q) = j ∧ dN1 (RD q) < j) :=
    Classical.propDecidable _
  if h : ∃ q, q < N ∧ dKind (RD q) = 0 ∧ dN2 (RD q) = j ∧ dN1 (RD q) < j then
    stL_X RD N g u (dN1 (RD (Nat.find h))) * g (dPt (RD (Nat.find h))) * u
  else 1
termination_by j
decreasing_by exact (Nat.find_spec h).2.2.2

section
variable {G : Type*} [Group G] {RD : ℕ → ℕ} {N : ℕ} {g : ℕ → G} {u : G}

theorem stL_X_zero : stL_X RD N g u 0 = 1 := by
  rw [stL_X, dif_neg]
  rintro ⟨q, -, -, -, h⟩
  exact Nat.not_lt_zero _ h

theorem stL_X_tree {t : ℕ} (ht : t < N) (hk : dKind (RD t) = 0)
    (hlt : dN1 (RD t) < dN2 (RD t))
    (huniq : ∀ q < N, dKind (RD q) = 0 → dN2 (RD q) = dN2 (RD t) → q = t) :
    stL_X RD N g u (dN2 (RD t)) = stL_X RD N g u (dN1 (RD t)) * g (dPt (RD t)) * u := by
  have hex : ∃ q, q < N ∧ dKind (RD q) = 0 ∧ dN2 (RD q) = dN2 (RD t) ∧
      dN1 (RD q) < dN2 (RD t) := ⟨t, ht, hk, rfl, hlt⟩
  rw [stL_X, dif_pos hex]
  have hq := Nat.find_spec hex
  rw [huniq _ hq.1 hq.2.1 hq.2.2.1]

end

theorem st_sound_bdd {LP RD RW PW RJ : ℕ → ℕ} {N S : ℕ} (hf : foldRange LP RD RW PW RJ 0 N 1 = S)
    (hS : 0 < S) (hRW : ∀ r < N, wLen (RW r) < 2 ^ 16) (hPW : ∀ p, wLen (PW p) < 2 ^ 16)
    (hPWH : ∀ p, wInH (PW p) = true)
    {G : Type*} [Group G] (H : Subgroup G) (x : ℕ → G) (u : G)
    (hxH : ∀ c < 10, x c ∈ H) (hx : ∀ c, x c * x c = 1) (hu : u * u = 1)
    (hθ : ∀ c < 10, c ≠ 7 → u * x c * u = x (fld THM (4 * c) 15))
    (h47 : (x 7 * u) ^ 4 = 1)
    (hone : ∀ w, wInH w = true → isOne LP w = true → evalWord x (wList w) = 1) :
    ∃ X : ℕ → G, X 0 = 1 ∧ ∀ r < N,
      (isFact (dKind (RD r)) = true →
        X (dN1 (RD r)) * evalWord x (wList (PW (dPt (RD r)))) * u *
          (X (dN2 (RD r)) * evalWord x (wList (RW r)))⁻¹ ∈ H) ∧
      (isStab (dKind (RD r)) = true →
        X (dN2 (RD r)) * evalWord x (wList (RW r)) * (X (dN2 (RD r)))⁻¹ ∈ H) ∧
      wInH (RW r) = true := by
  obtain ⟨hrec, hlt, hinc⟩ := stL_fold_spec hf hS
  have hRWH : ∀ r < N, wInH (RW r) = true := fun r hr => stL_recOK_wInH (hrec r hr)
  have hy : stL_Hyp LP RD RW PW N H x u :=
    ⟨hRW, hRWH, fun r hr hk => stL_recOK_tree (hrec r hr) hk, hPW, hPWH, hxH, hx, hu, hθ, h47,
      hone⟩
  set X := stL_X RD N (fun p => evalWord x (wList (PW p))) u with hXdef
  have hX0 : X 0 = 1 := stL_X_zero
  have hXt : ∀ t < N, dKind (RD t) = 0 →
      X (dN2 (RD t)) = X (dN1 (RD t)) * evalWord x (wList (PW (dPt (RD t)))) * u := by
    intro t ht hk
    refine stL_X_tree ht hk (hlt t ht hk) fun q hq hqk hq2 => ?_
    rcases lt_trichotomy q t with h | h | h
    · exact absurd hq2 (ne_of_lt (hinc q t h ht hqk hk))
    · exact h
    · exact absurd hq2 (ne_of_gt (hinc t q h hq hk hqk))
  have hsem : ∀ r < N, stL_Sem H x u X RD RW PW r := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ihr =>
      intro hr
      exact stL_recOK_sem hy hX0 hr (fun hk => by rw [hXt r hr hk]; exact stL_rc_refl _)
        (hrec r hr) (fun q hq => ihr q hq (lt_trans hq hr))
  exact ⟨X, hX0, fun r hr => ⟨(hsem r hr).1, (hsem r hr).2.1, hRWH r hr⟩⟩

end CFSG.KC.B433Alt

end
