module

public import CFSG.Certificates.Kernel.Misc.Coset.ActSound

public section

namespace CFSG.KC.MiscCoset.Act

@[expose] noncomputable def leftPointOK (A S P : Nat → Nat) (m N K x : Nat) : Bool :=
  andB (allR 0 (Nat.add m m) fun c => Nat.blt (step A (Nat.add m m) x c) N)
  (andB (allR 0 m fun g =>
    andB (Nat.beq (step A (Nat.add m m) (step A (Nat.add m m) x (Nat.add g g))
      (Nat.succ (Nat.add g g))) x)
    (Nat.beq (step A (Nat.add m m) (step A (Nat.add m m) x (Nat.succ (Nat.add g g)))
      (Nat.add g g)) x))
  (andB (allR 0 K fun k => andB (Nat.blt (S (Nat.add (Nat.mul k N) x)) N)
    (allR 0 (Nat.add m m) fun c =>
      Nat.beq (S (Nat.add (Nat.mul k N) (step A (Nat.add m m) x c)))
        (step A (Nat.add m m) (S (Nat.add (Nat.mul k N) x)) c)))
  (Bool.rec (motive := fun _ => Bool)
    (andB (Nat.blt (P (Nat.mul 2 x)) N)
      (andB (Nat.blt (Nat.div (P (Nat.succ (Nat.mul 2 (P (Nat.mul 2 x))))) K)
        (Nat.div (P (Nat.succ (Nat.mul 2 x))) K))
      (andB (Nat.blt (Nat.mod (P (Nat.succ (Nat.mul 2 x))) K) K)
        (Nat.beq (S (Nat.add (Nat.mul (Nat.mod (P (Nat.succ (Nat.mul 2 x))) K) N)
          (P (Nat.mul 2 x)))) x))))
    true (Nat.beq x 0))))

theorem walk_left {A S : ℕ → ℕ} {L N k : ℕ}
    (hs : ∀ x < N, ∀ c < L, step A L x c < N)
    (hc : ∀ x < N, S (k * N + x) < N ∧
      ∀ c < L, S (k * N + step A L x c) = step A L (S (k * N + x)) c) :
    ∀ w : List ℕ, (∀ c ∈ w, c < L) → ∀ x < N,
      walk A L w (S (k * N + x)) = S (k * N + walk A L w x) := by
  intro w
  induction w with
  | nil => intro _ x _; rfl
  | cons c w ih =>
    intro hw x hx
    have hc' : c < L := hw c List.mem_cons_self
    change walk A L w (step A L (S (k * N + x)) c) = S (k * N + walk A L w (step A L x c))
    rw [← (hc x hx).2 c hc']
    exact ih (fun c' h' => hw c' (List.mem_cons_of_mem _ h')) _ (hs x hx c hc')

theorem pointOK_of_left {A S P : ℕ → ℕ} {m N K : ℕ} {rels : List (List ℕ)}
    (hreg : ∀ x < N, leftPointOK A S P m N K x = true)
    (hcodes : ∀ r ∈ rels, ∀ c ∈ r, c < m + m)
    (h0 : relsAt A (Nat.add m m) rels 0 = true) :
    ∀ x < N, pointOK A m N rels x = true := by
  have e : ∀ a b : Bool, andB a b = true → a = true ∧ b = true := fun a b h => by
    rwa [andB_eq, Bool.and_eq_true] at h
  have e2 : ∀ a b : Bool, a = true → b = true → andB a b = true := by
    intro a b ha hb; rw [ha, hb]; rfl
  have hs : ∀ x < N, ∀ c < m + m, step A (m + m) x c < N := by
    intro x hx c hc
    have := allR_spec (e _ _ (hreg x hx)).1 c (Nat.zero_le c) (by simpa using hc)
    rwa [Nat.blt_eq] at this
  have hS : ∀ k < K, ∀ x < N, S (k * N + x) < N ∧
      ∀ c < m + m, S (k * N + step A (m + m) x c) = step A (m + m) (S (k * N + x)) c := by
    intro k hk x hx
    have h3 := (e _ _ (e _ _ (e _ _ (hreg x hx)).2).2).1
    have h3k := e _ _ (allR_spec h3 k (Nat.zero_le k) (by simpa using hk))
    have h3a := h3k.1
    rw [Nat.blt_eq] at h3a
    refine ⟨h3a, fun c hc => ?_⟩
    exact Nat.eq_of_beq_eq_true (allR_spec h3k.2 c (Nat.zero_le c) (by simpa using hc))
  have key : ∀ d, ∀ y < N, P (2 * y + 1) / K = d → ∀ r ∈ rels, walk A (m + m) r y = y := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro y hy hd r hr
      by_cases y0 : y = 0
      · subst y0; exact relsAt_spec h0 r hr
      · have h4 := (e _ _ (e _ _ (e _ _ (hreg y hy)).2).2).2
        have hb : Nat.beq y 0 = false := by
          cases hb : Nat.beq y 0 with
          | false => rfl
          | true => exact absurd (Nat.eq_of_beq_eq_true hb) y0
        rw [hb] at h4
        obtain ⟨hp, h4⟩ := e _ _ h4
        obtain ⟨hdp, h4⟩ := e _ _ h4
        obtain ⟨hk, hx⟩ := e _ _ h4
        rw [Nat.blt_eq] at hp hdp hk
        have hp' : P (2 * y) < N := hp
        have hdp' : P (2 * P (2 * y) + 1) / K < P (2 * y + 1) / K := hdp
        have hk' : P (2 * y + 1) % K < K := hk
        have hx' : S (P (2 * y + 1) % K * N + P (2 * y)) = y := Nat.eq_of_beq_eq_true hx
        have ihp := ih _ (hd ▸ hdp') (P (2 * y)) hp' rfl r hr
        rw [← hx', walk_left hs (hS _ hk') r (hcodes r hr) _ hp', ihp]
  intro x hx
  exact e2 _ _ (e _ _ (hreg x hx)).1
    (e2 _ _ (e _ _ (e _ _ (hreg x hx)).2).1 (relsAt_of (key _ x hx rfl)))

end CFSG.KC.MiscCoset.Act

end
