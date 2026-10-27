module

public import Certificates.Data.Kernel.WittCnt
public import CFSG.Certificates.Kernel.Spor.PCountWSound

public section

namespace CFSG.KC.WCnt

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KS.PCnt CFSG.Sporadic.Schreier

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem cRow_nil (n w m : Nat) (c : Nat → Bool) (k : Nat → Nat → Nat) (g acc : Nat) :
    cRow n w m c k g [] acc = acc := rfl

theorem cRow_cons (n w m : Nat) (c : Nat → Bool) (k : Nat → Nat → Nat) (g t : Nat)
    (T : List Nat) (acc : Nat) :
    cRow n w m c k g (t :: T) acc =
      if c (pcomp n w m g t) = true then cRow n w m c k g T (k (pcomp n w m g t) acc)
      else cRow n w m c k g T acc := by
  have h : cRow n w m c k g (t :: T) acc = strictN (pcomp n w m g t) (fun h =>
      nIf(c h, strictN (k h acc) (cRow n w m c k g T), cRow n w m c k g T acc)) := rfl
  rw [h, strictN_eq']
  cases c (pcomp n w m g t)
  · simp
  · simp [strictN_eq']

@[expose] def Pruned {n : Nat} (w : Nat) (F : Nat → Nat) :
    List ((Nat → Bool) × List (Equiv.Perm (Fin n))) → Equiv.Perm (Fin n) → Prop
  | [], _ => True
  | L :: Ls, g => ∀ t ∈ L.2, (L.1 (pkw w (g * t)) = false →
      ∀ h ∈ products (Ls.map Prod.snd), F (pkw w (g * t * h)) = 0) ∧ Pruned w F Ls (g * t)

theorem ccnt_pkw {n w : Nat} (hw : n ≤ 2 ^ w) (h32 : n < 2 ^ 32) (F : Nat → Nat) :
    ∀ (Ls : List ((Nat → Bool) × List (Equiv.Perm (Fin n)))) (g : Equiv.Perm (Fin n)) (acc : Nat),
      Pruned w F Ls g →
      ccnt n w (mask w) F (Ls.map fun L => (L.1, L.2.map (pkw w))) (pkw w g) acc =
        acc + ((products (Ls.map Prod.snd)).map fun h => F (pkw w (g * h))).sum
  | [], g, acc, _ => by
    change acc + F (pkw w g) = _
    simp [products]
  | (c, T) :: Ls, g, acc, hP => by
    change cRow n w (mask w) c (ccnt n w (mask w) F (Ls.map fun L => (L.1, L.2.map (pkw w))))
      (pkw w g) (T.map (pkw w)) acc =
        acc + ((products (T :: Ls.map Prod.snd)).map fun h => F (pkw w (g * h))).sum
    induction T generalizing acc with
    | nil => simp [cRow_nil, products]
    | cons t T ih =>
      have hPt := hP t List.mem_cons_self
      have hPT : Pruned w F ((c, T) :: Ls) g := fun t' ht' => hP t' (List.mem_cons_of_mem _ ht')
      have hsplit : ((products ((t :: T) :: Ls.map Prod.snd)).map fun h => F (pkw w (g * h))).sum =
          ((products (Ls.map Prod.snd)).map fun h => F (pkw w (g * t * h))).sum +
            ((products (T :: Ls.map Prod.snd)).map fun h => F (pkw w (g * h))).sum := by
        simp only [products, List.flatMap_cons, List.map_append, List.sum_append, List.map_map,
          Function.comp_def, mul_assoc]
      rw [List.map_cons, cRow_cons, pkw_mul hw h32, hsplit]
      split
      · rw [ih _ hPT, ccnt_pkw hw h32 F Ls (g * t) acc hPt.2]
        omega
      · rename_i hc
        rw [ih _ hPT]
        have h0 : ((products (Ls.map Prod.snd)).map fun h => F (pkw w (g * t * h))).sum = 0 :=
          List.sum_eq_zero fun x hx => by
            obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hx
            exact hPt.1 (by simpa using hc) h hh
        omega

theorem mask_five : mask 5 = 31 := rfl

theorem pt_pkw (σ : Equiv.Perm (Fin 22)) (i : Fin 22) : pt (pkw 5 σ) i.val = (σ i).val := by
  have h31 : (31 : Nat) = 2 ^ 5 - 1 := by norm_num
  have h : pt (pkw 5 σ) i.val = fd 5 (pkw 5 σ) i.val := by
    change (pkw 5 σ >>> (5 * i.val)) &&& 31 = pkw 5 σ / 2 ^ (5 * i.val) % 2 ^ 5
    rw [Nat.shiftRight_eq_div_pow, h31, Nat.and_two_pow_sub_one_eq_mod]
  rw [h, fd_pkw (by norm_num) σ i.isLt]
  simp [pv]

theorem upk22_pkw (σ : Equiv.Perm (Fin 22)) : upk22 (pkw 5 σ) = ⇑σ := by
  funext i
  refine Fin.ext ?_
  change Nat.mod (pt (pkw 5 σ) i.val) 22 = _
  rw [pt_pkw]
  exact Nat.mod_eq_of_lt (σ i).isLt

theorem ind_pkw (Q : (Fin 22 → Fin 22) → Prop) [DecidablePred Q] (σ d : Equiv.Perm (Fin 22)) :
    ind Q (pkw 5 d) (pkw 5 σ) = if Q ⇑(σ * d) then 1 else 0 := by
  have e : pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) (pkw 5 σ) (pkw 5 d) = pkw 5 (σ * d) := by
    have h := pkw_mul (n := 22) (w := 5) (by norm_num) (by norm_num) σ d
    rw [mask_five] at h
    exact h
  unfold ind
  rw [e, strictN_eq', upk22_pkw]
  by_cases h : Q ⇑(σ * d)
  · rw [decide_eq_true h, if_pos h]
  · rw [decide_eq_false h, if_neg h]

theorem indB_pkw (b : Nat → Bool) (Q : (Fin 22 → Fin 22) → Prop) [DecidablePred Q]
    (hb : ∀ τ : Equiv.Perm (Fin 22), b (pkw 5 τ) = decide (Q ⇑τ)) (σ d : Equiv.Perm (Fin 22)) :
    indB b (pkw 5 d) (pkw 5 σ) = if Q ⇑(σ * d) then 1 else 0 := by
  have e : pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) (pkw 5 σ) (pkw 5 d) = pkw 5 (σ * d) := by
    have h := pkw_mul (n := 22) (w := 5) (by norm_num) (by norm_num) σ d
    rw [mask_five] at h
    exact h
  unfold indB
  rw [e, strictN_eq', hb]
  by_cases h : Q ⇑(σ * d)
  · rw [decide_eq_true h, if_pos h]
  · rw [decide_eq_false h, if_neg h]

theorem allB_iff (f : Nat → Bool) : ∀ n, allB f n = true ↔ ∀ i < n, f i = true
  | 0 => by simp [allB]
  | n + 1 => by
    have h : allB f (n + 1) = (f n && allB f n) := by
      change Bool.rec (motive := fun _ => Bool) false (allB f n) (f n) = _
      cases f n <;> rfl
    rw [h, Bool.and_eq_true, allB_iff f n]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h'
      exact ⟨h' n (Nat.lt_succ_self n), fun i hi => h' i (Nat.lt_succ_of_lt hi)⟩

theorem presT_iff (X y : Nat) : ∀ l : List Nat,
    presT X l y = true ↔ ∀ i ∈ l, inM X (pt y i) = true
  | [] => by simp [presT]
  | i :: l => by
    have h : presT X (i :: l) y = (inM X (pt y i) && presT X l y) := by
      change Bool.rec (motive := fun _ => Bool) false (presT X l y) (inM X (pt y i)) = _
      cases inM X (pt y i) <;> rfl
    rw [h, Bool.and_eq_true, presT_iff X y l, List.forall_mem_cons]

theorem presT_pkw (τ : Equiv.Perm (Fin 22)) (S : Finset (Fin 22)) (l : List Nat) (X : Nat)
    (hl : ∀ x : Fin 22, x ∈ S ↔ x.val ∈ l) (hlt : ∀ i ∈ l, i < 22)
    (hX : ∀ x : Fin 22, inM X x.val = true ↔ x ∈ S) :
    presT X l (pkw 5 τ) = decide (∀ x ∈ S, τ x ∈ S) := by
  rw [Bool.eq_iff_iff, presT_iff, decide_eq_true_iff]
  constructor
  · intro h x hx
    have h1 := h x.val ((hl x).1 hx)
    rw [pt_pkw τ x] at h1
    exact (hX _).1 h1
  · intro h i hi
    have hi' := hlt i hi
    have e : pt (pkw 5 τ) i = (τ ⟨i, hi'⟩).val := pt_pkw τ ⟨i, hi'⟩
    rw [e]
    exact (hX _).2 (h _ ((hl _).2 hi))

theorem relT_pkw (τ : Equiv.Perm (Fin 22)) (t p : Fin 22 → Fin 22) (T P : Nat)
    (hT : ∀ i : Fin 22, pt T i.val = (t i).val) (hP : ∀ i : Fin 22, pt P i.val = (p i).val) :
    relT T P (pkw 5 τ) = decide (∀ x, τ (t x) = p (τ x)) := by
  rw [Bool.eq_iff_iff, relT, allB_iff, decide_eq_true_iff]
  constructor
  · intro h x
    have h1 := Nat.eq_of_beq_eq_true (h x.val x.isLt)
    rw [hT, pt_pkw, pt_pkw, hP] at h1
    exact Fin.ext h1
  · intro h i hi
    have e : pt T i = (t ⟨i, hi⟩).val := hT ⟨i, hi⟩
    have e' : pt (pkw 5 τ) i = (τ ⟨i, hi⟩).val := pt_pkw τ ⟨i, hi⟩
    rw [e, e', pt_pkw, hP, h]
    exact Nat.beq_refl _

theorem relAny_iff (T y : Nat) : ∀ Ps : List Nat,
    relAny T Ps y = true ↔ ∃ P ∈ Ps, relT T P y = true
  | [] => by simp [relAny]
  | P :: Ps => by
    have h : relAny T (P :: Ps) y = (relT T P y || relAny T Ps y) := by
      change Bool.rec (motive := fun _ => Bool) (relAny T Ps y) true (relT T P y) = _
      cases relT T P y <;> rfl
    rw [h, Bool.or_eq_true, relAny_iff T y Ps]
    constructor
    · rintro (h1 | ⟨Q, hQ, h1⟩)
      · exact ⟨P, List.mem_cons_self, h1⟩
      · exact ⟨Q, List.mem_cons_of_mem _ hQ, h1⟩
    · rintro ⟨Q, hQ, h1⟩
      rcases List.mem_cons.1 hQ with rfl | hQ
      · exact Or.inl h1
      · exact Or.inr ⟨Q, hQ, h1⟩

theorem relAny_pkw_iff (τ : Equiv.Perm (Fin 22)) (t : Fin 22 → Fin 22) (T : Nat)
    (hT : ∀ i : Fin 22, pt T i.val = (t i).val) {k : Nat} (p : Fin k → Fin 22 → Fin 22)
    (Ps : List Nat) (hlen : Ps.length = k)
    (hP : ∀ j : Fin k, ∀ i : Fin 22, pt (Ps.getD j.val 0) i.val = (p j i).val) :
    relAny T Ps (pkw 5 τ) = true ↔ ∃ j : Fin k, ∀ x, τ (t x) = p j (τ x) := by
  rw [relAny_iff]
  constructor
  · rintro ⟨P, hPm, h⟩
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hPm
    have hn' : n < k := hlen ▸ hn
    have hPn : ∀ i : Fin 22, pt Ps[n] i.val = (p ⟨n, hn'⟩ i).val := fun i => by
      have h1 := hP ⟨n, hn'⟩ i
      simpa [List.getD_eq_getElem?_getD, hn] using h1
    rw [relT_pkw τ t (p ⟨n, hn'⟩) T Ps[n] hT hPn, decide_eq_true_iff] at h
    exact ⟨⟨n, hn'⟩, h⟩
  · rintro ⟨j, hj⟩
    have hn : j.val < Ps.length := hlen ▸ j.isLt
    have hPn : ∀ i : Fin 22, pt Ps[j.val] i.val = (p j i).val := fun i => by
      have h1 := hP j i
      simpa [List.getD_eq_getElem?_getD, hn] using h1
    refine ⟨Ps[j.val], List.getElem_mem hn, ?_⟩
    rw [relT_pkw τ t (p j) T Ps[j.val] hT hPn]
    exact decide_eq_true hj

end CFSG.KC.WCnt

end
