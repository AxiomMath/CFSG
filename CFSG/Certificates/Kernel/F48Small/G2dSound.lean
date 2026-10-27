module

public import Certificates.Data.Kernel.F48Small.G2dK
public import CFSG.Certificates.Kernel.F48Small.PackSound

public section

namespace CFSG.KC.F48S

open CFSG.KC.Ord CFSG.KC.LQT.L CFSG.Quasithin

theorem triK_cons3 (d : Char → ℕ) (a b c : Char) (r : List Char) :
    triK d (a :: b :: c :: r) 0 0 0 = (d a, d b, d c) :: triK d r 0 0 0 := rfl

theorem triK_getD (d : Char → ℕ) : ∀ (e : ℕ) (l : List Char), 3 * e + 2 < l.length →
    (triK d l 0 0 0).getD e (0, 0, 0) =
      (d (l.getD (3 * e) '0'), d (l.getD (3 * e + 1) '0'), d (l.getD (3 * e + 2) '0'))
  | e, a :: b :: c :: r, h => by
    rw [triK_cons3]
    cases e with
    | zero => rfl
    | succ e =>
      have hr : 3 * e + 2 < r.length := by simp at h; omega
      have e0 : 3 * (e + 1) = 3 * e + 2 + 1 := by ring
      rw [List.getD_cons_succ, triK_getD d e r hr, e0]
      simp only [List.getD_cons_succ]
  | e, [], h => by simp at h
  | e, [_], h => by simp at h
  | e, [_, _], h => by simp at h

@[expose] def ValG (l : List ℕ) : Prop := l.length = 28 ∧ ∀ e ∈ l, e < 64

theorem pget_encL_g : ∀ (a : List ℕ), (∀ e ∈ a, e < 64) → ∀ j, pget (encL a) j = a.getD j 0
  | [], _, j => by rw [pget_eq, encL_nil]; simp
  | x :: a, h, j => by
    have hx : x < 64 := h x (by simp)
    have ha : ∀ e ∈ a, e < 64 := fun e he => h e (by simp [he])
    cases j with
    | zero => rw [pget_eq, encL_cons, pow_zero, Nat.div_one, enc_mod _ _ hx]; rfl
    | succ j =>
      rw [List.getD_cons_succ, ← pget_encL_g a ha j, pget_eq, pget_eq, encL_cons, pow_succ',
        ← Nat.div_div_eq_div_mul, enc_div _ _ hx]

theorem pcomp_encL_g (p : ℕ) : ∀ (b : List ℕ), (∀ e ∈ b, e < 64) →
    pcomp p b.length (encL b) = encL (b.map (pget p))
  | [], _ => rfl
  | x :: b, h => by
    have hx : x < 64 := h x (by simp)
    have hb : ∀ e ∈ b, e < 64 := fun e he => h e (by simp [he])
    rw [List.length_cons, pcomp_succ, encL_cons, enc_mod _ _ hx, enc_div _ _ hx,
      pcomp_encL_g p b hb, List.map_cons, encL_cons]

theorem valG_compL {a b : List ℕ} (ha : ValG a) (hb : ValG b) : ValG (compL a b) := by
  refine ⟨by simp [compL, hb.1], fun e he => ?_⟩
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 he
  rw [List.getD_eq_getElem?_getD]
  cases h : a[j]? with
  | none => simp
  | some v => exact ha.2 v (List.mem_of_getElem? h)

theorem encL_compL_g {a b : List ℕ} (ha : ValG a) (hb : ValG b) :
    encL (compL a b) = pcomp (encL a) 28 (encL b) := by
  rw [← hb.1, pcomp_encL_g _ b hb.2]
  congr 1
  apply List.map_congr_left
  intro j _
  rw [pget_encL_g a ha.2]

theorem encL_inj_g : ∀ {a b : List ℕ}, a.length = b.length → (∀ e ∈ a, e < 64) →
    (∀ e ∈ b, e < 64) → encL a = encL b → a = b
  | [], [], _, _, _, _ => rfl
  | x :: a, y :: b, hl, ha, hb, he => by
    have hx : x < 64 := ha x (by simp)
    have hy : y < 64 := hb y (by simp)
    rw [encL_cons, encL_cons] at he
    have e1 : x = y := by rw [← enc_mod x (encL a) hx, he, enc_mod _ _ hy]
    have e2 : encL a = encL b := by rw [← enc_div x (encL a) hx, he, enc_div _ _ hy]
    rw [e1, encL_inj_g (by simpa using hl) (fun e h => ha e (by simp [h]))
      (fun e h => hb e (by simp [h])) e2]

theorem eq_of_encL_g {a b : List ℕ} (ha : ValG a) (hb : ValG b) (h : encL a = encL b) : a = b :=
  encL_inj_g (ha.1.trans hb.1.symm) ha.2 hb.2 h

theorem valG_foldl {n : ℕ} (L : (Fin n × Bool) → List ℕ) (hL : ∀ l, ValG (L l)) :
    ∀ (w : List (Fin n × Bool)) (acc : List ℕ), ValG acc →
      ValG (w.foldl (fun acc l => compL acc (L l)) acc)
  | [], _, h => h
  | l :: w, acc, h => valG_foldl L hL w _ (valG_compL h (hL l))

theorem walkC_cons (P : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (a₀ : ℕ) (x : ℕ × ℕ × ℕ)
    (l : List (ℕ × ℕ × ℕ)) (e : ℕ) :
    walkC P a₀ (x :: l) e = Bool.rec (walkC P a₀ l (e + 1))
      (CFSG.KC.Ord.andB (P (e / 512) (e / 8 % 64) (e % 8) x.1 x.2.1 x.2.2) (walkC P a₀ l (e + 1)))
      (Nat.beq (e / 512) a₀) := rfl

theorem walkC_sound (P : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (a₀ : ℕ) :
    ∀ (l : List (ℕ × ℕ × ℕ)) (e : ℕ), walkC P a₀ l e = true → ∀ k < l.length,
      (e + k) / 512 = a₀ →
      P ((e + k) / 512) ((e + k) / 8 % 64) ((e + k) % 8) (l.getD k (0, 0, 0)).1
        (l.getD k (0, 0, 0)).2.1 (l.getD k (0, 0, 0)).2.2 = true
  | [], _, _, k, hk, _ => by simp at hk
  | x :: l, e, h, k, hk, ha => by
    rw [walkC_cons] at h
    have hrest : walkC P a₀ l (e + 1) = true := by
      cases hb : Nat.beq (e / 512) a₀ <;> rw [hb] at h
      · exact h
      · rw [andB_eq, Bool.and_eq_true] at h
        exact h.2
    cases k with
    | zero =>
      have hb : Nat.beq (e / 512) a₀ = true := by
        rw [Nat.beq_eq]
        simpa using ha
      rw [hb, andB_eq, Bool.and_eq_true] at h
      simpa using h.1
    | succ k =>
      have e1 : e + 1 + k = e + (k + 1) := by omega
      have := walkC_sound P a₀ l (e + 1) hrest k (by simpa using hk) (by rw [e1]; exact ha)
      rw [e1] at this
      simpa using this

theorem candAt_iff (TV TiV AV BV VV : List ℕ) (U Y a b c j t r : ℕ) :
    candAt TV TiV AV BV VV U Y a b c j t r = true ↔
      j < 4 ∧ t < 32 ∧ r < 32 ∧
      pcomp (pcomp (getK TV t) 28 (getK AV a)) 28 (getK TiV t) = U ∧
      pcomp (pcomp (pcomp (getK TV t) 28 (getK BV b)) 28 (getK TiV t)) 28 (getK TV r) = Y ∧
      pcomp (pcomp (getK TiV r) 28 (pcomp (pcomp (getK TV t) 28 (getK AV c)) 28 (getK TiV t))) 28
        (getK TV r) = getK VV j := by
  simp only [candAt, andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]

end CFSG.KC.F48S
