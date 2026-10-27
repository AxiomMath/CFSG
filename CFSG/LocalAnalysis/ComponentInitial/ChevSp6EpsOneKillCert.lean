module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneKillAction

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

open Subgroup

theorem foldl_code (l : List ℕ) (r : ℕ) :
    l.foldl (fun r a => 64 * r + a) r = r * 64 ^ l.length + codeT l := by
  induction l generalizing r with
  | nil => simp [codeT]
  | cons a l ih =>
    show l.foldl (fun r a => 64 * r + a) (64 * r + a) = r * 64 ^ (l.length + 1) + codeT (a :: l)
    rw [ih, show codeT (a :: l) = l.foldl (fun r a => 64 * r + a) (64 * 0 + a) from rfl, ih]
    ring

theorem codeT_cons (a : ℕ) (l : List ℕ) : codeT (a :: l) = a * 64 ^ l.length + codeT l := by
  rw [codeT, List.foldl_cons, foldl_code]
  ring

theorem codeT_lt : ∀ l : List ℕ, (∀ a ∈ l, a < 64) → codeT l < 64 ^ l.length
  | [], _ => by simp [codeT]
  | a :: l, h => by
    rw [codeT_cons, List.length_cons, pow_succ]
    have ha := h a List.mem_cons_self
    have hl := codeT_lt l fun b hb => h b (List.mem_cons_of_mem _ hb)
    have : a * 64 ^ l.length + codeT l < (a + 1) * 64 ^ l.length := by nlinarith
    calc a * 64 ^ l.length + codeT l < (a + 1) * 64 ^ l.length := this
      _ ≤ 64 * 64 ^ l.length := Nat.mul_le_mul_right _ ha
      _ = 64 ^ l.length * 64 := by ring

theorem codeT_injective : ∀ l l' : List ℕ, l.length = l'.length → (∀ a ∈ l, a < 64) →
    (∀ a ∈ l', a < 64) → codeT l = codeT l' → l = l'
  | [], [], _, _, _, _ => rfl
  | a :: l, b :: l', hlen, hl, hl', hc => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    rw [codeT_cons, codeT_cons, ← hlen] at hc
    have h1 := codeT_lt l fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have h2 := codeT_lt l' fun x hx => hl' x (List.mem_cons_of_mem _ hx)
    rw [← hlen] at h2
    have hpos : 0 < 64 ^ l.length := by positivity
    have hab : a = b := by
      have e1 : (a * 64 ^ l.length + codeT l) / 64 ^ l.length = a := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt h1, Nat.zero_add]
      have e2 : (b * 64 ^ l.length + codeT l') / 64 ^ l.length = b := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt h2, Nat.zero_add]
      rw [← e1, hc, e2]
    subst hab
    have hcl : codeT l = codeT l' := by omega
    rw [codeT_injective l l' hlen (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      (fun x hx => hl' x (List.mem_cons_of_mem _ hx)) hcl]
  | [], _ :: _, hlen, _, _, _ => absurd hlen (by simp)
  | _ :: _, [], hlen, _, _, _ => absurd hlen (by simp)

@[expose] def Good (l : List ℕ) : Prop := l.length = 6 ∧ ∀ a ∈ l, a < 64

theorem good_compT {a b : List ℕ} (ha : Good a) (hb : Good b) : Good (compT a b) :=
  ⟨by simp [compT, hb.1], fun x hx => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    exact evalV_lt ha.2 y⟩

theorem good_tupleOf (σ : Equiv.Perm (Fin 64)) : Good (tupleOf σ) :=
  ⟨by simp [tupleOf], fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact fn_lt σ _⟩

theorem good_letter {l : List ℕ} (hl : Good l) (a : ℕ) : Good (letter l a) := by
  match a with
  | 0 => show Good z0T; exact ⟨rfl, by decide⟩
  | 1 => show Good lam1T; exact ⟨rfl, by decide⟩
  | 2 => show Good lam2T; exact ⟨rfl, by decide⟩
  | n + 3 => exact hl

theorem good_evalW {l : List ℕ} (hl : Good l) (w : List ℕ) : Good (evalW l w) := by
  unfold evalW
  have key : ∀ (w : List ℕ) (acc : List ℕ), Good acc →
      Good (w.foldl (fun acc a => compT acc (letter l a)) acc) := by
    intro w
    induction w with
    | nil => intro acc h; exact h
    | cons a w ih => intro acc h; exact ih _ (good_compT h (good_letter hl a))
  exact key w idT ⟨rfl, by decide⟩

theorem codeT_inj_good {a b : List ℕ} (ha : Good a) (hb : Good b) (h : codeT a = codeT b) :
    a = b :=
  codeT_injective a b (ha.1.trans hb.1.symm) ha.2 hb.2 h

@[expose] def letterG {G : Type*} [Group G] (z l₁ l₂ t : G) : ℕ → G
  | 0 => z
  | 1 => l₁
  | 2 => l₂
  | _ => t

@[expose] def evalWG {G : Type*} [Group G] (z l₁ l₂ t : G) (w : List ℕ) : G :=
  w.foldl (fun acc a => acc * letterG z l₁ l₂ t a) 1

namespace KillData

variable {G : Type*} [Group G] {u : Bool} {Jh E : Subgroup G} {cV cE : G → ℕ}
  {z l₁ l₂ : G} (h : KillData u Jh E cV cE z l₁ l₂)
include h

theorem letterG_mem {t : G} (ht : t ∈ normalizer (Jh : Set G)) (a : ℕ) :
    letterG z l₁ l₂ t a ∈ normalizer (Jh : Set G) := by
  match a with
  | 0 => exact h.z_norm
  | 1 => exact h.l₁_norm
  | 2 => exact h.l₂_norm
  | n + 3 => exact ht

theorem evalWG_mem {t : G} (ht : t ∈ normalizer (Jh : Set G)) (w : List ℕ) :
    evalWG z l₁ l₂ t w ∈ normalizer (Jh : Set G) := by
  unfold evalWG
  have key : ∀ (w : List ℕ) (acc : G), acc ∈ normalizer (Jh : Set G) →
      w.foldl (fun acc a => acc * letterG z l₁ l₂ t a) acc ∈ normalizer (Jh : Set G) := by
    intro w
    induction w with
    | nil => intro acc hacc; exact hacc
    | cons a w ih => intro acc hacc; exact ih _ (mul_mem hacc (h.letterG_mem ht a))
  exact key w 1 (one_mem _)

theorem tupleOf_ρV_eq {g : G} (hg : g ∈ normalizer (Jh : Set G)) {T : List ℕ} (hT : Good T)
    (hact : ∀ x ∈ Jh, cV (g * x * g⁻¹) = evalV T (cV x)) : tupleOf (h.ρV ⟨g, hg⟩) = T := by
  apply List.ext_getElem
  · rw [(good_tupleOf _).1, hT.1]
  · intro j hj _
    have hj6 : j < 6 := by simpa [tupleOf] using hj
    have h2 : 2 ^ j < 64 := two_pow_lt_64 (List.mem_range.2 hj6)
    simp only [tupleOf, List.getElem_map, List.getElem_range]
    rw [fn, dite_eq_left h2, h.ρV_apply]
    show cV (g * h.liftV (2 ^ j) * g⁻¹) = T[j]
    rw [hact _ (h.liftV_mem _), h.cV_liftV h2, evalV_two_pow hj6,
      List.getD_eq_getElem _ _ (by rw [hT.1]; exact hj6)]

theorem tupleOf_letter {t : G} (ht : t ∈ normalizer (Jh : Set G)) (a : ℕ) :
    tupleOf (h.ρV ⟨letterG z l₁ l₂ t a, h.letterG_mem ht a⟩) =
      letter (tupleOf (h.ρV ⟨t, ht⟩)) a := by
  match a with
  | 0 => exact h.tupleOf_ρV_eq (T := z0T) h.z_norm ⟨rfl, by decide⟩ h.z_act
  | 1 => exact h.tupleOf_ρV_eq (T := lam1T) h.l₁_norm ⟨rfl, by decide⟩ h.l₁_act
  | 2 => exact h.tupleOf_ρV_eq (T := lam2T) h.l₂_norm ⟨rfl, by decide⟩ h.l₂_act
  | n + 3 => rfl

theorem tupleOf_evalWG {t : G} (ht : t ∈ normalizer (Jh : Set G)) (w : List ℕ) :
    tupleOf (h.ρV ⟨evalWG z l₁ l₂ t w, h.evalWG_mem ht w⟩) = evalW (tupleOf (h.ρV ⟨t, ht⟩)) w := by
  unfold evalWG evalW
  have key : ∀ (w : List ℕ) (acc : G) (hacc : acc ∈ normalizer (Jh : Set G)),
      tupleOf (h.ρV ⟨w.foldl (fun acc a => acc * letterG z l₁ l₂ t a) acc,
        (by
          have key' : ∀ (w : List ℕ) (acc : G), acc ∈ normalizer (Jh : Set G) →
              w.foldl (fun acc a => acc * letterG z l₁ l₂ t a) acc ∈ normalizer (Jh : Set G) := by
            intro w
            induction w with
            | nil => intro acc hacc; exact hacc
            | cons a w ih => intro acc hacc; exact ih _ (mul_mem hacc (h.letterG_mem ht a))
          exact key' w acc hacc)⟩) =
        w.foldl (fun acc a => compT acc (letter (tupleOf (h.ρV ⟨t, ht⟩)) a))
          (tupleOf (h.ρV ⟨acc, hacc⟩)) := by
    intro w
    induction w with
    | nil => intro acc hacc; rfl
    | cons a w ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      rw [ih _ (mul_mem hacc (h.letterG_mem ht a))]
      congr 1
      have e : (⟨acc * letterG z l₁ l₂ t a, mul_mem hacc (h.letterG_mem ht a)⟩ :
          normalizer (Jh : Set G)) = ⟨acc, hacc⟩ * ⟨_, h.letterG_mem ht a⟩ := rfl
      rw [e, map_mul, tupleOf_mul (h.ρV_mem_Gq _).1, h.tupleOf_letter ht a]
  rw [key w 1 (one_mem _)]
  congr 1
  rw [show (⟨1, one_mem _⟩ : normalizer (Jh : Set G)) = 1 from rfl, map_one, tupleOf_one]

end KillData

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
