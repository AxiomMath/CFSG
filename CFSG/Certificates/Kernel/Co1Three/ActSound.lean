module

public import CFSG.Certificates.Kernel.Co1Three.TermSound

public section

namespace CFSG.KC.Co1Cl

open CFSG.KC.Enum

theorem epM_acc {M : Type*} [Monoid M] (f : Nat → M) (p : Nat) :
    ∀ (G : List Nat) (v : Nat) (acc b : M), epM f p G v (acc * b) = acc * epM f p G v b
  | [], _, _, _ => rfl
  | g :: G, v, acc, b => by rw [epM, epM, mul_assoc, epM_acc f p G]

theorem epM_eq_mul {M : Type*} [Monoid M] (f : Nat → M) (p : Nat) (G : List Nat) (v : Nat) (acc : M) :
    epM f p G v acc = acc * epM f p G v 1 := by
  rw [← epM_acc, mul_one]

theorem epM_zero {M : Type*} [Monoid M] (f : Nat → M) (p : Nat) : ∀ G : List Nat, epM f p G 0 1 = 1
  | [] => rfl
  | g :: G => by rw [epM, Nat.zero_div, Nat.zero_mod, pow_zero, mul_one, epM_zero f p G]

theorem commute_epM {M : Type*} [Monoid M] (f : Nat → M) (p : Nat) (z : M) :
    ∀ G : List Nat, (∀ x ∈ G, Commute z (f x)) → ∀ (v : Nat) (acc : M), Commute z acc →
      Commute z (epM f p G v acc)
  | [], _, _, _, h => h
  | g :: G, hG, v, acc, h => by
    rw [epM]
    exact commute_epM f p z G (fun x hx => hG x (List.mem_cons_of_mem g hx)) _ _
      (h.mul_right ((hG g List.mem_cons_self).pow_right _))

theorem pow_mod_eq {M : Type*} [Monoid M] {x : M} {p : Nat} (h : x ^ p = 1) (k : Nat) :
    x ^ (k % p) = x ^ k := by
  conv_rhs => rw [← Nat.div_add_mod k p]
  rw [pow_add, pow_mul, h, one_pow, one_mul]

theorem addVK_succ (p n x y : Nat) :
    addVK p (n + 1) x y = (x % p + y % p) % p + p * addVK p n (x / p) (y / p) := rfl

theorem epM_addVK {M : Type*} [Monoid M] (f : Nat → M) {p : Nat} (hp : 0 < p) :
    ∀ G : List Nat, (∀ x ∈ G, ∀ y ∈ G, Commute (f x) (f y)) → (∀ x ∈ G, f x ^ p = 1) →
      ∀ x y : Nat, epM f p G (addVK p G.length x y) 1 = epM f p G x 1 * epM f p G y 1
  | [], _, _, _, _ => (mul_one 1).symm
  | g :: G, hc, ho, x, y => by
    have hc' : ∀ x ∈ G, ∀ y ∈ G, Commute (f x) (f y) := fun a ha b hb =>
      hc a (List.mem_cons_of_mem g ha) b (List.mem_cons_of_mem g hb)
    have ho' : ∀ x ∈ G, f x ^ p = 1 := fun a ha => ho a (List.mem_cons_of_mem g ha)
    have hd : (x % p + y % p) % p < p := Nat.mod_lt _ hp
    rw [List.length_cons, addVK_succ, epM, epM, epM]
    rw [Nat.add_mul_mod_self_left, Nat.mod_mod, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hd,
      Nat.zero_add, one_mul, one_mul, one_mul, epM_eq_mul f p G _ (f g ^ ((x % p + y % p) % p)),
      epM_eq_mul f p G (x / p), epM_eq_mul f p G (y / p), epM_addVK f hp G hc' ho',
      pow_mod_eq (ho g List.mem_cons_self) (x % p + y % p), pow_add]
    have key : Commute (f g ^ (y % p)) (epM f p G (x / p) 1) :=
      commute_epM f p _ G (fun a ha => (hc g List.mem_cons_self a (List.mem_cons_of_mem g ha)).pow_left _) _ _
        (Commute.one_right _)
    calc f g ^ (x % p) * f g ^ (y % p) * (epM f p G (x / p) 1 * epM f p G (y / p) 1)
        = f g ^ (x % p) * ((f g ^ (y % p) * epM f p G (x / p) 1) * epM f p G (y / p) 1) := by
          simp only [mul_assoc]
      _ = f g ^ (x % p) * epM f p G (x / p) 1 * (f g ^ (y % p) * epM f p G (y / p) 1) := by
          rw [key.eq]
          simp only [mul_assoc]

theorem epM_actK {M : Type*} [Monoid M] (f : Nat → M) {p : Nat} (hp : 0 < p) (G : List Nat)
    (hc : ∀ x ∈ G, ∀ y ∈ G, Commute (f x) (f y)) (ho : ∀ x ∈ G, f x ^ p = 1) :
    ∀ (rows : List Nat) (v acc : Nat), epM f p G (actK p G.length rows v acc) 1 =
      epM f p G acc 1 * epM (fun c => epM f p G c 1) p rows v 1
  | [], _, acc => (mul_one (epM f p G acc 1)).symm
  | r :: rows, v, acc => by
    have iter : ∀ (a e : Nat), epM f p G (Nat.rec (motive := fun _ => Nat) a
        (fun _ b => strictN b fun b => addVK p G.length b r) e) 1 = epM f p G a 1 * epM f p G r 1 ^ e := by
      intro a e
      induction e with
      | zero =>
        rw [pow_zero, mul_one]
        rfl
      | succ e ih =>
        change epM f p G (strictN (Nat.rec (motive := fun _ => Nat) a
          (fun _ b => strictN b fun b => addVK p G.length b r) e) fun b => addVK p G.length b r) 1 = _
        rw [strictN_eq, epM_addVK f hp G hc ho, ih, pow_succ, mul_assoc]
    change epM f p G (strictN (v % p) fun e => strictN (Nat.rec (motive := fun _ => Nat) acc
      (fun _ b => strictN b fun b => addVK p G.length b r) e) fun acc' => actK p G.length rows (v / p) acc') 1 = _
    rw [strictN_eq, strictN_eq, epM_actK f hp G hc ho rows, iter, epM, one_mul,
      epM_eq_mul (fun c => epM f p G c 1) p rows (v / p) (epM f p G r 1 ^ (v % p)), mul_assoc]

theorem conj_epM {M : Type*} [Group M] (f F : Nat → M) (p : Nat) (g : M) :
    ∀ (G rows : List Nat), rows.length = G.length →
      (∀ j < G.length, g⁻¹ * f (G.getD j 0) * g = F (rows.getD j 0)) →
      ∀ (v : Nat) (acc : M), g⁻¹ * epM f p G v acc * g = g⁻¹ * acc * g * epM F p rows v 1
  | [], [], _, _, _, _ => (mul_one _).symm
  | [], _ :: _, h, _, _, _ => absurd h (by simp)
  | _ :: _, [], h, _, _, _ => absurd h (by simp)
  | x :: G, r :: rows, hl, hr, v, acc => by
    have hc : ∀ y, g⁻¹ * y * g = MulAut.conj g⁻¹ y := fun y => by
      rw [MulAut.conj_apply, inv_inv]
    have h0 := hr 0 (Nat.succ_pos _)
    simp only [List.getD_cons_zero] at h0
    have h0' : MulAut.conj g⁻¹ (f x) = F r := by
      rw [← hc]
      exact h0
    rw [epM, conj_epM f F p g G rows (Nat.succ.inj hl) (fun j hj => by
      simpa using hr (j + 1) (Nat.succ_lt_succ hj)), epM, one_mul,
      epM_eq_mul F p rows (v / p) (F r ^ (v % p)), hc, hc, map_mul, map_pow, h0', mul_assoc]

theorem conj_actK {M : Type*} [Group M] (f : Nat → M) {p : Nat} (hp : 0 < p) (Gs : List Nat)
    (hc : ∀ x ∈ Gs, ∀ y ∈ Gs, Commute (f x) (f y)) (ho : ∀ x ∈ Gs, f x ^ p = 1) (g : M)
    (rows : List Nat) (hl : rows.length = Gs.length)
    (hr : ∀ j < rows.length, f (Gs.getD j 0) * g = g * epM f p Gs (rows.getD j 0) 1) (v : Nat) :
    g⁻¹ * epM f p Gs v 1 * g = epM f p Gs (actK p Gs.length rows v 0) 1 := by
  rw [conj_epM f (fun c => epM f p Gs c 1) p g Gs rows hl (fun j hj => by
      rw [mul_assoc, hr j (hl ▸ hj), inv_mul_cancel_left]) v 1,
    epM_actK f hp Gs hc ho rows v 0, epM_zero, mul_one, inv_mul_cancel, one_mul]

theorem nzRows_eq (NZ : List (Nat × List Nat)) (g : Nat) : nzRows NZ g = (NZ.getD g (0, [])).2 := by
  induction NZ generalizing g with
  | nil => rfl
  | cons a L ih => cases g with
    | zero => rfl
    | succ g => exact ih g

theorem forest_isConj {M : Type*} [Group M] (f : Nat → M) {p : Nat} (hp : 0 < p) (Gs : List Nat)
    (hc : ∀ x ∈ Gs, ∀ y ∈ Gs, Commute (f x) (f y)) (ho : ∀ x ∈ Gs, f x ^ p = 1)
    {NZ : List (Nat × List Nat)} {RT : List Nat} {DP : Nat} {FT : List Nat}
    (hf : forestK p Gs.length NZ RT DP FT = true)
    (hnz : ∀ x ∈ NZ, x.2.length = Gs.length ∧
      ∀ j < x.2.length, f (Gs.getD j 0) * f x.1 = f x.1 * epM f p Gs (x.2.getD j 0) 1) :
    ∀ c, 1 ≤ c → c < p ^ Gs.length → ∃ r ∈ RT, IsConj (epM f p Gs r 1) (epM f p Gs c 1) := by
  intro c h1 h2
  obtain ⟨r, hr, hrt⟩ := forestK_sound hf c h1 h2
  refine ⟨r, hr, ?_⟩
  clear h1 h2
  induction hrt with
  | refl => exact IsConj.refl _
  | tail _ hab ih =>
    obtain ⟨g, hg, hact⟩ := hab
    rw [nzRows_eq] at hact
    have hx : NZ.getD g (0, []) ∈ NZ := by
      rw [List.getD_eq_getElem _ _ hg]
      exact List.getElem_mem hg
    obtain ⟨hl, hrow⟩ := hnz _ hx
    have := conj_actK f hp Gs hc ho _ _ hl hrow
    refine ih.trans (isConj_iff.2 ⟨(f (NZ.getD g (0, [])).1)⁻¹, ?_⟩)
    rw [inv_inv, this, hact]

end CFSG.KC.Co1Cl

end
