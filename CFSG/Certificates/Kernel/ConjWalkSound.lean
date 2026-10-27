module

public import Certificates.Data.Kernel.ConjWalk
public import CFSG.Certificates.Kernel.ConjCountSound

public section

namespace CFSG.KC.ConjWalk

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.ConjCount

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem ln_lt (N q : ℕ) : ln N q < 64 := by
  unfold ln
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem ln_eq (N q : ℕ) : ln N q = N / 2 ^ (6 * q) % 64 := by
  change (N >>> (6 * q)) &&& (2 ^ 6 - 1) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

theorem ln_zero {x : ℕ} (hx : x < 64) (e : ℕ) : ln (x + 64 * e) 0 = x := by
  rw [ln_eq]
  simp only [Nat.mul_zero, pow_zero, Nat.div_one]
  omega

theorem ln_succ {x : ℕ} (hx : x < 64) (e q : ℕ) : ln (x + 64 * e) (q + 1) = ln e q := by
  rw [ln_eq, ln_eq, show 6 * (q + 1) = 6 + 6 * q by ring, pow_add, ← Nat.div_div_eq_div_mul,
    show (2 : ℕ) ^ 6 = 64 by norm_num, show (x + 64 * e) / 64 = e by omega]

theorem pkN_succ (f : ℕ → ℕ) (k s : ℕ) : pkN f (k + 1) s = f s + 64 * pkN f k (s + 1) := rfl

theorem ln_pkN (f : ℕ → ℕ) (hf : ∀ i, f i < 64) :
    ∀ k s q, q < k → ln (pkN f k s) q = f (s + q)
  | 0, _, _, hq => absurd hq (Nat.not_lt_zero _)
  | k + 1, s, 0, _ => by rw [pkN_succ, ln_zero (hf s), Nat.add_zero]
  | k + 1, s, q + 1, hq => by
    rw [pkN_succ, ln_succ (hf s), ln_pkN f hf k (s + 1) q (by omega)]
    congr 1
    omega

theorem ln_encL : ∀ (l : List ℕ), (∀ x ∈ l, x < 64) → ∀ q, ln (encL 64 l) q = l.getD q 0
  | [], _, q => by
    rw [ln_eq]
    simp [encL]
  | x :: xs, h, 0 => by
    rw [show encL 64 (x :: xs) = x + 64 * encL 64 xs from rfl, ln_zero (h x (by simp))]
    rfl
  | x :: xs, h, q + 1 => by
    rw [show encL 64 (x :: xs) = x + 64 * encL 64 xs from rfl, ln_succ (h x (by simp)),
      ln_encL xs (fun y hy => h y (List.mem_cons_of_mem x hy)) q]
    rfl

section Group

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

@[expose] def Rp (n : ℕ) [MulAction Γ (Fin n)] (N : ℕ) (g : Γ) : Prop := ∀ q < n, ln N q = act n g q

@[expose] def kap (n : ℕ) [MulAction Γ (Fin n)] (a b c : ℕ) (g : Γ) : ℕ :=
  act n g a + 64 * (act n g b + 64 * act n g c)

theorem rp_encL (hn : n ≤ 64) (g : Γ) : Rp n (encL 64 (tab n g)) g := by
  intro q _
  rw [ln_encL _ (fun x hx => ?_)]
  · rfl
  · simp only [tab, List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    omega

theorem rp_cjP {G GI C : ℕ} {g c : Γ} (hG : Rp n G g) (hGI : Rp n GI g⁻¹) (hC : Rp n C c) :
    Rp n (cjP n G GI C) (g * c * g⁻¹) := by
  intro q hq
  unfold cjP
  rw [ln_pkN _ (fun i => ln_lt _ _) n 0 q hq, Nat.zero_add, hGI q hq, hC _ (act_lt _ hq),
    hG _ (act_lt _ (act_lt _ hq)), act_mul _ _ hq, act_mul _ _ (act_lt _ hq)]

theorem keyP_eq {a b c C : ℕ} {g : Γ} (ha : a < n) (hb : b < n) (hc : c < n) (hC : Rp n C g) :
    keyP a b c C = kap n a b c g := by
  unfold keyP kap
  rw [hC a ha, hC b hb, hC c hc]
  rfl

theorem popS_eq (s : List ℕ) : ∀ p, popS p s = s.drop p
  | 0 => rfl
  | p + 1 => by
    have e1 : ∀ l : List ℕ, List.rec (motive := fun _ => List ℕ) [] (fun _ t _ => t) l = l.tail :=
      fun l => by cases l <;> rfl
    have e : popS (p + 1) s = (popS p s).tail := e1 (popS p s)
    rw [e, popS_eq s p, List.tail_drop]

theorem topS_mem : ∀ {l : List ℕ}, l ≠ [] → topS l ∈ l
  | [], h => absurd rfl h
  | a :: _, _ => List.mem_cons_self

theorem testBit_of_land {S k : ℕ} (h : Nat.land (Nat.shiftRight S k) 1 = 0) :
    S.testBit k = false := by
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not]
  have e : Nat.land (Nat.shiftRight S k) 1 = S / 2 ^ k % 2 := by
    change (S >>> k) &&& (2 ^ 1 - 1) = _
    rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod, pow_one]
  omega

theorem testBit_lor_one (S k j : ℕ) :
    (Nat.lor S (Nat.shiftLeft 1 k)).testBit j = true ↔ S.testBit j = true ∨ j = k := by
  rw [show Nat.lor S (Nat.shiftLeft 1 k) = S ||| 1 <<< k from rfl, Nat.testBit_lor,
    Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_iff]
  exact or_congr Iff.rfl eq_comm

variable {H : Subgroup Γ} {x0 x1 t : Γ} {a b c X0 X0I X1 X1I : ℕ}

theorem walkAux_sound (h0 : x0 ∈ H) (h1 : x1 ∈ H) (hX0 : Rp n X0 x0) (hX0I : Rp n X0I x0⁻¹)
    (hX1 : Rp n X1 x1) (hX1I : Rp n X1I x1⁻¹) (ha : a < n) (hb : b < n) (hc : c < n) :
    ∀ (recs s : List ℕ) (S d : ℕ) (L : List Γ),
      walkAux n a b c X0 X0I X1 X1I recs s S d = true → s.length = d →
      (∀ C ∈ s, ∃ g ∈ H, Rp n C (g * t * g⁻¹)) → (∀ g ∈ L, g ∈ H) →
      (L.map fun g => kap n a b c (g * t * g⁻¹)).Nodup →
      (∀ k, S.testBit k = true ↔ k ∈ L.map fun g => kap n a b c (g * t * g⁻¹)) →
      ∃ L' : List Γ, (∀ g ∈ L', g ∈ H) ∧ (L'.map fun g => kap n a b c (g * t * g⁻¹)).Nodup ∧
        L'.length = L.length + recs.length
  | [], _, _, _, L, _, _, _, hL, hnd, _ => ⟨L, hL, hnd, rfl⟩
  | r :: rs, s, S, d, L, hw, hs, hC, hL, hnd, hS => by
    have e : walkAux n a b c X0 X0I X1 X1I (r :: rs) s S d = strictB (Nat.shiftRight r 1) fun p =>
        Nat.blt p d &&
        strictB (Bool.rec (motive := fun _ => Nat) (cjP n X1 X1I (topS (popS p s)))
          (cjP n X0 X0I (topS (popS p s))) (Nat.beq (Nat.land r 1) 0)) fun C =>
        strictB (keyP a b c C) fun k =>
        Nat.beq (Nat.land (Nat.shiftRight S k) 1) 0 &&
        strictB (Nat.lor S (Nat.shiftLeft 1 k)) fun S' =>
        strictB (Nat.succ (Nat.sub d p)) fun d' =>
          walkAux n a b c X0 X0I X1 X1I rs (C :: popS p s) S' d' := rfl
    rw [e] at hw
    simp only [strictB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hw
    obtain ⟨hp, hbit, hw⟩ := hw
    set p := Nat.shiftRight r 1
    have hne : popS p s ≠ [] := by
      rw [popS_eq, ne_eq, List.drop_eq_nil_iff]
      omega
    obtain ⟨g, hg, hpar⟩ := hC (topS (popS p s))
      (List.mem_of_mem_drop (i := p) (by rw [← popS_eq]; exact topS_mem hne))
    have hnew : ∀ B : Bool, ∃ g' ∈ H, Rp n (Bool.rec (motive := fun _ => Nat)
        (cjP n X1 X1I (topS (popS p s))) (cjP n X0 X0I (topS (popS p s))) B) (g' * t * g'⁻¹) := by
      intro B
      have conj : ∀ x : Γ, x * (g * t * g⁻¹) * x⁻¹ = (x * g) * t * (x * g)⁻¹ := fun x => by group
      cases B
      · exact ⟨x1 * g, H.mul_mem h1 hg, conj x1 ▸ rp_cjP hX1 hX1I hpar⟩
      · exact ⟨x0 * g, H.mul_mem h0 hg, conj x0 ▸ rp_cjP hX0 hX0I hpar⟩
    obtain ⟨g', hg', hC'⟩ := hnew (Nat.beq (Nat.land r 1) 0)
    rw [keyP_eq ha hb hc hC'] at hbit hw
    have hk := testBit_of_land hbit
    have hnot : kap n a b c (g' * t * g'⁻¹) ∉ L.map fun g => kap n a b c (g * t * g⁻¹) := by
      intro hm
      rw [← hS] at hm
      rw [hm] at hk
      exact Bool.noConfusion hk
    obtain ⟨L', hL', hnd', hlen⟩ := walkAux_sound h0 h1 hX0 hX0I hX1 hX1I ha hb hc rs _ _ _
      (g' :: L) hw (by rw [List.length_cons, popS_eq, List.length_drop, hs]; rfl)
      (fun C hm => by
        rcases List.mem_cons.1 hm with rfl | hm
        · exact ⟨g', hg', hC'⟩
        · exact hC C (List.mem_of_mem_drop (popS_eq s p ▸ hm)))
      (fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hg'
        · exact hL x hx)
      (by rw [List.map_cons]; exact List.nodup_cons.2 ⟨hnot, hnd⟩)
      (fun k => by rw [testBit_lor_one, hS, List.map_cons, List.mem_cons]; exact or_comm)
    refine ⟨L', hL', hnd', ?_⟩
    rw [hlen, List.length_cons, List.length_cons]
    omega

theorem walkK_sound {T : ℕ} {recs : List ℕ} (h0 : x0 ∈ H) (h1 : x1 ∈ H) (hX0 : Rp n X0 x0)
    (hX0I : Rp n X0I x0⁻¹) (hX1 : Rp n X1 x1) (hX1I : Rp n X1I x1⁻¹) (hT : Rp n T t)
    (ha : a < n) (hb : b < n) (hc : c < n) (h : walkK n a b c X0 X0I X1 X1I T recs = true) :
    ∃ L : List Γ, (∀ g ∈ L, g ∈ H) ∧ (L.map fun g => g * t * g⁻¹).Nodup ∧
      L.length = recs.length + 1 := by
  unfold walkK at h
  simp only [strictB_eq] at h
  have hT' : Rp n T ((1 : Γ) * t * (1 : Γ)⁻¹) := by rw [one_mul, inv_one, mul_one]; exact hT
  rw [keyP_eq ha hb hc hT'] at h
  obtain ⟨L, hL, hnd, hlen⟩ := walkAux_sound h0 h1 hX0 hX0I hX1 hX1I ha hb hc recs [T] _ 1 [1] h
    rfl (fun C hm => by rw [List.mem_singleton.1 hm]; exact ⟨1, H.one_mem, hT'⟩)
    (fun g hg => by rw [List.mem_singleton.1 hg]; exact H.one_mem) (List.nodup_singleton _)
    (fun k => by
      rw [show Nat.shiftLeft 1 (kap n a b c ((1 : Γ) * t * (1 : Γ)⁻¹)) =
        Nat.lor 0 (Nat.shiftLeft 1 (kap n a b c ((1 : Γ) * t * (1 : Γ)⁻¹))) from
        (Nat.zero_or _).symm, testBit_lor_one, Nat.zero_testBit]
      simp)
  refine ⟨L, hL, ?_, by rw [hlen, List.length_singleton, Nat.add_comm]⟩
  have e : (L.map fun g => kap n a b c (g * t * g⁻¹)) =
      (L.map fun g => g * t * g⁻¹).map (kap n a b c) := by
    rw [List.map_map]
    rfl
  rw [e] at hnd
  exact hnd.of_map _

theorem walkK_noFifteen [Finite Γ] {T m : ℕ} {recs : List ℕ} (h0 : x0 ∈ H) (h1 : x1 ∈ H)
    (hX0 : Rp n X0 x0) (hX0I : Rp n X0I x0⁻¹) (hX1 : Rp n X1 x1) (hX1I : Rp n X1I x1⁻¹)
    (hT : Rp n T t) (ha : a < n) (hb : b < n) (hc : c < n)
    (h : walkK n a b c X0 X0I X1 X1I T recs = true) (htH : t ∈ H) (ht : orderOf t = 5)
    (hH : Nat.card H = 5 * m) (hm : ¬ 5 ∣ m) (hlen : Nat.card H < 15 * (recs.length + 1)) :
    ∀ z ∈ H, orderOf z ≠ 15 := by
  obtain ⟨L, hL, hnd, hl⟩ := walkK_sound h0 h1 hX0 hX0I hX1 hX1I hT ha hb hc h
  exact no_orderOf_fifteen hH hm htH ht L hL hnd (by rw [hl]; exact hlen)

end Group

end CFSG.KC.ConjWalk

end
