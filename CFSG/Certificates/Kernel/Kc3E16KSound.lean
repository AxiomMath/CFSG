module

public import Certificates.Data.Kernel.Kc3E16K
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.Kc3K

open CFSG.KC.Enum

theorem strictB_eqK (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem packL_cons (w x : Nat) (l : List Nat) : packL w (x :: l) = x + 2 ^ w * packL w l := by
  have e : packL w (x :: l) = x + (packL w l <<< w) := rfl
  rw [e, Nat.shiftLeft_eq, Nat.mul_comm]

theorem packL_inj {w : Nat} : ∀ {l l' : List Nat}, l.length = l'.length → (∀ x ∈ l, x < 2 ^ w) →
    (∀ x ∈ l', x < 2 ^ w) → packL w l = packL w l' → l = l'
  | [], [], _, _, _, _ => rfl
  | x :: l, x' :: l', hlen, hl, hl', h => by
    rw [packL_cons, packL_cons] at h
    have hx : x < 2 ^ w := hl x (by simp)
    have hx' : x' < 2 ^ w := hl' x' (by simp)
    have e1 : x = x' := by
      have := congrArg (· % 2 ^ w) h
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hx'] at this
      exact this
    have e2 : packL w l = packL w l' := by
      have := congrArg (· / 2 ^ w) h
      have hp : 0 < 2 ^ w := Nat.two_pow_pos w
      simp only [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hx',
        Nat.zero_add] at this
      exact this
    rw [e1, packL_inj (by simpa using hlen) (fun y hy => hl y (by simp [hy]))
      (fun y hy => hl' y (by simp [hy])) e2]

theorem eq_of_packL {w : Nat} {B : List Nat} {f g : Nat → Nat} (hf : ∀ b ∈ B, f b < 2 ^ w)
    (hg : ∀ b ∈ B, g b < 2 ^ w) (h : packL w (B.map f) = packL w (B.map g)) :
    ∀ b ∈ B, f b = g b := by
  have e := packL_inj (by simp) (by simpa using hf) (by simpa using hg) h
  intro b hb
  exact List.map_inj_left.1 e b hb

theorem testBit_maskL : ∀ (l : List Nat) (p : Nat), (maskL l).testBit p = true ↔ p ∈ l
  | [], p => by simp [maskL]
  | x :: l, p => by
    have e : maskL (x :: l) = Nat.lor (Nat.shiftLeft 1 x) (maskL l) := rfl
    rw [e]
    change ((1 <<< x) ||| maskL l).testBit p = true ↔ _
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
      testBit_maskL l p, List.mem_cons, decide_eq_true_eq]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h

theorem cntIn_eq (F : Nat) : ∀ l : List Nat, cntIn F l = (l.filter fun p => F.testBit p).length
  | [] => rfl
  | p :: l => by
    have e : cntIn F (p :: l) = cond (F.testBit p) (Nat.succ (cntIn F l)) (cntIn F l) := rfl
    rw [e, cntIn_eq F l, List.filter_cons]
    cases F.testBit p <;> simp

theorem chainLt_sorted : ∀ l : List Nat, chainLt l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    have e : chainLt (a :: b :: l) = (decide (a < b) && chainLt (b :: l)) := rfl
    rw [e, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := chainLt_sorted (b :: l) h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact lt_trans h.1 (List.rel_of_pairwise_cons ih hc)

section Specs

variable {w m : Nat} {TF : Nat → Nat}

theorem elK_spec {NN N M : Nat} {B gs : List Nat} {eu ev ky iv kv : Nat → Nat}
    {tg : Nat → Nat → Nat} {k : Nat} (h : elK w m NN N M TF B gs eu ev ky iv kv tg k = true) :
    eu k < NN ∧ ev k < NN ∧ ky k = packL w (B.map fun b => exK w m TF (eu k) (ev k) b) ∧
    (∀ c < gs.length, tg c k < N ∧ ky (tg c k) =
      packL w (B.map fun b => pg w m (TF (gs.getD c 0)) (exK w m TF (eu k) (ev k) b))) ∧
    ((∀ b ∈ B, exK w m TF (eu k) (ev k) (exK w m TF (eu k) (ev k) b) = b) →
      (∃ b ∈ B, exK w m TF (eu k) (ev k) b ≠ b) → iv k < M ∧ kv (iv k) = k) := by
  unfold elK at h
  rw [strictB_eqK, strictB_eqK] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hu, hv⟩, hk⟩, hc⟩, hi⟩ := h
  refine ⟨of_decide_eq_true hu, of_decide_eq_true hv, beq_iff_eq.1 hk, fun c hc' => ?_,
    fun hsq hmv => ?_⟩
  · have hc2 := List.all_eq_true.1 hc c (List.mem_range.2 hc')
    rw [Bool.and_eq_true] at hc2
    exact ⟨of_decide_eq_true hc2.1, beq_iff_eq.1 hc2.2⟩
  · have hs : B.all (fun b => exK w m TF (eu k) (ev k) (exK w m TF (eu k) (ev k) b) == b) =
        true := List.all_eq_true.2 fun b hb => beq_iff_eq.2 (hsq b hb)
    have hm : B.any (fun b => exK w m TF (eu k) (ev k) b != b) = true := by
      obtain ⟨b, hb, hne⟩ := hmv
      exact List.any_eq_true.2 ⟨b, hb, bne_iff_ne.2 hne⟩
    rw [hs, hm] at hi
    simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hi
    exact ⟨of_decide_eq_true hi.1, beq_iff_eq.1 hi.2⟩

theorem ivK_spec {N M R : Nat} {B : List Nat} {eu ev ky kv vu vv rt cj ri : Nat → Nat}
    {FR FL : Nat → List Nat} {FM : Nat → Nat} {i : Nat}
    (h : ivK w m N M R TF B eu ev ky kv vu vv rt cj ri FR FL FM i = true) :
    kv i < N ∧ vu i = eu (kv i) ∧ vv i = ev (kv i) ∧ (i + 1 < M → ky (kv i) < ky (kv (i + 1))) ∧
    rt i < R ∧ ri (rt i) < M ∧ cj i < N ∧
    (∀ b ∈ B, exK w m TF (vu i) (vv i) (exK w m TF (eu (cj i)) (ev (cj i)) b) =
      exK w m TF (eu (cj i)) (ev (cj i)) (exK w m TF (vu (ri (rt i))) (vv (ri (rt i))) b)) ∧
    FL i = (FR (rt i)).map (exK w m TF (eu (cj i)) (ev (cj i))) ∧ FM i = maskL (FL i) := by
  unfold ivK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  rw [strictB_eqK, strictB_eqK, strictB_eqK] at h8
  simp only [Bool.and_eq_true] at h8
  obtain ⟨⟨h8a, h8b⟩, h8c⟩ := h8
  refine ⟨of_decide_eq_true h1, beq_iff_eq.1 h2, beq_iff_eq.1 h3, fun hi => ?_,
    of_decide_eq_true h5, of_decide_eq_true h6, of_decide_eq_true h7,
    fun b hb => beq_iff_eq.1 (List.all_eq_true.1 h8a b hb), beq_iff_eq.1 h8b, beq_iff_eq.1 h8c⟩
  rw [Bool.or_eq_true] at h4
  rcases h4 with h4 | h4
  · simp [hi] at h4
  · exact of_decide_eq_true h4

theorem rtK_spec {n M : Nat} {vu vv ri : Nat → Nat} {FR : Nat → List Nat} {ρ : Nat}
    (h : rtK w m n M TF vu vv ri FR ρ = true) :
    ri ρ < M ∧ (FR ρ).Pairwise (· < ·) ∧
    (∀ p ∈ FR ρ, p < n ∧ exK w m TF (vu (ri ρ)) (vv (ri ρ)) p = p) ∧
    ((List.range n).filter fun p => exK w m TF (vu (ri ρ)) (vv (ri ρ)) p == p).length =
      (FR ρ).length := by
  unfold rtK at h
  rw [Bool.and_eq_true, strictB_eqK, strictB_eqK] at h
  obtain ⟨h1, h2⟩ := h
  simp only [Bool.and_eq_true] at h2
  obtain ⟨⟨h2, h3⟩, h4⟩ := h2
  refine ⟨of_decide_eq_true h1, chainLt_sorted _ h2, fun p hp => ?_, beq_iff_eq.1 h4⟩
  have h5 := List.all_eq_true.1 h3 p hp
  rw [Bool.and_eq_true] at h5
  exact ⟨of_decide_eq_true h5.1, beq_iff_eq.1 h5.2⟩

theorem prK_spec {M : Nat} {B : List Nat} {ky kv vu vv : Nat → Nat} {pr ct : Nat → Nat → Nat}
    {FL : Nat → List Nat} {FM : Nat → Nat} {i : Nat}
    (h : prK w m M TF B ky kv vu vv pr ct FL FM i = true) :
    ∀ j < M, pr i j = pr j i ∧ (i < j → (pr i j < M →
      ky (kv (pr i j)) = packL w (B.map fun b =>
        exK w m TF (vu i) (vv i) (exK w m TF (vu j) (vv j) b)) ∧
      ct i j = ct j i ∧ ct i j = cntIn (FM j) (FL i)) ∧
      (¬ pr i j < M → ∃ b ∈ B, exK w m TF (vu i) (vv i) (exK w m TF (vu j) (vv j) b) ≠
        exK w m TF (vu j) (vv j) (exK w m TF (vu i) (vv i) b))) := by
  intro j hj
  unfold prK at h
  simp only [strictB_eqK, List.all_eq_true, List.mem_range] at h
  have hj' := h j hj
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at hj'
  obtain ⟨hs, hr⟩ := hj'
  refine ⟨hs, fun hij => ?_⟩
  rcases hr with hr | hr
  · exact absurd hij hr
  · by_cases hp : pr i j < M
    · simp only [hp, decide_true, cond_true, Bool.and_eq_true, beq_iff_eq] at hr
      exact ⟨fun _ => ⟨hr.1.1, hr.1.2, hr.2⟩, fun h' => absurd hp h'⟩
    · simp only [hp, decide_false, cond_false, List.any_eq_true, bne_iff_ne, ne_eq] at hr
      exact ⟨fun h' => absurd h' hp, fun _ => hr⟩

theorem nbK_spec {M : Nat} {pr : Nat → Nat → Nat} {NB : Nat → List Nat} {NM : Nat → Nat} {i : Nat}
    (h : nbK M pr NB NM i = true) :
    NB i = (List.range M).filter (fun j => decide (pr i j < M)) ∧ NM i = maskL (NB i) := by
  unfold nbK at h
  simpa only [Bool.and_eq_true, beq_iff_eq] using h

end Specs

end CFSG.KC.Kc3K

end
