module

public import Certificates.Data.Kernel.M22Out.Replay
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutTab47Check
import all CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutTab47Check
public import Mathlib.RingTheory.WittVector.IsPoly
public import Std.Data.HashSet.Lemmas
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KC.M22Out

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.OutCheck

@[expose] def ValidT (t : Tab) : Prop := t.length = 22 ∧ ∀ a ∈ t, a < 22

private theorem getD_of_lt {α : Type} {l : List α} {d : α} {i : Nat} (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

private theorem getD_mem {α : Type} {l : List α} {d : α} {i : Nat} (h : i < l.length) :
    l.getD i d ∈ l := by
  rw [getD_of_lt h]
  exact List.getElem_mem h

theorem strictK_eq {β : Sort _} (y : Nat) (k : Nat → β) : strictK y k = k y := by
  cases y <;> rfl

private theorem packL32_lt : ∀ l : List Nat, (∀ a ∈ l, a < 32) → packL 32 l < 32 ^ l.length
  | [], _ => by
    change 0 < 1
    omega
  | a :: l, h => by
    have ha := h a (by simp)
    have hl := packL32_lt l fun b hb => h b (by simp [hb])
    change a + 32 * packL 32 l < 32 ^ (l.length + 1)
    rw [Nat.pow_succ]
    generalize 32 ^ l.length = X at hl ⊢
    omega

private theorem packL32_inj : ∀ l₁ l₂ : List Nat, l₁.length = l₂.length → (∀ a ∈ l₁, a < 32) →
    (∀ a ∈ l₂, a < 32) → packL 32 l₁ = packL 32 l₂ → l₁ = l₂
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _ => by simp at h
  | a :: l₁, b :: l₂, hl, h₁, h₂, h => by
    have ha := h₁ a (by simp)
    have hb := h₂ b (by simp)
    change a + 32 * packL 32 l₁ = b + 32 * packL 32 l₂ at h
    have hab : a = b := by omega
    have hr : packL 32 l₁ = packL 32 l₂ := by omega
    rw [hab, packL32_inj l₁ l₂ (by simpa using hl) (fun x hx => h₁ x (by simp [hx]))
      (fun x hx => h₂ x (by simp [hx])) hr]

theorem packT_inj {a b : Tab} (ha : ValidT a) (hb : ValidT b) (h : packT a = packT b) : a = b :=
  packL32_inj a b (ha.1.trans hb.1.symm) (fun x hx => by have := ha.2 x hx; omega)
    (fun x hx => by have := hb.2 x hx; omega) h

private theorem packT_lt {t : Tab} (h : ValidT t) : packT t < 2 ^ 110 := by
  have := packL32_lt t fun x hx => by have := h.2 x hx; omega
  rw [h.1] at this
  exact Nat.lt_of_lt_of_le this (by decide)

theorem lane_pack {α : Type} (f : α → Nat) (B : Nat) (pk : List α → Nat)
    (hcons : ∀ x L, pk (x :: L) = f x + B * pk L) :
    ∀ (L : List α) (k : Nat), (∀ x ∈ L, f x < B) → (hk : k < L.length) →
      pk L / B ^ k % B = f L[k]
  | [], k, _, hk => absurd hk (Nat.not_lt_zero k)
  | x :: L, 0, hf, _ => by
    rw [hcons, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (hf x (by simp))]
    rfl
  | x :: L, k + 1, hf, hk => by
    have hx := hf x (by simp)
    have hB : 0 < B := Nat.lt_of_le_of_lt (Nat.zero_le _) hx
    rw [hcons, Nat.pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hB,
      Nat.div_eq_of_lt hx, Nat.zero_add]
    exact lane_pack f B pk hcons L k (fun y hy => hf y (by simp [hy])) (by simpa using hk)

theorem laneW_eq (w P k : Nat) : laneW w (2 ^ w - 1) P k = P / 2 ^ (w * k) % 2 ^ w := by
  change (P >>> (w * k)) &&& (2 ^ w - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

private theorem packTs_cons (t : Tab) (T : List Tab) :
    packTs (t :: T) = packT t + 2 ^ 110 * packTs T := rfl

private theorem packW_cons (w : List Nat) (W : List (List Nat)) :
    packW (w :: W) = encW w + 2 ^ 17 * packW W := rfl

theorem tabAt_packTs {T : List Tab} (hv : ∀ t ∈ T, ValidT t) {k : Nat} (hk : k < T.length) :
    tabAt (packTs T) k = packT T[k] := by
  change laneW 110 (2 ^ 110 - 1) (packTs T) k = _
  rw [laneW_eq, Nat.pow_mul]
  exact lane_pack packT (2 ^ 110) packTs packTs_cons T k (fun t ht => packT_lt (hv t ht)) hk

theorem wordAt_packW {W : List (List Nat)} (hv : ∀ w ∈ W, encW w < 2 ^ 17) {k : Nat}
    (hk : k < W.length) : wordAt (packW W) k = encW W[k] := by
  change laneW 17 (2 ^ 17 - 1) (packW W) k = _
  rw [laneW_eq, Nat.pow_mul]
  exact lane_pack encW (2 ^ 17) packW packW_cons W k hv hk

private theorem encW_cons (i : Nat) (w : List Nat) : encW (i :: w) = i + 2 * encW w := rfl

private theorem encW_pos : ∀ w : List Nat, 0 < encW w
  | [] => Nat.one_pos
  | i :: w => by
    rw [encW_cons]
    have := encW_pos w
    omega

private theorem encW_lt : ∀ w : List Nat, (∀ i ∈ w, i < 2) → encW w < 2 ^ (w.length + 1)
  | [], _ => by decide
  | i :: w, h => by
    have hi := h i (by simp)
    have hw := encW_lt w fun j hj => h j (by simp [hj])
    rw [encW_cons, List.length_cons, Nat.pow_succ]
    generalize 2 ^ (w.length + 1) = X at hw ⊢
    omega

private theorem encW_inj : ∀ v w : List Nat, (∀ i ∈ v, i < 2) → (∀ i ∈ w, i < 2) →
    encW v = encW w → v = w
  | [], [], _, _, _ => rfl
  | [], j :: w, _, _, h => by
    rw [encW_cons] at h
    have := encW_pos w
    change 1 = _ at h
    omega
  | i :: v, [], _, _, h => by
    rw [encW_cons] at h
    have := encW_pos v
    change _ = 1 at h
    omega
  | i :: v, j :: w, hv, hw, h => by
    rw [encW_cons, encW_cons] at h
    have hi := hv i (by simp)
    have hj := hw j (by simp)
    have hij : i = j := by omega
    have he : encW v = encW w := by omega
    rw [hij, encW_inj v w (fun x hx => hv x (by simp [hx])) (fun x hx => hw x (by simp [hx])) he]

theorem tmul_valid {g t : Tab} (hg : ValidT g) (ht : ValidT t) : ValidT (tmul g t) := by
  refine ⟨by simp [tmul, ht.1], fun a ha => ?_⟩
  simp only [tmul, List.mem_map] at ha
  obtain ⟨j, hj, rfl⟩ := ha
  have hj' : j < g.length := by rw [hg.1]; exact ht.2 j hj
  rw [getD_of_lt hj']
  exact hg.2 _ (List.getElem_mem hj')

private theorem blt_dec (a b : Nat) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_iff]

private theorem beq_dec (a b : Nat) : Nat.beq a b = decide (a = b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]

private theorem stepK_eq (TP WP : Nat) (g t : Tab) (i e k q c : Nat) :
    stepK TP WP g t i e k q c =
      if q < c ∧ packT (tmul g t) = tabAt TP k then
        (if k = c then (if wordAt WP c = i + 2 * e then c + 1 else 0)
          else if k < c then c else 0)
      else 0 := by
  unfold stepK
  have hw2 : Nat.add i (Nat.mul (nat_lit 2) e) = i + 2 * e := rfl
  rw [hw2]
  simp only [blt_dec, beq_dec]
  by_cases h1 : q < c <;> by_cases h2 : packT (tmul g t) = tabAt TP k <;> simp [h1, h2]
  by_cases h3 : k = c
  · by_cases h4 : wordAt WP c = i + 2 * e <;> simp [h3, h4]
  · by_cases h5 : k < c <;> simp [h3, h5]

private theorem stepK_zero (TP WP : Nat) (g t : Tab) (i e k q : Nat) :
    stepK TP WP g t i e k q 0 = 0 := by
  rw [stepK_eq, if_neg (fun h => Nat.not_lt_zero q h.1)]

private theorem stepK_mono {TP WP : Nat} {g t : Tab} {i e k q c : Nat}
    (h : stepK TP WP g t i e k q c ≠ 0) : c ≤ stepK TP WP g t i e k q c := by
  rw [stepK_eq] at h ⊢
  split_ifs at h ⊢ <;> omega

private theorem replayK_cons (TP WP : Nat) (g₀ g₁ t : Tab) (Ts : List Tab) (E : List Nat)
    (KK : List (List Nat)) (q c : Nat) :
    replayK TP WP g₀ g₁ (t :: Ts) E KK q c =
      replayK TP WP g₀ g₁ Ts E.tail KK.tail (q + 1)
        (stepK TP WP g₁ t 1 (E.headD 0) ((KK.headD []).getD 1 0) q
          (stepK TP WP g₀ t 0 (E.headD 0) ((KK.headD []).getD 0 0) q c)) := by
  change strictK _ _ = _
  rw [strictK_eq, strictK_eq]
  rfl

private theorem replayK_zero (TP WP : Nat) (g₀ g₁ : Tab) :
    ∀ (Ts : List Tab) (E : List Nat) (KK : List (List Nat)) (q : Nat),
      replayK TP WP g₀ g₁ Ts E KK q 0 = 0
  | [], _, _, _ => rfl
  | t :: Ts, E, KK, q => by
    rw [replayK_cons, stepK_zero, stepK_zero]
    exact replayK_zero TP WP g₀ g₁ Ts _ _ _

private theorem replayK_mono (TP WP : Nat) (g₀ g₁ : Tab) :
    ∀ (Ts : List Tab) (E : List Nat) (KK : List (List Nat)) (q c : Nat),
      replayK TP WP g₀ g₁ Ts E KK q c ≠ 0 → c ≤ replayK TP WP g₀ g₁ Ts E KK q c
  | [], _, _, _, _, _ => Nat.le_refl _
  | t :: Ts, E, KK, q, c, h => by
    rw [replayK_cons] at h ⊢
    generalize hc₁ : stepK TP WP g₀ t 0 (E.headD 0) ((KK.headD []).getD 0 0) q c = c₁ at h ⊢
    generalize hc₂ : stepK TP WP g₁ t 1 (E.headD 0) ((KK.headD []).getD 1 0) q c₁ = c₂ at h ⊢
    have h₂ : c₂ ≠ 0 := fun e => h (by rw [e, replayK_zero])
    have h₁ : c₁ ≠ 0 := fun e => h₂ (by rw [← hc₂, e, stepK_zero])
    have m₀ : c ≤ c₁ := by
      rw [← hc₁]
      exact stepK_mono (by rw [hc₁]; exact h₁)
    have m₁ : c₁ ≤ c₂ := by
      rw [← hc₂]
      exact stepK_mono (by rw [hc₂]; exact h₂)
    exact Nat.le_trans m₀ (Nat.le_trans m₁ (replayK_mono TP WP g₀ g₁ Ts _ _ _ _ h))

theorem replayK_append (TP WP : Nat) (g₀ g₁ : Tab) :
    ∀ (A B : List Tab) (E : List Nat) (KK : List (List Nat)) (q c : Nat),
      replayK TP WP g₀ g₁ (A ++ B) E KK q c =
        replayK TP WP g₀ g₁ B (E.drop A.length) (KK.drop A.length) (q + A.length)
          (replayK TP WP g₀ g₁ A E KK q c)
  | [], B, E, KK, q, c => by
    rw [List.nil_append, List.length_nil, List.drop_zero, List.drop_zero, Nat.add_zero]
    rfl
  | t :: A, B, E, KK, q, c => by
    rw [List.cons_append, replayK_cons, replayK_cons, replayK_append TP WP g₀ g₁ A,
      List.length_cons, List.drop_tail, List.drop_tail, Nat.add_assoc, Nat.add_comm 1 A.length]

private theorem stepK_mem {T : List Tab} (hv : ∀ t ∈ T, ValidT t) {WP : Nat} {g t : Tab}
    {i e k q c : Nat} (hp : ValidT (tmul g t)) (h : stepK (packTs T) WP g t i e k q c ≠ 0)
    (hle : stepK (packTs T) WP g t i e k q c ≤ T.length) : tmul g t ∈ T := by
  rw [stepK_eq] at h hle
  by_cases hcond : q < c ∧ packT (tmul g t) = tabAt (packTs T) k
  swap
  · rw [if_neg hcond] at h
    exact absurd rfl h
  rw [if_pos hcond] at h hle
  have hk : k < T.length := by
    split_ifs at h hle <;> omega
  rw [packT_inj hp (hv _ (List.getElem_mem hk)) (by rw [hcond.2, tabAt_packTs hv hk])]
  exact List.getElem_mem hk

section Bfs

variable (gens T W : List Tab) (KK : List (List Nat))

private noncomputable def RR (q c : Nat) : Nat :=
  replayK (packTs T) (packW W) (gens.getD 0 idTab) (gens.getD 1 idTab) (T.drop q)
    ((W.map encW).drop q) (KK.drop q) q c

private def kAt (q i : Nat) : Nat := ((KK.drop q).headD []).getD i 0

private def innerF (G : Array Tab) (t : Tab) (w : List Nat)
    (st : Std.HashSet Tab × Array (Tab × List Nat)) (i : Nat) :
    Std.HashSet Tab × Array (Tab × List Nat) :=
  if st.1.contains (tmul G[i]! t) then st
  else (st.1.insert (tmul G[i]! t), st.2.push (tmul G[i]! t, i :: w))

private def pairF (G : Array Tab) (st : Std.HashSet Tab × Array (Tab × List Nat))
    (p : Tab × List Nat) : Std.HashSet Tab × Array (Tab × List Nat) :=
  (List.range G.size).foldl (innerF G p.1 p.2) st

private theorem bfsLayer_eq (G : Array Tab) (seen : Std.HashSet Tab)
    (F : Array (Tab × List Nat)) :
    bfsLayer G seen F = F.toList.foldl (pairF G) (seen, #[]) := by
  rw [Array.foldl_toList]
  rfl

private structure Setup : Prop where
  g2 : gens.length = 2
  gv : ∀ g ∈ gens, ValidT g
  tv : ∀ t ∈ T, ValidT t
  nd : T.Nodup
  wl : W.length = T.length
  wb : ∀ w ∈ W, w.length < 17 ∧ ∀ i ∈ w, i < 2

private structure BfsMatch (b c d : Nat) (st : Std.HashSet Tab × Array (Tab × List Nat)) :
    Prop where
  seen : ∀ y, st.1.contains y = true ↔ ∃ j < c, T.getD j [] = y
  next : st.2.toList = (List.range' b (c - b)).map fun j => (T.getD j [], W.getD j [])
  len : ∀ j, b ≤ j → j < c → (W.getD j []).length = d + 1
  wt : ∀ j < c, wordTab gens (W.getD j []) = T.getD j []

variable {gens T W KK}

private theorem RR_succ {q : Nat} (hs : Setup gens T W) (hq : q < T.length) (c : Nat) :
    RR gens T W KK q c =
      RR gens T W KK (q + 1)
        (stepK (packTs T) (packW W) (gens.getD 1 idTab) (T.getD q []) 1 (encW (W.getD q []))
          (kAt KK q 1) q
          (stepK (packTs T) (packW W) (gens.getD 0 idTab) (T.getD q []) 0 (encW (W.getD q []))
            (kAt KK q 0) q c)) := by
  have hqW : q < (W.map encW).length := by rw [List.length_map, hs.wl]; exact hq
  have hE : (W.map encW).drop q = encW (W.getD q []) :: (W.map encW).drop (q + 1) := by
    rw [List.drop_eq_getElem_cons hqW, List.getElem_map,
      getD_of_lt (l := W) (d := []) (i := q) (by rw [hs.wl]; exact hq)]
  unfold RR
  rw [List.drop_eq_getElem_cons hq, replayK_cons, ← getD_of_lt (d := []) hq, hE, List.tail_drop]
  rfl

private theorem RR_zero (q : Nat) : RR gens T W KK q 0 = 0 := replayK_zero _ _ _ _ _ _ _ _

private theorem RR_mono {q c : Nat} (h : RR gens T W KK q c ≠ 0) : c ≤ RR gens T W KK q c :=
  replayK_mono _ _ _ _ _ _ _ _ _ h

private theorem closed_aux (hs : Setup gens T W) :
    ∀ n q c, q + n = T.length → RR gens T W KK q c = T.length →
      ∀ j, q ≤ j → j < T.length → ∀ i < 2, tmul (gens.getD i idTab) (T.getD j []) ∈ T := by
  intro n
  induction n with
  | zero =>
    intro q c hq _ j h1 h2
    omega
  | succ n ih =>
    intro q c hq hr j h1 h2 i hi
    have hqN : q < T.length := by omega
    rw [RR_succ hs hqN] at hr
    generalize hc₁ : stepK (packTs T) (packW W) (gens.getD 0 idTab) (T.getD q []) 0
      (encW (W.getD q [])) (kAt KK q 0) q c = c₁ at hr
    generalize hc₂ : stepK (packTs T) (packW W) (gens.getD 1 idTab) (T.getD q []) 1
      (encW (W.getD q [])) (kAt KK q 1) q c₁ = c₂ at hr
    have h₂ : c₂ ≠ 0 := fun e => by rw [e, RR_zero] at hr; omega
    have h₁ : c₁ ≠ 0 := fun e => h₂ (by rw [← hc₂, e, stepK_zero])
    have l₂ : c₂ ≤ T.length := by
      have := RR_mono (gens := gens) (T := T) (W := W) (KK := KK) (q := q + 1) (c := c₂)
        (by omega)
      omega
    have m₁ : c₁ ≤ c₂ := by
      rw [← hc₂]
      exact stepK_mono (by rw [hc₂]; exact h₂)
    rcases Nat.lt_or_ge q j with hj | hj
    · exact ih (q + 1) c₂ (by omega) hr j hj h2 i hi
    · have hjq : j = q := by omega
      rw [hjq]
      have hil : i < gens.length := by rw [hs.g2]; exact hi
      have hp := tmul_valid (hs.gv _ (getD_mem (d := idTab) hil))
        (hs.tv _ (getD_mem (d := []) hqN))
      rcases (by omega : i = 0 ∨ i = 1) with hi0 | hi1
      · rw [hi0] at hp ⊢
        have e₁ : stepK (packTs T) (packW W) (gens.getD 0 idTab) (T.getD q []) 0
            (encW (W.getD q [])) (kAt KK q 0) q c ≠ 0 := by rw [hc₁]; exact h₁
        have e₂ : stepK (packTs T) (packW W) (gens.getD 0 idTab) (T.getD q []) 0
            (encW (W.getD q [])) (kAt KK q 0) q c ≤ T.length := by rw [hc₁]; omega
        exact stepK_mem hs.tv hp e₁ e₂
      · rw [hi1] at hp ⊢
        have e₁ : stepK (packTs T) (packW W) (gens.getD 1 idTab) (T.getD q []) 1
            (encW (W.getD q [])) (kAt KK q 1) q c₁ ≠ 0 := by rw [hc₂]; exact h₂
        have e₂ : stepK (packTs T) (packW W) (gens.getD 1 idTab) (T.getD q []) 1
            (encW (W.getD q [])) (kAt KK q 1) q c₁ ≤ T.length := by rw [hc₂]; exact l₂
        exact stepK_mem hs.tv hp e₁ e₂

private theorem inner_step (hs : Setup gens T W) {b c d q i : Nat} (hi : i < 2) (hq : q < c)
    (hbc : b ≤ c) (hqd : (W.getD q []).length = d)
    {st : Std.HashSet Tab × Array (Tab × List Nat)} (hm : BfsMatch gens T W b c d st)
    (hne : stepK (packTs T) (packW W) (gens.getD i idTab) (T.getD q []) i (encW (W.getD q []))
      (kAt KK q i) q c ≠ 0)
    (hle : stepK (packTs T) (packW W) (gens.getD i idTab) (T.getD q []) i (encW (W.getD q []))
      (kAt KK q i) q c ≤ T.length) :
    BfsMatch gens T W b
      (stepK (packTs T) (packW W) (gens.getD i idTab) (T.getD q []) i (encW (W.getD q []))
        (kAt KK q i) q c) d
      (innerF gens.toArray (T.getD q []) (W.getD q []) st i) := by
  have hc0 := stepK_mono hne
  have hcN : c ≤ T.length := Nat.le_trans hc0 hle
  have hqN : q < T.length := Nat.lt_of_lt_of_le hq hcN
  have hqW : q < W.length := by rw [hs.wl]; exact hqN
  have hil : i < gens.length := by rw [hs.g2]; exact hi
  have hG : gens.toArray[i]! = gens.getD i idTab := by
    rw [getElem!_pos gens.toArray i (by simpa using hil), List.getElem_toArray, getD_of_lt hil]
  have hgv : ValidT (gens.getD i idTab) := hs.gv _ (getD_mem hil)
  have htq : ValidT (T.getD q []) := hs.tv _ (getD_mem hqN)
  have hpv := tmul_valid hgv htq
  generalize hk : kAt KK q i = k at hne hle ⊢
  rw [stepK_eq] at hne hle ⊢
  unfold innerF
  rw [hG]
  by_cases hcond : q < c ∧ packT (tmul (gens.getD i idTab) (T.getD q [])) = tabAt (packTs T) k
  swap
  · rw [if_neg hcond] at hne
    exact absurd rfl hne
  rw [if_pos hcond] at hne hle ⊢
  by_cases hkc : k = c
  · rw [if_pos hkc] at hne hle ⊢
    by_cases hw : wordAt (packW W) c = i + 2 * encW (W.getD q [])
    swap
    · rw [if_neg hw] at hne
      exact absurd rfl hne
    rw [if_pos hw] at hle ⊢
    have hcN' : c < T.length := hle
    have hcW : c < W.length := by rw [hs.wl]; exact hcN'
    have hpk : packT (tmul (gens.getD i idTab) (T.getD q [])) = tabAt (packTs T) c := by
      rw [← hkc]
      exact hcond.2
    have ht : tmul (gens.getD i idTab) (T.getD q []) = T.getD c [] := by
      apply packT_inj hpv (hs.tv _ (getD_mem hcN'))
      rw [hpk, tabAt_packTs hs.tv hcN', getD_of_lt hcN']
    have hwbin : ∀ w ∈ W, encW w < 2 ^ 17 := fun w hw' => by
      have := encW_lt w (hs.wb w hw').2
      exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by have := (hs.wb w hw').1; omega))
    have hwk : W.getD c [] = i :: W.getD q [] := by
      apply encW_inj _ _ (hs.wb _ (getD_mem (l := W) (d := []) (i := c) hcW)).2
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hi
        · exact (hs.wb _ (getD_mem (l := W) (d := []) (i := q) hqW)).2 x hx
      rw [encW_cons, ← hw, wordAt_packW hwbin hcW, getD_of_lt hcW]
    have hnot : st.1.contains (T.getD c []) = false := by
      cases e : st.1.contains (T.getD c [])
      · rfl
      · obtain ⟨j, hj, ej⟩ := (hm.seen _).1 e
        have := (hs.nd.getD_inj (fallback := []) (Nat.lt_trans hj hcN') hcN').1 ej
        omega
    rw [ht, hnot, if_neg Bool.false_ne_true]
    refine ⟨fun y => ?_, ?_, fun j hj1 hj2 => ?_, fun j hj => ?_⟩
    · dsimp only
      rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, hm.seen]
      constructor
      · rintro (e | ⟨j, hj, e⟩)
        · exact ⟨c, Nat.lt_succ_self c, e⟩
        · exact ⟨j, by omega, e⟩
      · rintro ⟨j, hj, e⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · exact Or.inr ⟨j, hj, e⟩
        · rw [hj] at e
          exact Or.inl e
    · dsimp only
      rw [Array.toList_push, hm.next]
      have e1 : c + 1 - b = (c - b) + 1 := by omega
      rw [e1, List.range'_concat, List.map_append]
      have e2 : b + 1 * (c - b) = c := by omega
      rw [e2]
      simp only [List.map_cons, List.map_nil, hwk]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj2 with hj2 | hj2
      · exact hm.len j hj1 hj2
      · rw [hj2, hwk, List.length_cons, hqd]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact hm.wt j hj
      · rw [hj, hwk]
        change tmul (gens.getD i idTab) (wordTab gens (W.getD q [])) = _
        rw [hm.wt q hq, ht]
  · rw [if_neg hkc] at hne hle ⊢
    by_cases hkl : k < c
    swap
    · rw [if_neg hkl] at hne
      exact absurd rfl hne
    rw [if_pos hkl]
    have hkN : k < T.length := Nat.lt_of_lt_of_le hkl hcN
    have ht : tmul (gens.getD i idTab) (T.getD q []) = T.getD k [] := by
      apply packT_inj hpv (hs.tv _ (getD_mem hkN))
      rw [hcond.2, tabAt_packTs hs.tv hkN, getD_of_lt hkN]
    rw [ht, if_pos ((hm.seen _).2 ⟨k, hkl, rfl⟩)]
    exact hm

private theorem pair_step (hs : Setup gens T W) {b c d q : Nat} (hq : q < c) (hbc : b ≤ c)
    (hqd : (W.getD q []).length = d) {st : Std.HashSet Tab × Array (Tab × List Nat)}
    (hm : BfsMatch gens T W b c d st) (hr : RR gens T W KK q c = T.length) (hN : 0 < T.length) :
    ∃ c', c ≤ c' ∧ BfsMatch gens T W b c' d (pairF gens.toArray st (T.getD q [], W.getD q [])) ∧
      RR gens T W KK (q + 1) c' = T.length := by
  have hcN : c ≤ T.length := by
    have := RR_mono (gens := gens) (T := T) (W := W) (KK := KK) (q := q) (c := c) (by omega)
    omega
  rw [RR_succ hs (by omega)] at hr
  generalize hc₁ : stepK (packTs T) (packW W) (gens.getD 0 idTab) (T.getD q []) 0
    (encW (W.getD q [])) (kAt KK q 0) q c = c₁ at hr
  generalize hc₂ : stepK (packTs T) (packW W) (gens.getD 1 idTab) (T.getD q []) 1
    (encW (W.getD q [])) (kAt KK q 1) q c₁ = c₂ at hr
  have h₂ : c₂ ≠ 0 := fun e => by rw [e, RR_zero] at hr; omega
  have h₁ : c₁ ≠ 0 := fun e => h₂ (by rw [← hc₂, e, stepK_zero])
  have l₂ : c₂ ≤ T.length := by
    have := RR_mono (gens := gens) (T := T) (W := W) (KK := KK) (q := q + 1) (c := c₂) (by omega)
    omega
  have m₀ : c ≤ c₁ := by
    rw [← hc₁]
    exact stepK_mono (by rw [hc₁]; exact h₁)
  have m₁ : c₁ ≤ c₂ := by
    rw [← hc₂]
    exact stepK_mono (by rw [hc₂]; exact h₂)
  have hm₁ := inner_step (KK := KK) hs (i := 0) (by decide) hq hbc hqd hm
    (by rw [hc₁]; exact h₁) (by rw [hc₁]; omega)
  rw [hc₁] at hm₁
  have hm₂ := inner_step (KK := KK) hs (i := 1) (by decide) (Nat.lt_of_lt_of_le hq m₀)
    (Nat.le_trans hbc m₀) hqd hm₁ (by rw [hc₂]; exact h₂) (by rw [hc₂]; exact l₂)
  rw [hc₂] at hm₂
  refine ⟨c₂, Nat.le_trans m₀ m₁, ?_, hr⟩
  have hsz : gens.toArray.size = 2 := by simp [hs.g2]
  unfold pairF
  rw [hsz]
  exact hm₂

private theorem layer (hs : Setup gens T W) {b d : Nat} (hN : 0 < T.length) :
    ∀ n q c (st : Std.HashSet Tab × Array (Tab × List Nat)), q + n = b → b ≤ c →
      (∀ j, q ≤ j → j < b → (W.getD j []).length = d) → BfsMatch gens T W b c d st →
      RR gens T W KK q c = T.length →
      ∃ c', b ≤ c' ∧
        BfsMatch gens T W b c' d ((List.range' q n).foldl
          (fun st j => pairF gens.toArray st (T.getD j [], W.getD j [])) st) ∧
        RR gens T W KK b c' = T.length := by
  intro n
  induction n with
  | zero =>
    intro q c st hq hbc _ hm hr
    rw [Nat.add_zero] at hq
    subst hq
    exact ⟨c, hbc, hm, hr⟩
  | succ n ih =>
    intro q c st hq hbc hd hm hr
    obtain ⟨c', hcc, hm', hr'⟩ := pair_step (KK := KK) hs (q := q) (by omega) hbc
      (hd q (Nat.le_refl q) (by omega)) hm hr hN
    rw [List.range'_succ, List.foldl_cons]
    exact ih (q + 1) c' _ (by omega) (Nat.le_trans hbc hcc)
      (fun j h1 h2 => hd j (by omega) h2) hm' hr'

private theorem empty_end (hs : Setup gens T W) (hN : 0 < T.length) {b : Nat}
    (hr : RR gens T W KK b b = T.length) : b = T.length := by
  have hbN : b ≤ T.length := by
    have := RR_mono (gens := gens) (T := T) (W := W) (KK := KK) (q := b) (c := b) (by omega)
    omega
  rcases Nat.lt_or_ge b T.length with h | h
  · have h0 : stepK (packTs T) (packW W) (gens.getD 0 idTab) (T.getD b []) 0
        (encW (W.getD b [])) (kAt KK b 0) b b = 0 := by
      rw [stepK_eq, if_neg (fun h' => Nat.lt_irrefl b h'.1)]
    rw [RR_succ hs h, h0, stepK_zero, RR_zero] at hr
    omega
  · omega

private theorem range'_words {b c : Nat} (h1 : 1 ≤ b) (hbc : b ≤ c) (f : Nat → List Nat) :
    (List.range' 1 (b - 1)).map f ++ (List.range' b (c - b)).map f =
      (List.range' 1 (c - 1)).map f := by
  rw [← List.map_append]
  have h := List.range'_append (s := 1) (m := b - 1) (n := c - b) (step := 1)
  have e1 : 1 + 1 * (b - 1) = b := by omega
  have e2 : b - 1 + (c - b) = c - 1 := by omega
  rw [e1, e2] at h
  rw [h]

private theorem aux (hs : Setup gens T W) (hN : 0 < T.length) :
    ∀ fuel a b d (seen : Std.HashSet Tab) (F : Array (Tab × List Nat))
      (acc : Array (List Nat)), d + fuel = 200 → a ≤ b → 1 ≤ b →
      (∀ y, seen.contains y = true ↔ ∃ j < b, T.getD j [] = y) →
      F.toList = (List.range' a (b - a)).map (fun j => (T.getD j [], W.getD j [])) →
      (∀ j, a ≤ j → j < b → (W.getD j []).length = d) →
      (∀ j < b, wordTab gens (W.getD j []) = T.getD j []) →
      acc.toList = (List.range' 1 (b - 1)).map (fun j => W.getD j []) →
      RR gens T W KK a b = T.length →
      (bfsAux gens.toArray fuel seen F acc).toList =
          (List.range' 1 (T.length - 1)).map (fun j => W.getD j []) ∧
        ∀ j < T.length, wordTab gens (W.getD j []) = T.getD j [] := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b d seen F acc hd hab h1 _ _ hlen hwt hacc hr
    have hbN : b ≤ T.length := by
      have := RR_mono (gens := gens) (T := T) (W := W) (KK := KK) (q := a) (c := b) (by omega)
      omega
    obtain rfl : a = b := by
      rcases Nat.lt_or_ge a b with h | h
      · have := hlen a (Nat.le_refl a) h
        have hW := (hs.wb _ (getD_mem (l := W) (d := []) (i := a) (by rw [hs.wl]; omega))).1
        omega
      · omega
    have hb := empty_end hs hN hr
    rw [bfsAux, ← hb]
    exact ⟨hacc, hwt⟩
  | succ fuel ih =>
    intro a b d seen F acc hd hab h1 hseen hF hlen hwt hacc hr
    rw [bfsAux]
    by_cases he : F.isEmpty = true
    · rw [if_pos he]
      have hF0 : F.toList = [] := by
        rw [Array.isEmpty_iff] at he
        rw [he]
      rw [hF0] at hF
      have hab' : a = b := by
        have := congrArg List.length hF
        simp only [List.length_nil, List.length_map, List.length_range'] at this
        omega
      subst hab'
      have hb := empty_end hs hN hr
      rw [← hb]
      exact ⟨hacc, hwt⟩
    · rw [if_neg he]
      have hm0 : BfsMatch gens T W b b d (seen, #[]) :=
        ⟨hseen, by simp, fun j h1 h2 => absurd h2 (by omega), hwt⟩
      obtain ⟨c', hbc', hm', hr'⟩ := layer (KK := KK) hs hN (b - a) a b (seen, #[]) (by omega)
        (Nat.le_refl b) hlen hm0 hr
      have hfold : bfsLayer gens.toArray seen F = (List.range' a (b - a)).foldl
          (fun st j => pairF gens.toArray st (T.getD j [], W.getD j [])) (seen, #[]) := by
        rw [bfsLayer_eq, hF, List.foldl_map]
      rw [hfold]
      generalize (List.range' a (b - a)).foldl
          (fun st j => pairF gens.toArray st (T.getD j [], W.getD j [])) (seen, #[]) = st at hm' ⊢
      obtain ⟨s', n'⟩ := st
      refine ih b c' (d + 1) s' n' (acc ++ n'.map (·.2)) (by omega) hbc' (by omega) hm'.seen
        hm'.next hm'.len hm'.wt ?_ hr'
      rw [Array.toList_append, Array.toList_map, hacc, hm'.next, List.map_map]
      exact range'_words h1 hbc' _

private theorem eq_range' {α : Type} (l : List α) (d : α) :
    (List.range' 0 l.length).map (fun j => l.getD j d) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul]
    exact getD_of_lt h2

end Bfs

theorem bfsWords_eq_of_replay {gens T W : List Tab} {KK : List (List Nat)}
    (hg : gens.length = 2) (hgv : ∀ g ∈ gens, ValidT g) (hv : ∀ t ∈ T, ValidT t)
    (hnd : T.Nodup) (hT0 : T.getD 0 [] = idTab) (hW0 : W.getD 0 [] = [])
    (hWl : W.length = T.length) (hW : ∀ w ∈ W, w.length < 17 ∧ ∀ i ∈ w, i < 2)
    (hr : replayK (packTs T) (packW W) (gens.getD 0 idTab) (gens.getD 1 idTab) T (W.map encW) KK
      0 1 = T.length) :
    bfsWords gens = W ∧ W.map (wordTab gens) = T := by
  have hs : Setup gens T W := ⟨hg, hgv, hv, hnd, hWl, hW⟩
  have hr' : RR gens T W KK 0 1 = T.length := by
    unfold RR
    simpa only [List.drop_zero] using hr
  have hN : 0 < T.length := by
    rcases Nat.eq_zero_or_pos T.length with h | h
    · rw [h, List.length_eq_zero_iff.1 h] at hr
      exact absurd hr Nat.one_ne_zero
    · exact h
  have hseen : ∀ y, ((∅ : Std.HashSet Tab).insert idTab).contains y = true ↔
      ∃ j < 1, T.getD j [] = y := fun y => by
    rw [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false, beq_iff_eq]
    constructor
    · intro e
      exact ⟨0, Nat.one_pos, hT0.trans e⟩
    · rintro ⟨j, hj, e⟩
      obtain rfl : j = 0 := by omega
      exact hT0.symm.trans e
  obtain ⟨hacc, hwt⟩ := aux (KK := KK) hs hN 200 0 1 0 _ #[(idTab, [])] #[] rfl (Nat.zero_le 1)
    (Nat.le_refl 1) hseen
    (by
      change [(idTab, [])] = [(T.getD 0 [], W.getD 0 [])]
      rw [hT0, hW0])
    (fun j _ h2 => by
      obtain rfl : j = 0 := by omega
      rw [hW0]
      rfl)
    (fun j hj => by
      obtain rfl : j = 0 := by omega
      rw [hW0, hT0]
      rfl)
    rfl hr'
  constructor
  · unfold bfsWords
    rw [hacc]
    conv => rhs; rw [← eq_range' W []]
    rw [hWl]
    obtain ⟨n, hn⟩ : ∃ n, T.length = n + 1 := ⟨T.length - 1, by omega⟩
    rw [hn, List.range'_succ, List.map_cons, hW0, Nat.add_sub_cancel, Nat.zero_add]
  · apply List.ext_getElem
    · rw [List.length_map, hWl]
    · intro j h1 h2
      have hj : j < W.length := by simpa using h1
      rw [List.getElem_map, ← getD_of_lt (d := []) hj, hwt j h2, getD_of_lt h2]

theorem mul_mem_of_replay {gens T W : List Tab} {KK : List (List Nat)}
    (hg : gens.length = 2) (hgv : ∀ g ∈ gens, ValidT g) (hv : ∀ t ∈ T, ValidT t)
    (hnd : T.Nodup) (hWl : W.length = T.length) (hW : ∀ w ∈ W, w.length < 17 ∧ ∀ i ∈ w, i < 2)
    (hr : replayK (packTs T) (packW W) (gens.getD 0 idTab) (gens.getD 1 idTab) T (W.map encW) KK
      0 1 = T.length) :
    ∀ t ∈ T, ∀ i < 2, tmul (gens.getD i idTab) t ∈ T := by
  have hs : Setup gens T W := ⟨hg, hgv, hv, hnd, hWl, hW⟩
  have hr' : RR gens T W KK 0 1 = T.length := by
    unfold RR
    simpa only [List.drop_zero] using hr
  intro t ht i hi
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
  rw [← getD_of_lt (d := []) hj]
  exact closed_aux (KK := KK) hs T.length 0 1 (Nat.zero_add _) hr' j (Nat.zero_le j) hj i hi

end CFSG.KC.M22Out
