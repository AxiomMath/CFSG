module

public import Certificates.Data.Kernel.Spor.ImgEnum
public import CFSG.Certificates.Kernel.Spor.ONLin
public import CFSG.Certificates.Kernel.Spor.BfsReplay
public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.IE

open CFSG.KC.Enum CFSG.KS CFSG.KS.ONLin CFSG.KS.BfsReplay CFSG.PSL3Four.Native

@[expose] def eltF (G : Nat → Nat → Nat) (PAR LAB : Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, _, x => x
  | f + 1, k, x => if k = 0 then x else G (LAB k) (eltF G PAR LAB f (PAR k) x)

@[expose] def elt (G : Nat → Nat → Nat) (PAR LAB : Nat → Nat) (k : Nat) : Nat → Nat :=
  eltF G PAR LAB k k

theorem bIf_eq (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem lexB_iff (a b c d : Nat) : lexB a b c d = true ↔ LexLt a b c d := by
  unfold lexB LexLt
  rw [bIf_eq]
  by_cases h : a < c
  · simp [h]
  · have hb : Nat.blt a c = false := Bool.eq_false_iff.2 fun e => h (Nat.blt_eq.mp e)
    rw [hb, ite_eq_right (by simp), bAnd_iff, Nat.beq_eq, Nat.blt_eq]
    omega

section

variable {G : Nat → Nat → Nat} {P I PAR LAB POS : Nat → Nat} {ng cnt : Nat}

theorem ieAt_spec (h0 : ieAt G P I PAR LAB POS ng cnt 0 = true) {h : Nat}
    (hh : ieAt G P I PAR LAB POS ng cnt h = true) :
    (PAR 0 = 0 ∧ LAB 0 = 0 ∧ ∀ t < 154, imgAt I 0 t = P t) ∧
    (0 < h → PAR h < h ∧ LAB h < ng ∧ (∀ t < 154, G (LAB h) (imgAt I (PAR h) t) = imgAt I h t) ∧
      (h + 1 < cnt → LexLt (PAR h) (LAB h) (PAR (h + 1)) (LAB (h + 1)))) ∧
    ∀ j < ng, POS (h * ng + j) < cnt ∧
      (∀ t < 154, G j (imgAt I h t) = imgAt I (POS (h * ng + j)) t) ∧
      (POS (h * ng + j) = 0 ∨ ¬ LexLt h j (PAR (POS (h * ng + j))) (LAB (POS (h * ng + j)))) := by
  have e0 := h0
  unfold ieAt at e0
  rw [bAnd_iff, bIf_eq, ite_eq_left (by rfl)] at e0
  simp only [bAnd_iff, Nat.beq_eq] at e0
  obtain ⟨⟨a1, a2, a3⟩, -⟩ := e0
  refine ⟨⟨a1, a2, fun t ht => Nat.eq_of_beq_eq_true (allN_spec a3 t ht)⟩, fun hpos => ?_, ?_⟩
  · have e := hh
    unfold ieAt at e
    rw [bAnd_iff, bIf_eq, ite_eq_right (by simpa using Nat.pos_iff_ne_zero.1 hpos), strictB_eq,
      strictB_eq] at e
    simp only [bAnd_iff] at e
    obtain ⟨⟨b1, b2, b3, b4⟩, -⟩ := e
    refine ⟨Nat.blt_eq.mp b1, Nat.blt_eq.mp b2,
      fun t ht => Nat.eq_of_beq_eq_true (allN_spec b3 t ht), fun hc => ?_⟩
    rw [bIf_eq, ite_eq_left (Nat.blt_eq.mpr hc), lexB_iff] at b4
    exact b4
  · intro j hj
    have e := hh
    unfold ieAt at e
    rw [bAnd_iff] at e
    have c := allN_spec e.2 j hj
    rw [strictB_eq] at c
    simp only [bAnd_iff, Nat.add_eq, Nat.mul_eq] at c
    obtain ⟨c1, c2, c3⟩ := c
    refine ⟨Nat.blt_eq.mp c1, fun t ht => Nat.eq_of_beq_eq_true (allN_spec c2 t ht), ?_⟩
    rw [bIf_eq] at c3
    by_cases hq : POS (h * ng + j) = 0
    · exact Or.inl hq
    · rw [ite_eq_right (by simpa using hq)] at c3
      right
      rw [← lexB_iff]
      simpa using c3

theorem eltF_eq (hpar : ∀ k, 0 < k → k < cnt → PAR k < k) :
    ∀ k < cnt, ∀ f, k ≤ f → ∀ x, eltF G PAR LAB f k x = elt G PAR LAB k x := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk f hf x
    cases k with
    | zero =>
      cases f <;> rfl
    | succ k =>
      obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      have hp := hpar (k + 1) (by omega) hk
      unfold elt
      simp only [eltF, Nat.add_one_ne_zero, ↓reduceIte]
      rw [ih _ hp (by omega) f (by omega), ih _ hp (by omega) k (by omega)]

theorem elt_succ (hpar : ∀ k, 0 < k → k < cnt → PAR k < k) {k : Nat} (h0 : 0 < k) (hk : k < cnt)
    (x : Nat) : elt G PAR LAB k x = G (LAB k) (elt G PAR LAB (PAR k) x) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  conv_lhs => unfold elt
  simp only [eltF, Nat.add_one_ne_zero, ↓reduceIte]
  rw [eltF_eq hpar _ (by have := hpar (k + 1) h0 hk; omega) k
    (by have := hpar (k + 1) h0 hk; omega)]

theorem elt_zero (x : Nat) : elt G PAR LAB 0 x = x := rfl

end

theorem eltR_eq (G : Nat → Nat → Nat) (PAR LAB : Nat → Nat) :
    ∀ f k x, eltR G PAR LAB f k x = eltF G PAR LAB f k x
  | 0, _, _ => rfl
  | f + 1, k, x => by
    change nIf(Nat.beq k 0, x, G (LAB k) (eltR G PAR LAB f (PAR k) x)) = _
    rw [eltR_eq G PAR LAB f (PAR k) x]
    by_cases hk : k = 0
    · subst hk
      rfl
    · have hb : Nat.beq k 0 = false := Bool.eq_false_iff.2 fun e => hk (Nat.eq_of_beq_eq_true e)
      rw [hb]
      simp [eltF, hk]

theorem ieSl_spec {G : Nat → Nat → Nat} {P I PAR LAB POS : Nat → Nat} {ng cnt L q : Nat}
    (hq : cnt ≤ q * L) (h : ∀ s < q, ieSl G P I PAR LAB POS ng cnt (Nat.mul s L) L = true) :
    ∀ k < cnt, ieAt G P I PAR LAB POS ng cnt k = true := by
  intro k hk
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with e | e
    · subst e
      omega
    · exact e
  have hs := h (k / L) (by
    apply Nat.div_lt_of_lt_mul
    rw [Nat.mul_comm]
    omega)
  unfold ieSl at hs
  have hd := allN_spec hs (k % L) (Nat.mod_lt _ hL)
  rw [strictB_eq] at hd
  have e : Nat.add (Nat.mul (k / L) L) (k % L) = k := by
    simp only [Nat.add_eq, Nat.mul_eq]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod k L
  rw [e, bIf_eq, ite_eq_left (Nat.blt_eq.mpr hk)] at hd
  exact hd

theorem fpF_congr {f g : Nat → Nat} : ∀ {m : Nat}, (∀ t < m, f t = g t) → fpF f m = fpF g m
  | 0, _ => rfl
  | m + 1, h => by
    change Nat.add (Nat.mul (fpF f m) 262144) (f m) = Nat.add (Nat.mul (fpF g m) 262144) (g m)
    rw [fpF_congr fun t ht => h t (by omega), h m (by omega)]

theorem fpK_congr {I : Nat → Nat} {m : Nat} (hm : m ≤ 154) {a b : Nat}
    (h : ∀ t < 154, imgAt I a t = imgAt I b t) : fpK I m a = fpK I m b :=
  fpF_congr fun t ht => h t (by omega)

theorem ie_elt {n : Nat} {key : Nat → Nat} {G : Nat → Nat → Nat} {P I PAR LAB POS : Nat → Nat}
    {ng cnt : Nat} (hG : ∀ j < ng, Lin n key (G j)) (hc : 0 < cnt)
    (hpt : ∀ h < cnt, ieAt G P I PAR LAB POS ng cnt h = true) :
    ∀ k < cnt, Lin n key (elt G PAR LAB k) ∧ ∀ t < 154, elt G PAR LAB k (P t) = imgAt I k t := by
  have h0 := hpt 0 hc
  have hs := fun h (hh : h < cnt) => ieAt_spec h0 (hpt h hh)
  have hpar : ∀ k, 0 < k → k < cnt → PAR k < k := fun k h1 h2 => ((hs k h2).2.1 h1).1
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hk0 : k = 0
    · subst hk0
      exact ⟨Lin.id, fun t ht => ((hs 0 hc).1.2.2 t ht).symm⟩
    · obtain ⟨b1, b2, b3, -⟩ := (hs k hk).2.1 (by omega)
      obtain ⟨l1, l2⟩ := ih (PAR k) b1 (by omega)
      refine ⟨(Lin.comp (hG _ b2) l1).congr fun i _ => (elt_succ hpar (by omega) hk i).symm,
        fun t ht => ?_⟩
      rw [elt_succ hpar (by omega) hk, l2 t ht, b3 t ht]

theorem ie_replay {n : Nat} {key : Nat → Nat} {G : Nat → Nat → Nat} {P I PAR LAB POS FP : Nat → Nat}
    {ng cnt : Nat} {gens : Array Tab} (hO : Orbit n key) (hS : Spans n key P)
    (hG : ∀ j < ng, Lin n key (G j)) (hgs : gens.size = ng)
    (hgen : ∀ j < ng, ∀ x < n, (gens[j]!)[x]! = G j x) (hc : 0 < cnt)
    (hpt : ∀ h < cnt, ieAt G P I PAR LAB POS ng cnt h = true) (hd : distK FP cnt = true)
    (hFP : ∀ a < cnt, ∀ b < cnt, (∀ t < 154, imgAt I a t = imgAt I b t) → FP a = FP b) :
    Replay (leftStep n gens) gens.size (idTab n) cnt
      (fun k => Array.ofFn (n := n) fun i => elt G PAR LAB k i.val) PAR LAB
      (fun h j => POS (h * ng + j)) := by
  have h0 := hpt 0 hc
  have hs := fun h (hh : h < cnt) => ieAt_spec h0 (hpt h hh)
  have hpar : ∀ k, 0 < k → k < cnt → PAR k < k := fun k h1 h2 => ((hs k h2).2.1 h1).1
  have hE := ie_elt hG hc hpt
  have hlt : ∀ k < cnt, ∀ x < n, elt G PAR LAB k x < n := fun k hk x hx => by
    obtain ⟨M, hM⟩ := (hE k hk).1
    exact (hM x hx).1
  have get : ∀ (f : Nat → Nat) {x : Nat}, x < n →
      (Array.ofFn (n := n) fun i => f i.val)[x]! = f x := fun f x hx => by
    rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]
  have ext : ∀ (f g : Nat → Nat), (∀ x < n, f x = g x) →
      (Array.ofFn (n := n) fun i => f i.val) = Array.ofFn (n := n) fun i => g i.val := fun f g h => by
    apply Array.ext
    · simp
    · intro i h1 h2
      simp only [Array.getElem_ofFn]
      exact h i (by simpa using h1)
  have hstep : ∀ h < cnt, ∀ j < ng, leftStep n gens j (Array.ofFn (n := n) fun i => elt G PAR LAB h i.val) =
      Array.ofFn (n := n) fun i => G j (elt G PAR LAB h i.val) := fun h hh j hj => by
    unfold leftStep comp
    refine ext (fun x => (gens[j]!)[(Array.ofFn (n := n) fun i => elt G PAR LAB h i.val)[x]!]!)
      (fun x => G j (elt G PAR LAB h x)) fun x hx => ?_
    rw [get _ hx, hgen j hj _ (hlt h hh x hx)]
  refine ⟨hc, ext _ _ fun x _ => rfl, (hs 0 hc).1.1, (hs 0 hc).1.2.1, fun a ha b hb e => ?_,
    fun i h1 h2 => ?_, fun i h1 h2 => ((hs i (by omega)).2.1 h1).2.2.2 h2, fun h hh j hj => ?_⟩
  · have hab : ∀ t < 154, imgAt I a t = imgAt I b t := fun t ht => by
      rw [← (hE a ha).2 t ht, ← (hE b hb).2 t ht, ← get (elt G PAR LAB a) (hS.1 t ht),
        ← get (elt G PAR LAB b) (hS.1 t ht), e]
    have hf := hFP a ha b hb hab
    rcases Nat.lt_trichotomy a b with h | h | h
    · have := allN_spec (allN_spec hd b hb) a h
      simp [hf] at this
    · exact h
    · have := allN_spec (allN_spec hd a ha) b h
      simp [hf] at this
  · obtain ⟨b1, b2, -, -⟩ := (hs i h2).2.1 h1
    refine ⟨b1, by rw [hgs]; exact b2, ?_⟩
    rw [hstep _ (by omega) _ b2]
    exact ext _ _ fun x _ => elt_succ hpar h1 h2 x
  · rw [hgs] at hj
    obtain ⟨c1, c2, c3⟩ := (hs h hh).2.2 j hj
    refine ⟨c1, ?_, c3⟩
    rw [hstep h hh j hj]
    refine ext _ _ (Lin.eq_of_span hO hS (Lin.comp (hG j hj) (hE h hh).1) (hE _ c1).1 fun t ht => ?_)
    rw [(hE h hh).2 t ht, (hE _ c1).2 t ht]
    exact c2 t ht

theorem ie_enumBFS {n : Nat} {key : Nat → Nat} {G : Nat → Nat → Nat}
    {P I PAR LAB POS FP : Nat → Nat} {ng cnt cap : Nat} {gens : Array Tab} (hO : Orbit n key)
    (hS : Spans n key P) (hG : ∀ j < ng, Lin n key (G j)) (hgs : gens.size = ng)
    (hgen : ∀ j < ng, ∀ x < n, (gens[j]!)[x]! = G j x) (hc : 0 < cnt)
    (hpt : ∀ h < cnt, ieAt G P I PAR LAB POS ng cnt h = true) (hd : distK FP cnt = true)
    (hFP : ∀ a < cnt, ∀ b < cnt, (∀ t < 154, imgAt I a t = imgAt I b t) → FP a = FP b)
    (hcap : cnt ≤ cap) :
    let E : Enum := ⟨Array.ofFn (n := cnt) fun k => Array.ofFn (n := n) fun i =>
        elt G PAR LAB k.val i.val, Array.ofFn (n := cnt) fun i => PAR i.val,
        Array.ofFn (n := cnt) fun i => LAB i.val⟩
    enumBFS n gens cap = E ∧ enumOK n gens E = true :=
  enumBFS_replay (ie_replay hO hS hG hgs hgen hc hpt hd hFP) hcap

end CFSG.KS.IE

end
