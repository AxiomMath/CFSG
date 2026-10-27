module

public import Certificates.Data.Kernel.Fi23Nt.TabDefs
public import CFSG.Certificates.Kernel.E27Lie.Sound

public section

namespace CFSG.KS.Fi23Nt

open CFSG.KC.Enum CFSG.KC.Fi23Nt CFSG.KS.E27Lie CFSG.HardMathSupport.Foote.E27 Subgroup

noncomputable abbrev ppK (PAR i : ℕ) : ℕ := Nat.shiftRight (lnK 16 PAR i) 2

noncomputable abbrev pjK (PAR i : ℕ) : ℕ := Nat.land (lnK 16 PAR i) 3

noncomputable abbrev parT (n PAR : ℕ) : Array (ℕ × ℕ) := parOf n (ppK PAR) (pjK PAR)

noncomputable abbrev ltT (n : ℕ) (LT : List ℕ) : Array (Array ℕ) := ltOf 3 n (ltK LT)

theorem sN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem beq_true {a b : ℕ} (h : a = b) : Nat.beq a b = true := Eq.mpr Nat.beq_eq h

theorem nRec_eq (c : Bool) (t e : ℕ) :
    Bool.rec (motive := fun _ => ℕ) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem allN3_intro {f : ℕ → Bool} (h : ∀ i < 3, f i = true) : allN 3 f = true := by
  have e : allN 3 f = Bool.rec (motive := fun _ => Bool) false true
      (Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false true (f 0)) (f 1)) (f 2)) := rfl
  rw [e, h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num)]

theorem appK_eq (u v : List ℕ) : appK u v = u ++ v := by
  induction u with
  | nil => rfl
  | cons x u ih =>
    change x :: appK u v = _
    rw [ih, List.cons_append]

theorem rinvK_prod {M : Type*} [Group M] (e : ℕ → M) :
    ∀ w : List ℕ, (∀ r ∈ w, e (Nat.xor r 1) = (e r)⁻¹) →
      ((rinvK w).map e).prod = ((w.map e).prod)⁻¹
  | [], _ => by simp [rinvK]
  | x :: w, h => by
    change ((appK (rinvK w) [Nat.xor x 1]).map e).prod = _
    rw [appK_eq, List.map_append, List.prod_append,
      rinvK_prod e w fun r hr => h r (List.mem_cons_of_mem x hr)]
    have hx : e (x ^^^ 1) = (e x)⁻¹ := h x List.mem_cons_self
    simp [hx]

theorem eqLK_eq : ∀ u v : List ℕ, eqLK u v = true → u = v
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by simp [eqLK])
  | _ :: _, [], h => absurd h (by simp [eqLK])
  | x :: u, y :: v, h => by
    change Bool.rec (motive := fun _ => Bool) false (eqLK u v) (Nat.beq x y) = true at h
    obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    rw [beq_of h1, eqLK_eq u v h2]

variable {G : Type*} [Group G] {g : ℕ → G} {PAR n : ℕ} {LT : List ℕ}

theorem par_eq {i : ℕ} (hi : i < n) : (parT n PAR)[i]! = (ppK PAR i, pjK PAR i) :=
  ofFnG (fun i => (ppK PAR i, pjK PAR i)) hi

theorem lt_eq {j i : ℕ} (hj : j < 3) (hi : i < n) : ((ltT n LT)[j]!)[i]! = ltK LT j i := by
  rw [ofFnG (fun j => Array.ofFn (n := n) fun i => ltK LT j i.val) hj,
    ofFnG (fun i => ltK LT j i) hi]

theorem tree_of (hT : TabData g (parT n PAR) (ltT n LT) n 3) {i : ℕ} (h0 : i ≠ 0) (hi : i < n) :
    ppK PAR i < i ∧ pjK PAR i < 3 ∧
      tabElt g (parT n PAR) i = g (pjK PAR i) * tabElt g (parT n PAR) (ppK PAR i) := by
  obtain ⟨hp0, hj0⟩ := hT.par_lt i (Nat.pos_of_ne_zero h0) hi
  rw [par_eq hi] at hp0 hj0
  refine ⟨hp0, hj0, ?_⟩
  have hpi : ((parT n PAR)[i]!).1 < i := by rw [par_eq hi]; exact hp0
  rw [tabElt_succ g _ hpi, par_eq hi]

theorem gen_eq (hT : TabData g (parT n PAR) (ltT n LT) n 3) (hn : 0 < n) {j : ℕ} (hj : j < 3) :
    ltK LT j 0 < n ∧ g j = tabElt g (parT n PAR) (ltK LT j 0) := by
  obtain ⟨h1, h2⟩ := hT.left j hj 0 hn
  rw [lt_eq hj hn, tabElt_zero, mul_one] at *
  exact ⟨h1, h2⟩

theorem tmK_zero (f b : ℕ) : tmK PAR LT f 0 b = b := by
  cases f <;> rfl

theorem tmK_succ_ne {f a : ℕ} (b : ℕ) (h : a ≠ 0) :
    tmK PAR LT (f + 1) a b = ltK LT (pjK PAR a) (tmK PAR LT f (ppK PAR a) b) := by
  change Bool.rec (motive := fun _ => ℕ) (strictN (lnK 16 PAR a) fun q =>
    strictN (tmK PAR LT f (Nat.shiftRight q 2) b) (ltK LT (Nat.land q 3))) b (Nat.beq a 0) = _
  rw [nRec_eq, if_neg (by rw [Nat.beq_eq]; exact h), sN_eq, sN_eq]

theorem tmK_spec (hT : TabData g (parT n PAR) (ltT n LT) n 3) :
    ∀ f a b, a ≤ f → a < n → b < n → tmK PAR LT f a b < n ∧
      tabElt g (parT n PAR) a * tabElt g (parT n PAR) b =
        tabElt g (parT n PAR) (tmK PAR LT f a b) := by
  intro f
  induction f with
  | zero =>
    intro a b ha _ hb
    obtain rfl : a = 0 := by omega
    rw [tmK_zero, tabElt_zero, one_mul]
    exact ⟨hb, rfl⟩
  | succ f ih =>
    intro a b ha han hb
    by_cases h0 : a = 0
    · subst h0
      rw [tmK_zero, tabElt_zero, one_mul]
      exact ⟨hb, rfl⟩
    · obtain ⟨hp, hj, hE⟩ := tree_of hT h0 han
      obtain ⟨h1, h2⟩ := ih (ppK PAR a) b (by omega) (by omega) hb
      obtain ⟨h3, h4⟩ := hT.left (pjK PAR a) hj _ h1
      rw [lt_eq hj h1] at h3 h4
      rw [tmK_succ_ne b h0, hE, mul_assoc, h2]
      exact ⟨h3, h4⟩

theorem tm_spec (hT : TabData g (parT n PAR) (ltT n LT) n 3) {a b : ℕ} (ha : a < n) (hb : b < n) :
    tmK PAR LT n a b < n ∧ tabElt g (parT n PAR) a * tabElt g (parT n PAR) b =
      tabElt g (parT n PAR) (tmK PAR LT n a b) :=
  tmK_spec hT n a b ha.le ha hb

theorem testBit_foldMsk (A x : ℕ) : ∀ (len s : ℕ),
    (foldBlk 0 (fun k s => Nat.lor s (Nat.shiftLeft 1 (aK A k))) len s).testBit x = true ↔
      s.testBit x = true ∨ ∃ k < len, aK A k = x
  | 0, s => by simp [foldBlk]
  | len + 1, s => by
    change (strictN (Nat.lor s (Nat.shiftLeft 1 (aK A (Nat.add 0 len))))
      (foldBlk 0 (fun k s => Nat.lor s (Nat.shiftLeft 1 (aK A k))) len)).testBit x = true ↔ _
    rw [sN_eq, testBit_foldMsk A x len]
    change (s ||| 1 <<< aK A (0 + len)).testBit x = true ∨ _ ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow,
      decide_eq_true_eq, Nat.zero_add]
    constructor
    · rintro ((h | h) | ⟨k, hk, e⟩)
      · exact Or.inl h
      · exact Or.inr ⟨len, by omega, h⟩
      · exact Or.inr ⟨k, by omega, e⟩
    · rintro (h | ⟨k, hk, e⟩)
      · exact Or.inl (Or.inl h)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
        · exact Or.inr ⟨k, hk, e⟩
        · exact Or.inl (Or.inr e)

theorem bitK_iff (M x : ℕ) : bitK M x = true ↔ M.testBit x = true := by
  change Nat.beq ((M >>> x) &&& 1) 1 = true ↔ _
  rw [Nat.beq_eq, Nat.testBit, Nat.and_comm]
  rcases Nat.mod_two_eq_zero_or_one (M >>> x) with h | h <;>
    simp [Nat.one_and_eq_mod_two, h]

theorem bitK_msk (A x : ℕ) : bitK (mskK A) x = true ↔ ∃ k < 81, aK A k = x := by
  rw [bitK_iff]
  change (foldBlk 0 (fun k s => Nat.lor s (Nat.shiftLeft 1 (aK A k))) 81 0).testBit x = true ↔ _
  rw [testBit_foldMsk]
  simp

theorem subHK_spec {A : ℕ} (h : subHK n A = true) :
    aK A 0 = 0 ∧ (∀ k < 81, aK A k < n) ∧ ∀ k l, k < l → l < 81 → aK A k < aK A l := by
  unfold subHK at h
  obtain ⟨h1, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  have hs : ∀ i < 80, Nat.blt (aK A i) (aK A (Nat.succ i)) = true := CFSG.KS.allN_spec h3
  have hmono : ∀ k l, k < l → l < 81 → aK A k < aK A l := by
    intro k l hkl hl
    induction l with
    | zero => omega
    | succ l ih =>
      have := blt_of (hs l (by omega))
      rcases Nat.lt_succ_iff_lt_or_eq.1 hkl with h' | rfl
      · exact (ih h' (by omega)).trans this
      · exact this
  refine ⟨beq_of h1, fun k hk => ?_, hmono⟩
  rcases Nat.lt_or_ge k 80 with hk' | hk'
  · exact (hmono k 80 hk' (by norm_num)).trans (blt_of h2)
  · obtain rfl : k = 80 := by omega
    exact blt_of h2

theorem subIK_spec {A M k : ℕ} (h : subIK n PAR LT A M k = true) :
    tmK PAR LT n (aK A k) (tmK PAR LT n (aK A k) (aK A k)) = 0 ∧ ∀ l < 81,
      bitK M (tmK PAR LT n (aK A k) (aK A l)) = true ∧
        tmK PAR LT n (aK A k) (aK A l) = tmK PAR LT n (aK A l) (aK A k) := by
  unfold subIK at h
  rw [sB_eq] at h
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  refine ⟨beq_of h1, fun l hl => ?_⟩
  have h3 := CFSG.KS.allN_spec h2 l hl
  rw [sB_eq, sB_eq] at h3
  obtain ⟨h4, h5⟩ := (CFSG.KS.bAnd_iff _ _).1 h3
  exact ⟨h4, beq_of h5⟩

theorem sub_group (hT : TabData g (parT n PAR) (ltT n LT) n 3) {A : ℕ} (hh : subHK n A = true)
    (hs : ∀ k < 81, subIK n PAR LT A (mskK A) k = true) :
    ∃ A₀ : Subgroup G, (∀ x, x ∈ A₀ ↔ ∃ k < 81, tabElt g (parT n PAR) (aK A k) = x) ∧
      Nat.card A₀ = 81 ∧ (∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a) ∧ ∀ a ∈ A₀, a ^ 3 = 1 := by
  obtain ⟨h0, hlt, hmono⟩ := subHK_spec hh
  set E := tabElt g (parT n PAR)
  have hmul : ∀ k < 81, ∀ l < 81, ∃ k' < 81, E (aK A k) * E (aK A l) = E (aK A k') := by
    intro k hk l hl
    obtain ⟨-, hm⟩ := subIK_spec (hs k hk)
    obtain ⟨k', hk', e⟩ := (bitK_msk A _).1 (hm l hl).1
    exact ⟨k', hk', by rw [(tm_spec hT (hlt k hk) (hlt l hl)).2, e]⟩
  have hcube : ∀ k < 81, E (aK A k) ^ 3 = 1 := by
    intro k hk
    have hc := (subIK_spec (hs k hk)).1
    obtain ⟨h1, h2⟩ := tm_spec hT (hlt k hk) (hlt k hk)
    rw [pow_three, h2, (tm_spec hT (hlt k hk) h1).2, hc]
    exact tabElt_zero g _
  let X : Set G := {x | ∃ k < 81, E (aK A k) = x}
  have hmulX : ∀ x ∈ X, ∀ y ∈ X, x * y ∈ X := by
    rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
    obtain ⟨k', hk', e⟩ := hmul k hk l hl
    exact ⟨k', hk', e.symm⟩
  let S : Subgroup G :=
    { carrier := X
      mul_mem' := fun {x y} hx hy => hmulX x hx y hy
      one_mem' := ⟨0, by norm_num, by rw [h0]; exact tabElt_zero g _⟩
      inv_mem' := fun {x} hx => by
        obtain ⟨k, hk, rfl⟩ := hx
        have e : (E (aK A k))⁻¹ = E (aK A k) * E (aK A k) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_three, hcube k hk]
        rw [e]
        exact hmulX _ ⟨k, hk, rfl⟩ _ ⟨k, hk, rfl⟩ }
  refine ⟨S, fun x => Iff.rfl, ?_, ?_, ?_⟩
  · have hbij : Function.Bijective fun k : Fin 81 => (⟨E (aK A k), k, k.isLt, rfl⟩ : S) := by
      constructor
      · intro k l e
        have e' := hT.inj _ (hlt k k.isLt) _ (hlt l l.isLt) (congrArg Subtype.val e)
        apply Fin.ext
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with h' | h'
        · exact absurd e' (hmono k l h' l.isLt).ne
        · exact absurd e' (hmono l k h' k.isLt).ne'
      · rintro ⟨x, k, hk, rfl⟩
        exact ⟨⟨k, hk⟩, rfl⟩
    rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fin]
  · rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
    obtain ⟨-, hm⟩ := subIK_spec (hs k hk)
    rw [(tm_spec hT (hlt k hk) (hlt l hl)).2, (tm_spec hT (hlt l hl) (hlt k hk)).2,
      (hm l hl).2]
  · rintro _ ⟨k, hk, rfl⟩
    exact hcube k hk

theorem foldCnt (c : ℕ → Bool) : ∀ len s : ℕ,
    foldBlk 0 (fun l s => nIf(c l, Nat.succ s, s)) len s =
      s + ((Finset.range len).filter fun l => c l = true).card
  | 0, s => by simp [foldBlk]
  | len + 1, s => by
    change strictN (nIf(c (Nat.add 0 len), Nat.succ s, s))
      (foldBlk 0 (fun l s => nIf(c l, Nat.succ s, s)) len) = _
    have e0 : Nat.add 0 len = len := Nat.zero_add len
    rw [sN_eq, foldCnt c len, Finset.range_add_one, Finset.filter_insert, e0, nRec_eq]
    by_cases hc : c len = true
    · rw [if_pos hc, if_pos hc, Finset.card_insert_of_notMem (by simp)]
      omega
    · rw [if_neg hc, if_neg hc]

theorem card_filter_eq (hT : TabData g (parT n PAR) (ltT n LT) n 3) {A : ℕ}
    (hh : subHK n A = true) {A₀ : Subgroup G}
    (hA : ∀ x, x ∈ A₀ ↔ ∃ k < 81, tabElt g (parT n PAR) (aK A k) = x) (P : Subgroup G)
    (c : ℕ → Bool) (hc : ∀ l < 81, c l = true ↔ tabElt g (parT n PAR) (aK A l) ∈ P) :
    Nat.card ↥(A₀ ⊓ P) = ((Finset.range 81).filter fun l => c l = true).card := by
  obtain ⟨-, hlt, hmono⟩ := subHK_spec hh
  set s := (Finset.range 81).filter fun l => c l = true
  have hmem : ∀ l : s, tabElt g (parT n PAR) (aK A l.1) ∈ A₀ ⊓ P := by
    intro l
    have hl := Finset.mem_filter.1 l.2
    exact ⟨(hA _).2 ⟨l.1, Finset.mem_range.1 hl.1, rfl⟩,
      (hc l.1 (Finset.mem_range.1 hl.1)).1 hl.2⟩
  have hbij : Function.Bijective fun l : s => (⟨_, hmem l⟩ : ↥(A₀ ⊓ P)) := by
    constructor
    · intro k l e
      have hk := Finset.mem_range.1 (Finset.mem_filter.1 k.2).1
      have hl := Finset.mem_range.1 (Finset.mem_filter.1 l.2).1
      have e' := hT.inj _ (hlt _ hk) _ (hlt _ hl) (congrArg Subtype.val e)
      apply Subtype.ext
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h' | h'
      · exact absurd e' (hmono _ _ h' hl).ne
      · exact absurd e' (hmono _ _ h' hk).ne'
    · rintro ⟨x, hxA, hxP⟩
      obtain ⟨l, hl, rfl⟩ := (hA x).1 hxA
      exact ⟨⟨l, Finset.mem_filter.2 ⟨Finset.mem_range.2 hl, (hc l hl).2 hxP⟩⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_coe]

theorem centCK_eq (A r : ℕ) : centCK n PAR LT A r = ((Finset.range 81).filter fun l =>
    Nat.beq (tmK PAR LT n r (aK A l)) (tmK PAR LT n (aK A l) r) = true).card := by
  unfold centCK
  have e : (fun l s => strictN (aK A l) fun b =>
      nIf(Nat.beq (tmK PAR LT n r b) (tmK PAR LT n b r), Nat.succ s, s)) =
      fun l s => nIf(Nat.beq (tmK PAR LT n r (aK A l)) (tmK PAR LT n (aK A l) r), Nat.succ s, s) := by
    funext l s
    rw [sN_eq]
  rw [e, foldCnt, Nat.zero_add]

theorem cent_card (hT : TabData g (parT n PAR) (ltT n LT) n 3) {A : ℕ}
    (hh : subHK n A = true) {A₀ : Subgroup G}
    (hA : ∀ x, x ∈ A₀ ↔ ∃ k < 81, tabElt g (parT n PAR) (aK A k) = x) {r bd : ℕ} (hr : r < n)
    (hc : centIK n PAR LT A bd r = true) :
    Nat.card ↥(A₀ ⊓ centralizer ({tabElt g (parT n PAR) r} : Set G)) < bd := by
  obtain ⟨-, hlt, -⟩ := subHK_spec hh
  rw [card_filter_eq hT hh hA _ (fun l => Nat.beq (tmK PAR LT n r (aK A l))
    (tmK PAR LT n (aK A l) r))]
  · rw [← centCK_eq]
    exact blt_of hc
  · intro l hl
    obtain ⟨m1, e1⟩ := tm_spec hT hr (hlt l hl)
    obtain ⟨m2, e2⟩ := tm_spec hT (hlt l hl) hr
    rw [mem_centralizer_singleton_iff, Nat.beq_eq, e1, e2]
    exact ⟨fun e => by rw [e], fun e => (hT.inj _ m2 _ m1 e).symm⟩

theorem cosIK_spec {A R nr D x : ℕ} (h : cosIK n PAR LT A R nr D x = true) :
    ∃ c ≤ nr, ∃ k < 81, repK R c < n ∧ tmK PAR LT n (repK R c) (aK A k) = x := by
  unfold cosIK at h
  rw [sB_eq, sB_eq, sB_eq] at h
  obtain ⟨h1, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  exact ⟨_, Nat.le_of_ble_eq_true h2, _, blt_of h1, blt_of h3, beq_of h4⟩

theorem cent_lt (hT : TabData g (parT n PAR) (ltT n LT) n 3) {A : ℕ}
    (hh : subHK n A = true) (hs : ∀ k < 81, subIK n PAR LT A (mskK A) k = true)
    {A₀ : Subgroup G} (hA : ∀ x, x ∈ A₀ ↔ ∃ k < 81, tabElt g (parT n PAR) (aK A k) = x)
    {R nr D bd : ℕ} (hc : ∀ x < n, cosIK n PAR LT A R nr D x = true)
    (hz : ∀ c < nr, centIK n PAR LT A bd (lnK 16 R c) = true) :
    ∀ x < n, tabElt g (parT n PAR) x ∉ A₀ →
      Nat.card ↥(A₀ ⊓ centralizer ({tabElt g (parT n PAR) x} : Set G)) < bd := by
  obtain ⟨-, hlt, -⟩ := subHK_spec hh
  obtain ⟨A₁, hA₁, -, hab, -⟩ := sub_group hT hh hs
  have hAA : A₀ = A₁ := by
    ext y
    rw [hA, hA₁]
  intro x hx hxA
  obtain ⟨c, hc', k, hk, hr, e⟩ := cosIK_spec (hc x hx)
  have hE := (tm_spec hT hr (hlt k hk)).2
  rw [e] at hE
  rcases c with _ | c
  · change tmK PAR LT n 0 (aK A k) = x at e
    rw [tmK_zero] at e
    exact absurd ((hA _).2 ⟨k, hk, by rw [e]⟩) hxA
  · have hmem : tabElt g (parT n PAR) (aK A k) ∈ A₀ := (hA _).2 ⟨k, hk, rfl⟩
    rw [← hE]
    have hcomm : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a := by
      rw [hAA]
      exact hab
    set t := tabElt g (parT n PAR) (repK R (c + 1))
    set a := tabElt g (parT n PAR) (aK A k)
    have e2 : A₀ ⊓ centralizer ({t * a} : Set G) = A₀ ⊓ centralizer ({t} : Set G) := by
      ext y
      simp only [Subgroup.mem_inf, mem_centralizer_singleton_iff, and_congr_right_iff]
      intro hy
      have hay := hcomm _ hmem y hy
      constructor
      · intro e
        refine mul_right_cancel (b := a) ?_
        rw [mul_assoc, e, mul_assoc, mul_assoc, hay]
      · intro e
        rw [← mul_assoc, e, mul_assoc, ← hay, mul_assoc]
    rw [e2]
    exact cent_card hT hh hA hr (hz c (by omega))

theorem z_lt (hT : TabData g (parT n PAR) (ltT n LT) n 3) (hn : 0 < n) {A : ℕ}
    (hh : subHK n A = true) {A₀ : Subgroup G}
    (hA : ∀ x, x ∈ A₀ ↔ ∃ k < 81, tabElt g (parT n PAR) (aK A k) = x) {bd : ℕ}
    (hz : zK n PAR LT A bd = true) :
    Nat.card ↥(A₀ ⊓ centralizer (Set.range fun j : Fin 3 => g j)) < bd := by
  obtain ⟨-, hlt, -⟩ := subHK_spec hh
  set c : ℕ → Bool := fun l => allN 3 fun j =>
    Nat.beq (ltK LT j (aK A l)) (tmK PAR LT n (aK A l) (ltK LT j 0))
  rw [card_filter_eq hT hh hA _ c]
  · have e : zCK n PAR LT A = ((Finset.range 81).filter fun l => c l = true).card := by
      unfold zCK
      have e : (fun l s => strictN (aK A l) fun b =>
          nIf(allN 3 (fun j => Nat.beq (ltK LT j b) (tmK PAR LT n b (ltK LT j 0))),
            Nat.succ s, s)) = fun l s => nIf(c l, Nat.succ s, s) := by
        funext l s
        rw [sN_eq]
      rw [e, foldCnt, Nat.zero_add]
    rw [← e]
    exact blt_of hz
  · intro l hl
    have key : ∀ j < 3, (Nat.beq (ltK LT j (aK A l)) (tmK PAR LT n (aK A l) (ltK LT j 0)) = true ↔
        g j * tabElt g (parT n PAR) (aK A l) = tabElt g (parT n PAR) (aK A l) * g j) := by
      intro j hj
      obtain ⟨hg0, hg⟩ := gen_eq hT hn hj
      obtain ⟨hL1, hL2⟩ := hT.left j hj _ (hlt l hl)
      rw [lt_eq hj (hlt l hl)] at hL1 hL2
      obtain ⟨hm1, hm2⟩ := tm_spec hT (hlt l hl) hg0
      rw [Nat.beq_eq, hL2, hg, hm2]
      exact ⟨fun e => by rw [e], fun e => hT.inj _ hL1 _ hm1 e⟩
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      rintro _ ⟨j, rfl⟩
      exact (key j j.isLt).1 (CFSG.KS.allN_spec h j j.isLt)
    · intro h
      exact allN3_intro fun j hj => (key j hj).2 (h _ ⟨⟨j, hj⟩, rfl⟩)

theorem wdK_succ_ne {W : List (List ℕ)} {f i : ℕ} (h : i ≠ 0) :
    wdK W PAR (f + 1) i = W.getD (pjK PAR i) [] ++ wdK W PAR f (ppK PAR i) := by
  change Bool.rec (motive := fun _ => List ℕ) (appK (W.getD (pjK PAR i) [])
    (wdK W PAR f (ppK PAR i))) [] (Nat.beq i 0) = _
  have hb : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun e => h (beq_of e)
  rw [hb, appK_eq]

theorem wd_prod {M : Type*} [Group M] {g : ℕ → M}
    (hT : TabData g (parT n PAR) (ltT n LT) n 3) {W : List (List ℕ)} (e : ℕ → M)
    (hW : ∀ j < 3, ((W.getD j []).map e).prod = g j) :
    ∀ f i, i ≤ f → i < n → ((wdK W PAR f i).map e).prod = tabElt g (parT n PAR) i := by
  intro f
  induction f with
  | zero =>
    intro i hi _
    obtain rfl : i = 0 := by omega
    rw [tabElt_zero]
    rfl
  | succ f ih =>
    intro i hi hin
    by_cases h0 : i = 0
    · subst h0
      rw [tabElt_zero]
      rfl
    · obtain ⟨hp, hj, hE⟩ := tree_of hT h0 hin
      rw [wdK_succ_ne h0, List.map_append, List.prod_append, hW _ hj, ih _ (by omega) (by omega),
        hE]

theorem lnk_spec {W : List (List ℕ)} {A : ℕ} {u : List ℕ → List ℕ} :
    ∀ (I : List ℕ) (Ws : List (List ℕ)), lnkUK W PAR n A u I Ws = true →
      List.Forall₂ (fun i w => i < n ∧ (∃ k < 81, aK A k = i) ∧ w = u (wdK W PAR n i)) I Ws
  | [], [], _ => List.Forall₂.nil
  | [], _ :: _, h => absurd h (by simp [lnkUK])
  | _ :: _, [], h => absurd h (by simp [lnkUK])
  | i :: I, w :: Ws, h => by
    change Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false (lnkUK W PAR n A u I Ws)
        (eqLK w (u (wdK W PAR n i)))) (bitK (mskK A) i)) (Nat.blt i n) = true at h
    obtain ⟨h1, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    obtain ⟨h2, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    obtain ⟨h3, h4⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    exact List.Forall₂.cons ⟨blt_of h1, (bitK_msk A i).1 h2, eqLK_eq _ _ h3⟩
      (lnk_spec I Ws h4)

theorem pwK_spec (hT : TabData g (parT n PAR) (ltT n LT) n 3) (hn : 0 < n) {a : ℕ} (ha : a < n) :
    ∀ e, pwK n PAR LT a e < n ∧ tabElt g (parT n PAR) (pwK n PAR LT a e) =
      tabElt g (parT n PAR) a ^ e
  | 0 => ⟨hn, by rw [pow_zero]; exact tabElt_zero g _⟩
  | e + 1 => by
    obtain ⟨h1, h2⟩ := pwK_spec hT hn ha e
    change tmK PAR LT n a (pwK n PAR LT a e) < n ∧
      tabElt g (parT n PAR) (tmK PAR LT n a (pwK n PAR LT a e)) = _
    obtain ⟨h3, h4⟩ := tm_spec hT ha h1
    rw [← h4, h2, pow_succ']
    exact ⟨h3, rfl⟩

theorem gen_closure (hT : TabData g (parT n PAR) (ltT n LT) n 3) (hn : 0 < n) {A : ℕ}
    (hh : subHK n A = true) {A₀ : Subgroup G}
    (hA : ∀ x, x ∈ A₀ ↔ ∃ k < 81, tabElt g (parT n PAR) (aK A k) = x) {a : List ℕ} {Ex : ℕ}
    (hg : genK n PAR LT A a Ex = true) :
    A₀ = closure (Set.range fun i : Fin 4 => tabElt g (parT n PAR) (a.getD i 0)) := by
  obtain ⟨-, hlt, -⟩ := subHK_spec hh
  unfold genK at hg
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 hg
  have hmem : ∀ i < 4, ∃ k < 81, aK A k = a.getD i 0 := fun i hi =>
    (bitK_msk A _).1 (CFSG.KS.allN_spec h1 i hi)
  have halt : ∀ i < 4, a.getD i 0 < n := fun i hi => by
    obtain ⟨k, hk, e⟩ := hmem i hi
    rw [← e]
    exact hlt k hk
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := (hA x).1 hx
    have hk' := CFSG.KS.allN_spec h2 k hk
    unfold genIK at hk'
    rw [sB_eq] at hk'
    have e := beq_of hk'
    set ex := lnK 8 Ex k
    have hC : ∀ i < 4, ∀ m, tabElt g (parT n PAR) (pwK n PAR LT (a.getD i 0) m) ∈
        closure (Set.range fun i : Fin 4 => tabElt g (parT n PAR) (a.getD i 0)) := by
      intro i hi m
      rw [(pwK_spec hT hn (halt i hi) m).2]
      exact pow_mem (subset_closure (Set.mem_range_self (⟨i, hi⟩ : Fin 4))) m
    have hP : ∀ i < 4, ∀ m, pwK n PAR LT (a.getD i 0) m < n := fun i hi m =>
      (pwK_spec hT hn (halt i hi) m).1
    rw [← e]
    obtain ⟨t3, e3⟩ := tm_spec hT (hP 2 (by norm_num) (lnK 2 ex 2)) (hP 3 (by norm_num) (lnK 2 ex 3))
    obtain ⟨t2, e2⟩ := tm_spec hT (hP 1 (by norm_num) (lnK 2 ex 1)) t3
    obtain ⟨-, e1⟩ := tm_spec hT (hP 0 (by norm_num) (lnK 2 ex 0)) t2
    rw [← e1, ← e2, ← e3]
    exact mul_mem (hC 0 (by norm_num) _) (mul_mem (hC 1 (by norm_num) _)
      (mul_mem (hC 2 (by norm_num) _) (hC 3 (by norm_num) _)))
  · rw [closure_le]
    rintro _ ⟨⟨i, hi⟩, rfl⟩
    obtain ⟨k, hk, e⟩ := hmem i hi
    exact (hA _).2 ⟨k, hk, by rw [e]⟩

end CFSG.KS.Fi23Nt

end
