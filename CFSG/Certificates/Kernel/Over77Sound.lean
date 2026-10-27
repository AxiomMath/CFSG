module

public import Certificates.Data.Kernel.Over77.Checks
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.KS.Over77

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PF CFSG.KC.Over77

@[expose] def FR (a : Nat) (f : Fin 77 → Fin 77) : Prop :=
  ∀ x : Fin 77, pg 7 (mask 7) a x.val = (f x).val

@[expose] noncomputable def dec (a : Nat) (x : Fin 77) : Fin 77 :=
  ⟨pg 7 (mask 7) a x.val % 77, Nat.mod_lt _ (by decide)⟩

theorem cp_eq (a b : Nat) : cp a b = pcomp 77 7 (mask 7) a b := rfl

theorem fr_cp {a b : Nat} {f g : Fin 77 → Fin 77} (ha : FR a f) (hb : FR b g) :
    FR (cp a b) (f ∘ g) := fun x => by
  change pg 7 (mask 7) (pcomp 77 7 (mask 7) a b) x.val = (f (g x)).val
  rw [pg_pcomp (n := 77) (by decide) x.2, hb x, ha (g x)]

theorem fr_pidn : FR (pidn 77 7) id := fun x => pg_pidn (by decide) (by decide) x.2

theorem fr_one : FR (pidn 77 7) ⇑(1 : Equiv.Perm (Fin 77)) := by
  rw [Equiv.Perm.coe_one]
  exact fr_pidn

theorem fr_unique {a : Nat} {f g : Fin 77 → Fin 77} (hf : FR a f) (hg : FR a g) : f = g :=
  funext fun x => Fin.ext ((hf x).symm.trans (hg x))

theorem fr_dec {a : Nat} (h : canon a = true) : FR a (dec a) := by
  have h' : canonK 77 7 (mask 7) 539 a = true := h
  obtain ⟨_, _, _, hlt⟩ := canon_facts h'
  intro x
  exact (Nat.mod_eq_of_lt (hlt x.val x.2)).symm

theorem fr_mul {a b : Nat} {g h : Equiv.Perm (Fin 77)} (ha : FR a ⇑g) (hb : FR b ⇑h) :
    FR (cp a b) ⇑(g * h) := by
  rw [Equiv.Perm.coe_mul]
  exact fr_cp ha hb

theorem fr_of_ofFn {a : Nat} {g : Equiv.Perm (Fin 77)} {d : Array Nat}
    (h : Array.ofFn (fun i : Fin 77 => (g i : Nat)) = d)
    (hb : ∀ i < 77, pg 7 (mask 7) a i = d.getD i 0) : FR a ⇑g := by
  intro x
  rw [hb x x.2, ← h]
  simp [x.2]

@[expose] def wordP (G : Nat → Equiv.Perm (Fin 77)) : Nat → Nat → Equiv.Perm (Fin 77)
  | 0, _ => 1
  | n + 1, W => G (Nat.land W 3) * wordP G n (Nat.shiftRight W 2)

theorem wordV_succ (g : Nat → Nat) (n W : Nat) :
    wordV g (n + 1) W = cp (g (Nat.land W 3)) (wordV g n (Nat.shiftRight W 2)) := by
  change strictN (wordV g n (Nat.shiftRight W (nat_lit 2)))
    (fun v => cp (g (Nat.land W (nat_lit 3))) v) = _
  rw [strictN_eqP]

theorem fr_wordV {g : Nat → Nat} {G : Nat → Equiv.Perm (Fin 77)} (hg : ∀ c, FR (g c) ⇑(G c)) :
    ∀ n W, FR (wordV g n W) ⇑(wordP G n W)
  | 0, _ => fr_one
  | n + 1, W => by
    rw [wordV_succ]
    exact fr_mul (hg _) (fr_wordV hg n _)

theorem wordP_mem {G : Nat → Equiv.Perm (Fin 77)} {H : Subgroup (Equiv.Perm (Fin 77))}
    (hG : ∀ c, G c ∈ H) : ∀ n W, wordP G n W ∈ H
  | 0, _ => H.one_mem
  | n + 1, _ => H.mul_mem (hG _) (wordP_mem hG n _)

@[expose] def let4P (a b z y : Equiv.Perm (Fin 77)) (c : Nat) : Equiv.Perm (Fin 77) :=
  if c = 0 then a else if c = 1 then b else if c = 2 then z else y

theorem beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem fr_let4 {A B Z Y : Nat} {a b z y : Equiv.Perm (Fin 77)} (hA : FR A ⇑a) (hB : FR B ⇑b)
    (hZ : FR Z ⇑z) (hY : FR Y ⇑y) (c : Nat) : FR (let4 A B Z Y c) ⇑(let4P a b z y c) := by
  unfold let4 let4P
  by_cases h0 : c = 0
  · subst h0
    exact hA
  rw [if_neg h0, beq_false h0]
  by_cases h1 : c = 1
  · subst h1
    exact hB
  rw [if_neg h1, beq_false h1]
  by_cases h2 : c = 2
  · subst h2
    exact hZ
  rw [if_neg h2, beq_false h2]
  exact hY

theorem let4P_mem {a b z y : Equiv.Perm (Fin 77)} {H : Subgroup (Equiv.Perm (Fin 77))}
    (ha : a ∈ H) (hb : b ∈ H) (hz : z ∈ H) (hy : y ∈ H) (c : Nat) : let4P a b z y c ∈ H := by
  unfold let4P
  split_ifs
  exacts [ha, hb, hz, hy]

theorem bIf_iff (b x y : Bool) : Bool.rec (motive := fun _ => Bool) y x b = true ↔
    (b = true ∧ x = true) ∨ (b = false ∧ y = true) := by
  cases b <;> simp

theorem beqF_iff {a b : Nat} : Nat.beq a b = false ↔ a ≠ b := by
  constructor
  · intro h e
    subst e
    rw [Nat.beq_refl] at h
    exact Bool.noConfusion h
  · exact beq_false

theorem mulK_spec {T P S : Nat → Nat} {i D : Nat} (h : mulK T P S i D = true) :
    ∀ l < 8, ∀ k < 9, ∃ p < 110, ∃ j' < 8064, cp (T (8 * i + l)) (S k) = cp (P p) (T j') := by
  intro l hl k hk
  unfold mulK at h
  have e : Nat.add (Nat.shiftLeft i (nat_lit 3)) (Nat.add (nat_lit 0) l) = 8 * i + l := by
    change i <<< 3 + (0 + l) = 8 * i + l
    rw [Nat.shiftLeft_eq]
    omega
  have ek : Nat.add (nat_lit 0) k = k := Nat.zero_add k
  have h1 := allBlk_spec h l hl
  beta_reduce at h1
  rw [e, strictB_eqP] at h1
  beta_reduce at h1
  have h2 := allBlk_spec h1 k hk
  beta_reduce at h2
  rw [ek] at h2
  simp only [strictB_eqP, bIf_iff, Nat.blt_eq, Nat.beq_eq, Bool.false_eq_true, and_false,
    or_false] at h2
  obtain ⟨hp, hj, he⟩ := h2
  exact ⟨_, hp, _, hj, he⟩

theorem clsK_spec {T P X : Nat → Nat} {i D : Nat} (h : clsK T P X i D = true) :
    ∀ l < 32, canon (T (32 * i + l)) = true ∧ ∃ p < 110, T (32 * i + l) = P p ∨
      ∃ c < 82, ∃ q < 110, T (32 * i + l) = cp (cp (P p) (X c)) (P q) := by
  intro l hl
  unfold clsK at h
  have e : Nat.add (Nat.shiftLeft i (nat_lit 5)) (Nat.add (nat_lit 0) l) = 32 * i + l := by
    change i <<< 5 + (0 + l) = 32 * i + l
    rw [Nat.shiftLeft_eq]
    omega
  have h1 := allBlk_spec h l hl
  beta_reduce at h1
  rw [e] at h1
  simp only [strictB_eqP, bIf_iff, Nat.blt_eq, Nat.beq_eq, beqF_iff, Nat.sub_eq,
    Bool.false_eq_true, and_false, or_false] at h1
  obtain ⟨hc, hp, hr⟩ := h1
  refine ⟨hc, _, hp, ?_⟩
  rcases hr with ⟨_, he⟩ | ⟨hc0, hc83, hq, he⟩
  · exact Or.inl he
  · exact Or.inr ⟨_, by omega, _, hq, he⟩

theorem pinv_apply (f : Equiv.Perm (Fin 77)) (y : Fin 77) : f⁻¹ (f y) = y := by
  rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]

theorem papply_inv (f : Equiv.Perm (Fin 77)) (y : Fin 77) : f (f⁻¹ y) = y := by
  rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]

theorem over77_sound {T P X S : Nat → Nat} {A B Z Sig : Nat}
    (hT0 : CFSG.KC.Over77.idK (T 0) = true)
    (hmul : ∀ i < 1008, ∃ D, mulK T P S i D = true)
    (hcls : ∀ i < 252, ∃ D, clsK T P X i D = true)
    (hpw : ∀ p < 110, ∃ len W, pwK A B Z P p len W = true)
    (hsw : ∀ i < 82, ∃ len W, swK A B Z X Sig i len W = true)
    {pA pB pZ σ : Equiv.Perm (Fin 77)} {s : Fin 9 → Equiv.Perm (Fin 77)}
    (hA : FR A ⇑pA) (hB : FR B ⇑pB) (hZ : FR Z ⇑pZ) (hσ : FR Sig ⇑σ)
    (hs : ∀ k : Fin 9, FR (S k) ⇑(s k))
    (L : Subgroup (Equiv.Perm (Fin 77))) (hPL : Subgroup.closure {pA, pB, pZ} ≤ L)
    (hL : L ≤ Subgroup.closure (Set.range s))
    (hnot : ¬ L ≤ Subgroup.closure {pA, pB, pZ}) : σ ∈ L := by
  set Q : Subgroup (Equiv.Perm (Fin 77)) := Subgroup.closure {pA, pB, pZ} with hQ
  have hAP : pA ∈ Q := Subgroup.subset_closure (by simp)
  have hBP : pB ∈ Q := Subgroup.subset_closure (by simp)
  have hZP : pZ ∈ Q := Subgroup.subset_closure (by simp)
  have hM : ∀ j < 8064, ∀ k < 9, ∃ p < 110, ∃ j' < 8064, cp (T j) (S k) = cp (P p) (T j') := by
    intro j hj k hk
    obtain ⟨D, hD⟩ := hmul (j / 8) (by omega)
    have := mulK_spec hD (j % 8) (Nat.mod_lt _ (by decide)) k hk
    rwa [Nat.div_add_mod] at this
  have hC : ∀ j < 8064, canon (T j) = true ∧ ∃ p < 110, T j = P p ∨
      ∃ c < 82, ∃ q < 110, T j = cp (cp (P p) (X c)) (P q) := by
    intro j hj
    obtain ⟨D, hD⟩ := hcls (j / 32) (by omega)
    have := clsK_spec hD (j % 32) (Nat.mod_lt _ (by decide))
    rwa [Nat.div_add_mod] at this
  have hPr : ∀ p < 110, ∃ g ∈ Q, FR (P p) ⇑g := by
    intro p hp
    obtain ⟨len, W, h⟩ := hpw p hp
    have h' : Nat.beq (P p) (wordV (let4 A B Z (pidn 77 7)) len W) = true := h
    refine ⟨wordP (let4P pA pB pZ 1) len W,
      wordP_mem (let4P_mem hAP hBP hZP Q.one_mem) len W, ?_⟩
    rw [Nat.eq_of_beq_eq_true h']
    exact fr_wordV (fr_let4 hA hB hZ fr_one) len W
  have hX : ∀ i < 82, canon (X i) = true ∧ ∀ H : Subgroup (Equiv.Perm (Fin 77)), Q ≤ H →
      ∀ x ∈ H, ⇑x = dec (X i) → σ ∈ H := by
    intro i hi
    obtain ⟨len, W, h⟩ := hsw i hi
    unfold swK at h
    simp only [strictB_eqP, bIf_iff, Nat.beq_eq, Bool.false_eq_true, and_false, or_false] at h
    refine ⟨h.1, fun H hQH x hxH hx => ?_⟩
    have hxr : FR (X i) ⇑x := by
      rw [hx]
      exact fr_dec h.1
    have hw := fr_wordV (fr_let4 hA hB hZ hxr) len W
    rw [h.2] at hw
    have e : σ = wordP (let4P pA pB pZ x) len W := DFunLike.coe_injective (fr_unique hσ hw)
    rw [e]
    exact wordP_mem (let4P_mem (hQH hAP) (hQH hBP) (hQH hZP) hxH) len W
  have hT0' : dec (T 0) = id := by
    have h0 : Nat.beq (T 0) (pidn 77 7) = true := hT0
    have hf : FR (T 0) id := by
      rw [Nat.eq_of_beq_eq_true h0]
      exact fr_pidn
    exact fr_unique (fr_dec (hC 0 (by decide)).1) hf
  let R : Equiv.Perm (Fin 77) → Prop := fun g => ∃ j < 8064, ∃ p ∈ Q, ⇑g = ⇑p ∘ dec (T j)
  have hstep : ∀ k : Fin 9, ∀ g, R g → R (g * s k) := by
    rintro k g ⟨j, hj, p, hp, hg⟩
    obtain ⟨q, hq, j', hj', e⟩ := hM j hj k k.2
    obtain ⟨gq, hgq, hfq⟩ := hPr q hq
    refine ⟨j', hj', p * gq, Q.mul_mem hp hgq, ?_⟩
    have h1 := fr_cp (fr_dec (hC j hj).1) (hs k)
    have h2 := fr_cp hfq (fr_dec (hC j' hj').1)
    rw [e] at h1
    have h3 := fr_unique h1 h2
    funext x
    have h4 := congrFun h3 x
    simp only [Function.comp_apply] at h4
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, hg, h4]
  have hstep_pow : ∀ k : Fin 9, ∀ m : Nat, ∀ g, R g → R (g * s k ^ m) := by
    intro k m
    induction m with
    | zero => intro g hg; simpa using hg
    | succ m ih => intro g hg; rw [pow_succ, ← mul_assoc]; exact hstep k _ (ih g hg)
  have hcover : ∀ g ∈ Subgroup.closure (Set.range s), R g := by
    intro g hg
    refine Subgroup.closure_induction_right (p := fun g _ => R g) ?_ ?_ ?_ hg
    · refine ⟨0, by decide, 1, Q.one_mem, ?_⟩
      rw [hT0', Function.comp_id]
    · rintro x - y ⟨k, rfl⟩ hx
      exact hstep k x hx
    · rintro x - y ⟨k, rfl⟩ hx
      have h1 : s k * s k ^ (orderOf (s k) - 1) = 1 := by
        rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos (s k))]
        exact pow_orderOf_eq_one (s k)
      rw [inv_eq_of_mul_eq_one_right h1]
      exact hstep_pow k _ x hx
  obtain ⟨g, hgL, hgQ⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  obtain ⟨j, hj, p, hp, hg⟩ := hcover g (hL hgL)
  have hrL : p⁻¹ * g ∈ L := L.mul_mem (L.inv_mem (hPL hp)) hgL
  have hr : ⇑(p⁻¹ * g) = dec (T j) := by
    funext x
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, hg, pinv_apply]
  have hrT : FR (T j) ⇑(p⁻¹ * g) := by
    rw [hr]
    exact fr_dec (hC j hj).1
  obtain ⟨_, q, hq, hcase⟩ := hC j hj
  obtain ⟨gq, hgq, hfq⟩ := hPr q hq
  rcases hcase with e | ⟨c, hc, q', hq', e⟩
  · rw [e] at hrT
    have e2 : p⁻¹ * g = gq := DFunLike.coe_injective (fr_unique hrT hfq)
    have e3 : g = p * gq := by rw [← e2, mul_inv_cancel_left]
    exact absurd (by rw [e3]; exact Q.mul_mem hp hgq) hgQ
  · obtain ⟨gq', hgq', hfq'⟩ := hPr q' hq'
    obtain ⟨hcX, hσX⟩ := hX c hc
    rw [e] at hrT
    have h3 := fr_unique hrT (fr_cp (fr_cp hfq (fr_dec hcX)) hfq')
    refine hσX L hPL (gq⁻¹ * (p⁻¹ * g) * gq'⁻¹)
      (L.mul_mem (L.mul_mem (L.inv_mem (hPL hgq)) hrL) (L.inv_mem (hPL hgq'))) ?_
    funext x
    have h4 := congrFun h3 (gq'⁻¹ x)
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, papply_inv] at h4 ⊢
    rw [h4, pinv_apply]

end CFSG.KS.Over77

end
