module

public import Certificates.Data.Kernel.FixBoundK.TrivAut
public import CFSG.Quasithin.Background.HMathieuMask

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.FixBoundK.TrivSound

open CFSG.KLie.CT CFSG.KC.SortTree CFSG.KC.FixBoundK CFSG.KC.FixBoundK.Triv CFSG.KC.Loop
open CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem nIf_eq (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem nIf_beq (a b t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t (Nat.beq a b) = if a = b then t else e := by
  by_cases h : a = b
  · subst h
    rw [if_pos rfl, Nat.beq_refl]
  · rw [if_neg h, Bool.eq_false_iff.2 fun e => h (Nat.beq_eq ▸ e)]

theorem orB_eq (a b : Bool) : CFSG.KLie.CT.orB a b = (a || b) := by cases a <;> rfl

theorem andB_eq (a b : Bool) : CFSG.KLie.CT.andB a b = (a && b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : CFSG.KLie.CT.notB a = !a := by cases a <;> rfl

theorem strictK_eq (y : Nat) (k : Nat → Bool) : strictK y k = k y := by cases y <;> rfl

theorem lenS_eq {α : Type} (l : List α) : lenS l = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih => change Nat.succ (lenS l) = _; rw [ih]; rfl

theorem nthS_eq {α : Type} (d : α) (l : List α) (n : Nat) : nthS d l n = l.getD n d := by
  induction l generalizing n with
  | nil => rfl
  | cons x l ih =>
    cases n with
    | zero => rfl
    | succ k => rw [List.getD_cons_succ, ← ih k]; rfl

theorem allS_iff {α : Type} (f : α → Bool) (l : List α) :
    allS f l = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => exact iff_of_true rfl (fun _ h => absurd h List.not_mem_nil)
  | cons x l ih =>
    change Bool.rec (motive := fun _ => Bool) false (allS f l) (f x) = true ↔ _
    rw [bAnd_eq, Bool.and_eq_true, ih, List.forall_mem_cons]

theorem allN_iff (f : Nat → Bool) : ∀ n, allN n f = true ↔ ∀ i < n, f i = true
  | 0 => iff_of_true rfl fun i hi => absurd hi (Nat.not_lt_zero i)
  | n + 1 => by
    change CFSG.KLie.CT.andB (f n) (allN n f) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, allN_iff f n]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h2 i h
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem sumBelow_eq (m hi : Nat) (f : Nat → Nat) (hm : m ≤ 64 * hi) :
    sumBelow m hi f = ∑ i ∈ Finset.range m, f i := by
  have rec_sum : ∀ (G : Nat → Nat) (k : Nat),
      Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 => Nat.add (G l) ih2) k =
        ∑ l ∈ Finset.range k, G l := by
    intro G k
    induction k with
    | zero =>
      rw [Finset.sum_range_zero]
      rfl
    | succ k ih =>
      rw [Finset.sum_range_succ, ← ih]
      exact Nat.add_comm _ _
  have hgen : ∀ h, sumBelow m h f =
      ∑ i ∈ Finset.range (64 * h), if i < m then f i else 0 := by
    intro h
    induction h with
    | zero =>
      rw [Nat.mul_zero, Finset.sum_range_zero]
      rfl
    | succ h ih =>
      change Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
        Nat.add ((fun i => Bool.rec (motive := fun _ => Nat) 0 (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64 + sumBelow m h f = _
      rw [rec_sum, ih, Nat.mul_succ, Finset.sum_range_add,
        Nat.add_comm (Finset.sum (Finset.range 64) _)]
      refine Nat.add_left_cancel_iff.2 (Finset.sum_congr rfl fun l _ => ?_)
      have e : Nat.add (Nat.shiftLeft h 6) l = 64 * h + l := by
        change h <<< 6 + l = 64 * h + l
        rw [Nat.shiftLeft_eq, show (2 : Nat) ^ 6 = 64 from rfl]
        omega
      simp only [e, nIf_eq, Nat.blt_eq]
  rw [hgen hi, show 64 * hi = m + (64 * hi - m) by omega, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (s := Finset.range (64 * hi - m)) (fun i _ => ite_eq_right (by omega)),
    Nat.add_zero]
  exact Finset.sum_congr rfl fun i hi => ite_eq_left (Finset.mem_range.1 hi)

theorem sumBelow_card (m hi : Nat) (p : Nat → Bool) (hm : m ≤ 64 * hi) :
    sumBelow m hi (fun i => Bool.rec (motive := fun _ => Nat) 0 1 (p i)) =
      ((Finset.range m).filter fun i => p i = true).card := by
  rw [sumBelow_eq m hi _ hm, Finset.card_filter]
  exact Finset.sum_congr rfl fun i _ => nIf_eq (p i) 1 0

theorem pw2_eq (w : Nat) : pw2 w = 2 ^ w := Nat.one_shiftLeft w

theorem omK_eq : omK = 2 ^ 24 - 1 := by decide +kernel

theorem bit_eq (X i : Nat) : bit X i = X.testBit i := by
  change Nat.beq (Nat.land (Nat.shiftRight X i) 1) 1 = X.testBit i
  have h : Nat.land (Nat.shiftRight X i) 1 = X / 2 ^ i % 2 := by
    change (X >>> i) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [h, Nat.testBit_eq_decide_div_mod_eq]
  exact Bool.eq_iff_iff.2 (by rw [Nat.beq_eq, decide_eq_true_iff])

theorem actK_eq : ∀ (cs : List Nat) (m : Nat), actK cs m = actM cs m
  | [], _ => rfl
  | c :: cs, m => by
    change Nat.xor (Bool.rec (motive := fun _ => Nat) 0 c (Nat.beq (Nat.land m 1) 1))
      (actK cs (Nat.shiftRight m 1)) = actM (c :: cs) m
    have h1 : Nat.land m 1 = m % 2 := Nat.and_one_is_mod m
    have h2 : Nat.shiftRight m 1 = m / 2 := by
      change m >>> 1 = m / 2
      rw [Nat.shiftRight_eq_div_pow]
    rw [h1, h2, nIf_beq, actK_eq cs, actM]
    rfl

theorem synK_eq (x : Nat) : synK x = syndM x := by
  rw [synK, actK_eq]
  rfl

theorem cwK_eq (m : Nat) : cwK m = actM bmL m := by rw [cwK, actK_eq]

theorem synK_xor : XorLin synK := fun a b => by
  simp only [synK_eq]
  exact actM_xor _ a b

theorem cwK_xor : XorLin cwK := fun a b => by
  simp only [cwK_eq]
  exact actM_xor _ a b

theorem bmL_lt : ∀ b ∈ bmL, b < 2 ^ 24 := by decide +kernel

theorem cwK_lt (m : Nat) : cwK m < 2 ^ 24 := by
  rw [cwK_eq]
  exact actM_lt bmL_lt m

theorem cwK_zero : cwK 0 = 0 := cwK_xor.map_zero

theorem cwK_63 : cwK 63 = omK := by decide +kernel

theorem actM_zeros : ∀ (cs : List Nat), (∀ c ∈ cs, c = 0) → ∀ m, actM cs m = 0
  | [], _, _ => rfl
  | c :: cs, h, m => by
    rw [actM, actM_zeros cs (fun d hd => h d (List.mem_cons_of_mem c hd)),
      h c List.mem_cons_self]
    split_ifs <;> rfl

theorem xor_xor_cancel (a b : Nat) : a ^^^ b ^^^ b = a := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem eq_of_xor_eq_zero {a b : Nat} (h : a ^^^ b = 0) : a = b := by
  rw [← xor_xor_cancel a b, h, Nat.zero_xor]

@[expose] def IsCw (x : Nat) : Prop := x < 2 ^ 24 ∧ synK x = 0

theorem codeK_spec (h : codeK = true) :
    (∀ m < 4096, cwK m = 0 → m = 0) ∧ ∀ b ∈ bmL, synK b = 0 := by
  change Bool.rec (motive := fun _ => Bool) false
    (allS (fun b => Bool.rec (motive := fun _ => Bool) false (Nat.blt b (pw2 24))
      (Nat.beq (synK b) 0)) bmL)
    (Nat.beq (sumBelow 4096 64
      (fun m => Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq (cwK m) 0))) 1) = true at h
  rw [bAnd_eq, Bool.and_eq_true, allS_iff, Nat.beq_eq,
    sumBelow_card 4096 64 (fun m => Nat.beq (cwK m) 0) (by norm_num)] at h
  refine ⟨fun m hm hz => ?_, fun b hb => ?_⟩
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h.1
    have h0 : (0 : Nat) ∈ (Finset.range 4096).filter fun i => Nat.beq (cwK i) 0 = true := by
      rw [Finset.mem_filter, cwK_zero]
      exact ⟨by simp, rfl⟩
    have hm' : m ∈ (Finset.range 4096).filter fun i => Nat.beq (cwK i) 0 = true := by
      rw [Finset.mem_filter, hz]
      exact ⟨Finset.mem_range.2 hm, rfl⟩
    rw [ha, Finset.mem_singleton] at h0 hm'
    rw [hm', h0]
  · have := h.2 b hb
    rw [bAnd_eq, Bool.and_eq_true] at this
    exact Nat.eq_of_beq_eq_true this.1

theorem cwK_inj (hc : codeK = true) {a b : Nat} (ha : a < 4096) (hb : b < 4096)
    (h : cwK a = cwK b) : a = b := by
  have hx : cwK (a ^^^ b) = 0 := by rw [cwK_xor a b, h, Nat.xor_self]
  exact eq_of_xor_eq_zero ((codeK_spec hc).1 _
    (Nat.xor_lt_two_pow (n := 12) ha hb) hx)

theorem synK_cwK (hc : codeK = true) (m : Nat) : synK (cwK m) = 0 := by
  rw [cwK_eq, ← actM_map synK_xor]
  exact actM_zeros _ (fun c hc' => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc'
    exact (codeK_spec hc).2 b hb) m

theorem isCw_cwK (hc : codeK = true) (m : Nat) : IsCw (cwK m) := ⟨cwK_lt m, synK_cwK hc m⟩

theorem exists_cwK (hc : codeK = true) {x : Nat} (hx : IsCw x) : ∃ m < 4096, cwK m = x := by
  classical
  have hmem : ∀ m, bvec 24 (cwK m) ∈ C := fun m =>
    (bvec_mem_C_iff _).2 (by rw [← synK_eq]; exact synK_cwK hc m)
  set f : ℕ → C := fun m => ⟨bvec 24 (cwK m), hmem m⟩ with hf
  have hfinj : Set.InjOn f {m | m < 4096} := by
    intro a ha b hb h
    exact cwK_inj hc ha hb (bvec_inj (cwK_lt a) (cwK_lt b) (congrArg Subtype.val h))
  have hcardimg : (f '' {m | m < 4096}).ncard = 4096 := by
    rw [hfinj.ncard_image]
    have hset : {m : ℕ | m < 4096} = ((Finset.range 4096 : Finset ℕ) : Set ℕ) := by
      ext
      simp
    rw [hset, Set.ncard_coe_finset, Finset.card_range]
  have hcardC : Nat.card C = 4096 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := C), Nat.card_zmod, finrank_C]
    norm_num
  have hfin : Finite C := Nat.finite_of_card_ne_zero (by rw [hcardC]; norm_num)
  have huniv : f '' {m | m < 4096} = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    rw [Set.ncard_univ, hcardC, hcardimg]
  have hxC : bvec 24 x ∈ C := (bvec_mem_C_iff x).2 (by rw [← synK_eq]; exact hx.2)
  have hc' : (⟨bvec 24 x, hxC⟩ : C) ∈ f '' {m | m < 4096} := huniv ▸ Set.mem_univ _
  obtain ⟨m, hm, hfm⟩ := hc'
  exact ⟨m, hm, bvec_inj (cwK_lt m) hx.1 (congrArg Subtype.val hfm)⟩

@[expose] def pmR (σ : Nat → Nat) (x : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (if x.testBit n then 2 ^ σ n else 0) ^^^ pmR σ x n

theorem pmK_rec (G x : Nat) : ∀ n, Nat.rec (motive := fun _ => Nat) 0
    (fun j ih => Nat.xor (Bool.rec (motive := fun _ => Nat) 0 (pw2 (fget G j 5)) (bit x j)) ih) n =
    pmR (fun j => fget G j 5) x n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.rec_add_one, pmK_rec G x n, pmR, bit_eq, pw2_eq, nIf_eq]
    rfl

theorem pmK_eq (G x : Nat) : pmK G x = pmR (fun j => fget G j 5) x 24 := pmK_rec G x 24

theorem testBit_pmR (σ : Nat → Nat) (x t : Nat) : ∀ n, (∀ i j, i < j → j < n → σ i ≠ σ j) →
    (pmR σ x n).testBit t = decide (∃ j < n, x.testBit j = true ∧ σ j = t)
  | 0, _ => by simp [pmR]
  | n + 1, h => by
    rw [pmR, Nat.testBit_xor, testBit_pmR σ x t n (fun i j hij hj => h i j hij (by omega))]
    by_cases hx : x.testBit n = true
    · rw [if_pos hx, Nat.testBit_two_pow]
      by_cases hσ : σ n = t
      · have hno : ¬ ∃ j < n, x.testBit j = true ∧ σ j = t := fun ⟨j, hj, _, hj'⟩ =>
          h j n hj (by omega) (hj'.trans hσ.symm)
        rw [decide_eq_true hσ, decide_eq_false hno]
        exact (decide_eq_true ⟨n, by omega, hx, hσ⟩).symm
      · rw [decide_eq_false hσ, Bool.false_xor, decide_eq_decide]
        constructor
        · rintro ⟨j, hj, h1, h2⟩
          exact ⟨j, by omega, h1, h2⟩
        · rintro ⟨j, hj, h1, h2⟩
          refine ⟨j, ?_, h1, h2⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h' | rfl
          · exact h'
          · exact absurd h2 hσ
    · rw [if_neg hx, Nat.zero_testBit, Bool.false_xor, decide_eq_decide]
      constructor
      · rintro ⟨j, hj, h1, h2⟩
        exact ⟨j, by omega, h1, h2⟩
      · rintro ⟨j, hj, h1, h2⟩
        refine ⟨j, ?_, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h' | rfl
        · exact h'
        · exact absurd h1 hx

theorem permG_spec {G : Nat} (h : permG G = true) :
    (∀ j < 24, fget G j 5 < 24) ∧ ∀ i j, i < j → j < 24 → fget G i 5 ≠ fget G j 5 := by
  change allN 24 (fun j => CFSG.KLie.CT.andB (Nat.blt (fget G j 5) 24)
    (allN j fun i => CFSG.KLie.CT.notB (Nat.beq (fget G i 5) (fget G j 5)))) = true at h
  rw [allN_iff] at h
  refine ⟨fun j hj => ?_, fun i j hij hj e => ?_⟩
  · have := h j hj
    rw [andB_eq, Bool.and_eq_true, Nat.blt_eq] at this
    exact this.1
  · have := h j hj
    rw [andB_eq, Bool.and_eq_true, allN_iff] at this
    have h2 := this.2 i hij
    rw [notB_eq, e, Nat.beq_refl] at h2
    exact Bool.false_ne_true h2

section Perm

variable {G : Nat} (hG : permG G = true)

include hG

theorem testBit_pmK (x t : Nat) :
    (pmK G x).testBit t = decide (∃ j : Nat, j < 24 ∧ x.testBit j = true ∧ fget G j 5 = t) := by
  rw [pmK_eq, testBit_pmR _ x t 24 (permG_spec hG).2]

theorem testBit_pmK_sig (x : Nat) {j : Nat} (hj : j < 24) :
    (pmK G x).testBit (fget G j 5) = x.testBit j := by
  rw [testBit_pmK hG]
  by_cases hx : x.testBit j = true
  · rw [hx]
    exact decide_eq_true ⟨j, hj, hx, rfl⟩
  · have hno : ¬ ∃ i : Nat, i < 24 ∧ x.testBit i = true ∧ fget G i 5 = fget G j 5 := by
      rintro ⟨i, hi, h1, h2⟩
      rcases Nat.lt_trichotomy i j with hij | rfl | hij
      · exact (permG_spec hG).2 i j hij hj h2
      · exact hx h1
      · exact (permG_spec hG).2 j i hij hi h2.symm
    rw [decide_eq_false hno]
    exact (Bool.eq_false_iff.2 hx).symm

theorem testBit_pmK_ge (x : Nat) {t : Nat} (ht : 24 ≤ t) : (pmK G x).testBit t = false := by
  rw [testBit_pmK hG]
  refine decide_eq_false ?_
  rintro ⟨j, hj, -, e⟩
  have := (permG_spec hG).1 j hj
  omega

theorem exists_sig {t : Nat} (ht : t < 24) : ∃ j < 24, fget G j 5 = t := by
  classical
  have hsub : (Finset.range 24).image (fun j => fget G j 5) ⊆ Finset.range 24 := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_range.2 ((permG_spec hG).1 j (Finset.mem_range.1 hj))
  have hinj : Set.InjOn (fun j => fget G j 5) (Finset.range 24 : Set Nat) := by
    intro i hi j hj e
    have hi' := Finset.mem_range.1 hi
    have hj' := Finset.mem_range.1 hj
    rcases Nat.lt_trichotomy i j with hij | rfl | hij
    · exact absurd e ((permG_spec hG).2 i j hij hj')
    · rfl
    · exact absurd e.symm ((permG_spec hG).2 j i hij hi')
  have heq := Finset.eq_of_subset_of_card_le hsub (Finset.card_image_of_injOn hinj).ge
  have : t ∈ (Finset.range 24).image (fun j => fget G j 5) := by
    rw [heq]
    exact Finset.mem_range.2 ht
  obtain ⟨j, hj, e⟩ := Finset.mem_image.1 this
  exact ⟨j, Finset.mem_range.1 hj, e⟩

theorem pmK_ext {a b : Nat} (h : ∀ j < 24, (pmK G a).testBit (fget G j 5) =
    (pmK G b).testBit (fget G j 5)) : pmK G a = pmK G b := by
  apply Nat.eq_of_testBit_eq
  intro t
  rcases Nat.lt_or_ge t 24 with ht | ht
  · obtain ⟨j, hj, rfl⟩ := exists_sig hG ht
    exact h j hj
  · rw [testBit_pmK_ge hG a ht, testBit_pmK_ge hG b ht]

theorem pmK_lt (x : Nat) : pmK G x < 2 ^ 24 :=
  Nat.lt_pow_two_of_testBit _ fun _ ht => testBit_pmK_ge hG x ht

theorem pmK_and (x y : Nat) : pmK G (x &&& y) = pmK G x &&& pmK G y := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_and]
  rcases Nat.lt_or_ge t 24 with ht | ht
  · obtain ⟨j, hj, rfl⟩ := exists_sig hG ht
    rw [testBit_pmK_sig hG _ hj, testBit_pmK_sig hG _ hj, testBit_pmK_sig hG _ hj,
      Nat.testBit_and]
  · rw [testBit_pmK_ge hG _ ht, testBit_pmK_ge hG _ ht, Bool.false_and]

theorem pmK_xor : XorLin (pmK G) := fun x y => by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_xor]
  rcases Nat.lt_or_ge t 24 with ht | ht
  · obtain ⟨j, hj, rfl⟩ := exists_sig hG ht
    rw [testBit_pmK_sig hG _ hj, testBit_pmK_sig hG _ hj, testBit_pmK_sig hG _ hj,
      Nat.testBit_xor]
  · rw [testBit_pmK_ge hG _ ht, testBit_pmK_ge hG _ ht, testBit_pmK_ge hG _ ht]
    rfl

theorem pmK_zero : pmK G 0 = 0 := (pmK_xor hG).map_zero

theorem pmK_omK : pmK G omK = omK := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [omK_eq, Nat.testBit_two_pow_sub_one]
  rcases Nat.lt_or_ge t 24 with ht | ht
  · obtain ⟨j, hj, rfl⟩ := exists_sig hG ht
    rw [testBit_pmK_sig hG _ hj, Nat.testBit_two_pow_sub_one, decide_eq_true hj,
      decide_eq_true ht]
  · rw [testBit_pmK_ge hG _ ht, decide_eq_false (by omega)]

theorem pmK_inj {x y : Nat} (hx : x < 2 ^ 24) (hy : y < 2 ^ 24) (h : pmK G x = pmK G y) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro j
  rcases Nat.lt_or_ge j 24 with hj | hj
  · rw [← testBit_pmK_sig hG x hj, ← testBit_pmK_sig hG y hj, h]
  · rw [testBit_eq_false_of_lt_pow hx hj, testBit_eq_false_of_lt_pow hy hj]

end Perm

theorem compatK_iff (a b : Nat) : compatK a b = true ↔ synK (a &&& b) = 0 := by
  change Nat.beq (synK (a &&& b)) 0 = true ↔ _
  rw [Nat.beq_eq]

section Aut

variable {G : Nat} (hc : codeK = true) (hG : autG G = true)

include hG

theorem autG_perm : permG G = true := by
  have h := hG
  rw [autG, andB_eq, Bool.and_eq_true] at h
  exact h.1

theorem autG_basis : ∀ b ∈ bmL, synK (pmK G b) = 0 := by
  have h := hG
  rw [autG, andB_eq, Bool.and_eq_true, allS_iff] at h
  intro b hb
  exact Nat.eq_of_beq_eq_true (h.2 b hb)

include hc

theorem isCw_pmK {x : Nat} (hx : IsCw x) : IsCw (pmK G x) := by
  obtain ⟨m, -, rfl⟩ := exists_cwK hc hx
  refine ⟨pmK_lt (autG_perm hG) _, ?_⟩
  rw [cwK_eq, ← actM_map (pmK_xor (autG_perm hG)), ← actM_map synK_xor]
  refine actM_zeros _ (fun c hc' => ?_) m
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc'
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hd
  exact autG_basis hG b hb

theorem exists_pre {x : Nat} (hx : IsCw x) : ∃ y, IsCw y ∧ pmK G y = x := by
  classical
  have hP := autG_perm hG
  set S : Finset Nat := (Finset.range 4096).image cwK with hS
  have hmemS : ∀ {z}, IsCw z → z ∈ S := fun hz => by
    obtain ⟨m, hm, rfl⟩ := exists_cwK hc hz
    exact Finset.mem_image.2 ⟨m, Finset.mem_range.2 hm, rfl⟩
  have hSCw : ∀ {z}, z ∈ S → IsCw z := fun hz => by
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hz
    exact isCw_cwK hc m
  have hsub : S.image (pmK G) ⊆ S := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
    exact hmemS (isCw_pmK hc hG (hSCw hz))
  have hinj : Set.InjOn (pmK G) (S : Set Nat) := fun a ha b hb e =>
    pmK_inj hP (hSCw ha).1 (hSCw hb).1 e
  have heq := Finset.eq_of_subset_of_card_le hsub (Finset.card_image_of_injOn hinj).ge
  have hxS : x ∈ S.image (pmK G) := by
    rw [heq]
    exact hmemS hx
  obtain ⟨y, hy, e⟩ := Finset.mem_image.1 hxS
  exact ⟨y, hSCw hy, e⟩

theorem compatK_pmK (x : Nat) {y : Nat} (hy : y < 2 ^ 24) :
    compatK (pmK G x) (pmK G y) = compatK x y := by
  have hP := autG_perm hG
  have hz : x &&& y < 2 ^ 24 := Nat.and_lt_two_pow x hy
  rw [Bool.eq_iff_iff, compatK_iff, compatK_iff, ← pmK_and hP]
  constructor
  · intro h
    obtain ⟨w, hw, e⟩ := exists_pre hc hG ⟨pmK_lt hP _, h⟩
    rw [← pmK_inj hP hw.1 hz e]
    exact hw.2
  · intro h
    exact (isCw_pmK hc hG ⟨hz, h⟩).2

end Aut

theorem exclK_iff (a b : Nat) :
    exclK a b = true ↔ b = 0 ∨ b = omK ∨ b = a ∨ b = a ^^^ omK := by
  change CFSG.KLie.CT.orB (Nat.beq b 0) (CFSG.KLie.CT.orB (Nat.beq b omK) (CFSG.KLie.CT.orB (Nat.beq b a) (Nat.beq b (a ^^^ omK)))) =
    true ↔ _
  simp only [orB_eq, Bool.or_eq_true, Nat.beq_eq]

theorem spanK_iff (a b c : Nat) : spanK a b c = true ↔ exclK a c = true ∨ c = b ∨
    c = b ^^^ omK ∨ c = a ^^^ b ∨ c = a ^^^ b ^^^ omK := by
  change CFSG.KLie.CT.orB (exclK a c) (CFSG.KLie.CT.orB (Nat.beq c b) (CFSG.KLie.CT.orB (Nat.beq c (b ^^^ omK))
    (CFSG.KLie.CT.orB (Nat.beq c (a ^^^ b)) (Nat.beq c (a ^^^ b ^^^ omK))))) = true ↔ _
  simp only [orB_eq, Bool.or_eq_true, Nat.beq_eq]

@[expose] def Good (x₁ : Nat) : Prop :=
  ∀ x₂ x₃, IsCw x₂ → IsCw x₃ → compatK x₁ x₂ = true → compatK x₁ x₃ = true →
    compatK x₂ x₃ = true → exclK x₁ x₂ = true ∨ spanK x₁ x₂ x₃ = true

theorem exclK_map {f : Nat → Nat} (hf : XorLin f) (hΩ : f omK = omK) {a b : Nat}
    (h : exclK a b = true) : exclK (f a) (f b) = true := by
  rw [exclK_iff] at h ⊢
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl hf.map_zero
  · exact Or.inr (Or.inl hΩ)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (by rw [hf a omK, hΩ])))

theorem spanK_map {f : Nat → Nat} (hf : XorLin f) (hΩ : f omK = omK) {a b c : Nat}
    (h : spanK a b c = true) : spanK (f a) (f b) (f c) = true := by
  rw [spanK_iff] at h ⊢
  rcases h with h | rfl | rfl | rfl | rfl
  · exact Or.inl (exclK_map hf hΩ h)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl (by rw [hf b omK, hΩ])))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hf a b))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by rw [hf (a ^^^ b) omK, hf a b, hΩ]))))

theorem good_pmK {G : Nat} (hc : codeK = true) (hG : autG G = true) {x₁ : Nat} (h : Good x₁) :
    Good (pmK G x₁) := by
  have hP := autG_perm hG
  intro x₂ x₃ h2 h3 c12 c13 c23
  obtain ⟨y₂, hy₂, rfl⟩ := exists_pre hc hG h2
  obtain ⟨y₃, hy₃, rfl⟩ := exists_pre hc hG h3
  rw [compatK_pmK hc hG _ hy₂.1] at c12
  rw [compatK_pmK hc hG _ hy₃.1] at c13 c23
  rcases h y₂ y₃ hy₂ hy₃ c12 c13 c23 with he | hs
  · exact Or.inl (exclK_map (pmK_xor hP) (pmK_omK hP) he)
  · exact Or.inr (spanK_map (pmK_xor hP) (pmK_omK hP) hs)

theorem and_xor_omK (a : Nat) {y : Nat} (hy : y < 2 ^ 24) : (a ^^^ omK) &&& y = (a &&& y) ^^^ y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_and, omK_eq,
    Nat.testBit_two_pow_sub_one]
  rcases Nat.lt_or_ge i 24 with hi | hi
  · rw [decide_eq_true hi]
    cases a.testBit i <;> cases y.testBit i <;> rfl
  · rw [testBit_eq_false_of_lt_pow hy hi]
    simp

theorem compatK_xor_omK (x : Nat) {y : Nat} (hy : IsCw y) :
    compatK (x ^^^ omK) y = compatK x y := by
  rw [Bool.eq_iff_iff, compatK_iff, compatK_iff, and_xor_omK x hy.1, synK_xor (x &&& y) y, hy.2,
    Nat.xor_zero]

theorem exclK_xor_omK (a b : Nat) : exclK (a ^^^ omK) b = exclK a b := by
  rw [Bool.eq_iff_iff, exclK_iff, exclK_iff, xor_xor_cancel]
  tauto

theorem spanK_xor_omK (a b c : Nat) : spanK (a ^^^ omK) b c = spanK a b c := by
  have e1 : a ^^^ omK ^^^ b = a ^^^ b ^^^ omK := by
    rw [Nat.xor_assoc, Nat.xor_comm omK b, ← Nat.xor_assoc]
  rw [Bool.eq_iff_iff, spanK_iff, spanK_iff, exclK_xor_omK, e1, xor_xor_cancel]
  tauto

theorem good_xor_omK {x₁ : Nat} (h : Good x₁) : Good (x₁ ^^^ omK) := by
  intro x₂ x₃ h2 h3 c12 c13 c23
  rw [compatK_xor_omK _ h2] at c12
  rw [compatK_xor_omK _ h3] at c13
  rw [exclK_xor_omK, spanK_xor_omK]
  exact h x₂ x₃ h2 h3 c12 c13 c23

theorem sortK_spec (x₁ : Nat) : ∀ (l : List Nat) (p : Nat), sortK x₁ l p = true →
    l.Nodup ∧ ∀ m ∈ l, p ≤ m ∧ m < 4096 ∧ compatK x₁ (cwK m) = true
  | [], _, _ => ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
  | m :: l, p, h => by
    change Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false (sortK x₁ l (Nat.succ m)) (compatK x₁ (cwK m)))
      (Nat.blt m 4096)) (Nat.ble p m) = true at h
    rw [bAnd_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      Nat.ble_eq, Nat.blt_eq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    obtain ⟨hnd, hl⟩ := sortK_spec x₁ l (Nat.succ m) h4
    refine ⟨List.nodup_cons.2 ⟨fun hm => ?_, hnd⟩, ?_⟩
    · have := (hl m hm).1
      omega
    · intro m' hm'
      rcases List.mem_cons.1 hm' with rfl | hm'
      · exact ⟨h1, h2, h3⟩
      · obtain ⟨a, b, c⟩ := hl m' hm'
        exact ⟨by omega, b, c⟩

theorem trivRep_spec {x₁ : Nat} {k₁ : List Nat} (h : trivRep x₁ k₁ = true) {m₂ m₃ : Nat}
    (hm₂ : m₂ < 4096) (hm₃ : m₃ < 4096) (c12 : compatK x₁ (cwK m₂) = true)
    (c13 : compatK x₁ (cwK m₃) = true) (c23 : compatK (cwK m₂) (cwK m₃) = true) :
    exclK x₁ (cwK m₂) = true ∨ spanK x₁ (cwK m₂) (cwK m₃) = true := by
  classical
  unfold trivRep at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, lenS_eq,
    sumBelow_card 4096 64 _ (by norm_num), allS_iff] at h
  obtain ⟨hs, hcnt, hall⟩ := h
  obtain ⟨hnd, hl⟩ := sortK_spec x₁ k₁ 0 hs
  have hsub : k₁.toFinset ⊆ (Finset.range 4096).filter fun m => compatK x₁ (cwK m) = true := by
    intro m hm
    obtain ⟨-, a, b⟩ := hl m (List.mem_toFinset.1 hm)
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 a, b⟩
  have heq := Finset.eq_of_subset_of_card_le hsub
    (le_of_eq (by rw [hcnt, List.toFinset_card_of_nodup hnd]))
  have hin : ∀ m < 4096, compatK x₁ (cwK m) = true → m ∈ k₁ := by
    intro m hm hcm
    have : m ∈ k₁.toFinset := by
      rw [heq]
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hm, hcm⟩
    exact List.mem_toFinset.1 this
  have h2 := hall m₂ (hin m₂ hm₂ c12)
  rw [strictK_eq, orB_eq, Bool.or_eq_true, allS_iff] at h2
  rcases h2 with h2 | h2
  · exact Or.inl h2
  · have h3 := h2 m₃ (hin m₃ hm₃ c13)
    rw [strictK_eq, orB_eq, Bool.or_eq_true, notB_eq, c23] at h3
    rcases h3 with h3 | h3
    · exact absurd h3 (by decide)
    · exact Or.inr h3

theorem good_of_trivRep (hc : codeK = true) {x₁ : Nat} {k₁ : List Nat}
    (h : trivRep x₁ k₁ = true) : Good x₁ := by
  intro x₂ x₃ h2 h3 c12 c13 c23
  obtain ⟨m₂, hm₂, rfl⟩ := exists_cwK hc h2
  obtain ⟨m₃, hm₃, rfl⟩ := exists_cwK hc h3
  exact trivRep_spec h hm₂ hm₃ c12 c13 c23

theorem wordK_cons (GS GA k : Nat) (w : List Nat) (y : Nat) :
    wordK GS GA (k :: w) y = wordK GS GA w (pmK (genK GS GA k) y) := rfl

theorem good_word {GS GA : Nat} (hc : codeK = true) (ha : autK GS GA = true) :
    ∀ (w : List Nat), (∀ l ∈ w, l < 12) → ∀ y, Good y → Good (wordK GS GA w y)
  | [], _, _, h => h
  | k :: w, hw, y, h => by
    rw [wordK_cons]
    refine good_word hc ha w (fun l hl => hw l (List.mem_cons_of_mem k hl)) _ ?_
    exact good_pmK hc ((allN_iff _ 12).1 ha k (hw k List.mem_cons_self)) h

theorem entK_spec {GS GA : Nat} {reps : List Nat} {k : Nat} {e : Nat × List Nat}
    (h : entK GS GA reps k e = true) : e.1 < reps.length ∧ (∀ l ∈ e.2, l < 12) ∧
      (wordK GS GA e.2 (reps.getD e.1 0) = cwK (2 * k) ∨
        wordK GS GA e.2 (reps.getD e.1 0) = cwK (2 * k) ^^^ omK) := by
  change Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
      (strictK (wordK GS GA e.2 (nthS 0 reps e.1)) fun y =>
        strictK (cwK (Nat.shiftLeft k 1)) fun c => CFSG.KLie.CT.orB (Nat.beq y c) (Nat.beq y (c ^^^ omK)))
      (allS (fun l => Nat.blt l 12) e.2)) (Nat.blt e.1 (lenS reps)) = true at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, strictK_eq, strictK_eq, orB_eq,
    Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq, Nat.blt_eq, lenS_eq, allS_iff, nthS_eq] at h
  have hk : Nat.shiftLeft k 1 = 2 * k := by
    change k <<< 1 = 2 * k
    rw [Nat.shiftLeft_eq]
    omega
  rw [hk] at h
  exact ⟨h.1, fun l hl => Nat.blt_eq ▸ h.2.1 l hl, h.2.2⟩

theorem run_spec {GS GA : Nat} {reps : List Nat} : ∀ (l : List (Nat × List Nat)) (k₀ : Nat),
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun e _ ih k => Bool.rec (motive := fun _ => Bool) false (ih (Nat.succ k))
        (entK GS GA reps k e)) l k₀ = true →
    ∀ j < l.length, entK GS GA reps (k₀ + j) (l.getD j (0, [])) = true
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | e :: l, k₀, h, j, hj => by
    change Bool.rec (motive := fun _ => Bool) false (List.rec (motive := fun _ => Nat → Bool)
      (fun _ => true) (fun e _ ih k => Bool.rec (motive := fun _ => Bool) false (ih (Nat.succ k))
        (entK GS GA reps k e)) l (Nat.succ k₀)) (entK GS GA reps k₀ e) = true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    cases j with
    | zero => exact h.1
    | succ j =>
      have := run_spec l (Nat.succ k₀) h.2 j (by simpa using hj)
      have e2 : k₀ + (j + 1) = Nat.succ k₀ + j := by omega
      rw [List.getD_cons_succ, e2]
      exact this

theorem cover_of_wsAt {GS GA : Nat} {reps : List Nat} {ws : List (List (Nat × List Nat))}
    (hws : ∀ c < 16, wsAt GS GA reps ws c = true) {k : Nat} (hk1 : 1 ≤ k) (hk : k < 2048) :
    ∃ i < reps.length, ∃ w : List Nat, (∀ l ∈ w, l < 12) ∧
      (wordK GS GA w (reps.getD i 0) = cwK (2 * k) ∨
        wordK GS GA w (reps.getD i 0) = cwK (2 * k) ^^^ omK) := by
  set c := (k - 1) / 128 with hc
  set j := (k - 1) % 128 with hj
  have hc16 : c < 16 := by omega
  have h := hws c hc16
  change Bool.rec (motive := fun _ => Bool) false
    (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun e _ ih k => Bool.rec (motive := fun _ => Bool) false (ih (Nat.succ k))
        (entK GS GA reps k e)) (nthS [] ws c) (Nat.succ (128 * c)))
    (Nat.beq (lenS (nthS [] ws c)) (Bool.rec (motive := fun _ => Nat) 128 (2047 - 128 * c)
      (Nat.blt (2047 - 128 * c) 128))) = true at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hlen, hrun⟩ := h
  simp only [Nat.beq_eq, lenS_eq, nIf_eq, Nat.blt_eq] at hlen
  have hjl : j < (nthS [] ws c).length := by
    rw [hlen]
    split_ifs <;> omega
  have he := entK_spec (run_spec _ _ hrun j hjl)
  have hkk : Nat.succ (128 * c) + j = k := by omega
  rw [hkk] at he
  exact ⟨_, he.1, _, he.2.1, he.2.2⟩

theorem good_all {GS GA : Nat} {reps : List Nat} {k1s : List (List Nat)}
    {ws : List (List (Nat × List Nat))} (hc : codeK = true) (ha : autK GS GA = true)
    (hrep : ∀ i < reps.length, trivAt reps k1s i = true)
    (hws : ∀ c < 16, wsAt GS GA reps ws c = true) {x₁ : Nat} (hx : IsCw x₁) (h0 : x₁ ≠ 0)
    (hΩ : x₁ ≠ omK) : Good x₁ := by
  obtain ⟨m, hm, rfl⟩ := exists_cwK hc hx
  have h63 : cwK (m ^^^ 63) = cwK m ^^^ omK := by rw [cwK_xor m 63, cwK_63]
  obtain ⟨m', hm', hev, hcw⟩ : ∃ m', m' < 4096 ∧ m' % 2 = 0 ∧
      (cwK m' = cwK m ∨ cwK m' = cwK m ^^^ omK) := by
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · exact ⟨m, hm, h, Or.inl rfl⟩
    · refine ⟨m ^^^ 63, Nat.xor_lt_two_pow (n := 12) hm (by norm_num), ?_, Or.inr h63⟩
      rcases Nat.mod_two_eq_zero_or_one (m ^^^ 63) with h' | h'
      · exact h'
      · exact absurd ⟨fun _ => by norm_num, fun _ => h⟩ ((mod_two_xor m 63).1 h')
  have hk1 : 1 ≤ m' / 2 := by
    by_contra hz
    have hm0 : m' = 0 := by omega
    rw [hm0, cwK_zero] at hcw
    rcases hcw with e | e
    · exact h0 e.symm
    · exact hΩ (by rw [← xor_xor_cancel (cwK m) omK, ← e, Nat.zero_xor])
  obtain ⟨i, hi, w, hw, hword⟩ := cover_of_wsAt hws hk1 (by omega)
  have h2k : 2 * (m' / 2) = m' := by omega
  rw [h2k] at hword
  have hrepi := hrep i hi
  rw [trivAt, nthS_eq, nthS_eq] at hrepi
  have hg := good_word hc ha w hw _ (good_of_trivRep hc hrepi)
  have hgm' : Good (cwK m') := by
    rcases hword with e | e
    · rwa [e] at hg
    · have := good_xor_omK hg
      rwa [e, xor_xor_cancel] at this
  rcases hcw with e | e
  · rwa [e] at hgm'
  · have := good_xor_omK hgm'
    rwa [e, xor_xor_cancel] at this

theorem triv_spec {GS GA : Nat} {reps : List Nat} {k1s : List (List Nat)}
    {ws : List (List (Nat × List Nat))} (hc : codeK = true) (ha : autK GS GA = true)
    (hrep : ∀ i < reps.length, trivAt reps k1s i = true)
    (hws : ∀ c < 16, wsAt GS GA reps ws c = true) {x₁ : Nat} (hx₁ : IsCw x₁) :
    x₁ = 0 ∨ x₁ = omK ∨
      (∀ x₂, IsCw x₂ → synK (x₁ &&& x₂) = 0 →
        x₂ = 0 ∨ x₂ = omK ∨ x₂ = x₁ ∨ x₂ = x₁ ^^^ omK ∨
          (∀ x₃, IsCw x₃ → synK (x₁ &&& x₃) = 0 → synK (x₂ &&& x₃) = 0 →
            x₃ = 0 ∨ x₃ = omK ∨ x₃ = x₁ ∨ x₃ = x₁ ^^^ omK ∨ x₃ = x₂ ∨ x₃ = x₂ ^^^ omK ∨
              x₃ = x₁ ^^^ x₂ ∨ x₃ = x₁ ^^^ x₂ ^^^ omK)) := by
  by_cases h0 : x₁ = 0
  · exact Or.inl h0
  by_cases hΩ : x₁ = omK
  · exact Or.inr (Or.inl hΩ)
  have hg := good_all hc ha hrep hws hx₁ h0 hΩ
  refine Or.inr (Or.inr fun x₂ hx₂ c12 => ?_)
  by_cases he : exclK x₁ x₂ = true
  · rw [exclK_iff] at he
    tauto
  refine Or.inr (Or.inr (Or.inr (Or.inr fun x₃ hx₃ c13 c23 => ?_)))
  rcases hg x₂ x₃ hx₂ hx₃ ((compatK_iff _ _).2 c12) ((compatK_iff _ _).2 c13)
    ((compatK_iff _ _).2 c23) with h | h
  · exact absurd h he
  · rw [spanK_iff, exclK_iff] at h
    tauto

end CFSG.KC.FixBoundK.TrivSound

end
