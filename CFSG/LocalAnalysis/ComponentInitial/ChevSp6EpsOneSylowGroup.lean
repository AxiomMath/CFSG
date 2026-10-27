module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneSylowSearch
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneOqInputs
public import Batteries.Data.Nat.Bitwise.Lemmas
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

open CFSG.EvenSmallLie.OmegaEight.SpBranch (xorBits xorBits_succ xorBits_zero eq_xorBits xorBits_lt
  xorBits_two_pow_of_lt)

theorem xorBits_xor (n : ℕ) (f : ℕ → ℕ) (v w : ℕ) :
    xorBits n f (v ^^^ w) = xorBits n f v ^^^ xorBits n f w := by
  induction n with
  | zero => simp [xorBits_zero]
  | succ n ih =>
    rw [xorBits_succ, xorBits_succ, xorBits_succ, ih, Nat.testBit_xor]
    cases v.testBit n <;> cases w.testBit n <;>
      simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

theorem evalV_xor (l : List ℕ) (v w : ℕ) : evalV l (v ^^^ w) = evalV l v ^^^ evalV l w :=
  xorBits_xor 6 _ v w

theorem evalE_xor (l : List ℕ) (x y : ℕ) : evalE l (x ^^^ y) = evalE l x ^^^ evalE l y :=
  xorBits_xor 9 _ x y

theorem evalV_lt {l : List ℕ} (hl : ∀ a ∈ l, a < 64) (v : ℕ) : evalV l v < 64 := by
  have h := xorBits_lt (n := 6) (f := fun j => l.getD j 0) (fun j _ => by
    rw [List.getD_eq_getElem?_getD]
    rcases h : l[j]? with _ | a
    · simp
    · exact hl a (List.mem_of_getElem? h)) v
  exact h

theorem evalE_lt {l : List ℕ} (hl : ∀ a ∈ l, a < 512) (x : ℕ) : evalE l x < 512 := by
  have h := xorBits_lt (n := 9) (f := fun j => l.getD j 0) (fun j _ => by
    rw [List.getD_eq_getElem?_getD]
    rcases h : l[j]? with _ | a
    · simp
    · exact hl a (List.mem_of_getElem? h)) x
  exact h

@[expose] def fx (v w : Fin 64) : Fin 64 := ⟨v.val ^^^ w.val, Nat.xor_lt_two_pow (n := 6) v.2 w.2⟩

@[expose] def fx9 (x y : Fin 512) : Fin 512 :=
  ⟨x.val ^^^ y.val, Nat.xor_lt_two_pow (n := 9) x.2 y.2⟩

@[expose] def qF (u : Bool) (v : Fin 64) : Fin 512 := ⟨qOf u v, qOf_lt u v⟩

@[expose] def Gq (u : Bool) : Subgroup (Equiv.Perm (Fin 64)) where
  carrier := {σ | (∀ v w, σ (fx v w) = fx (σ v) (σ w)) ∧ ∃ τ : Equiv.Perm (Fin 512),
    (∀ x y, τ (fx9 x y) = fx9 (τ x) (τ y)) ∧ ∀ v, qF u (σ v) = τ (qF u v)}
  mul_mem' := by
    rintro σ σ' ⟨hσ, τ, hτ, hq⟩ ⟨hσ', τ', hτ', hq'⟩
    refine ⟨fun v w => ?_, τ * τ', fun x y => ?_, fun v => ?_⟩
    · simp only [Equiv.Perm.coe_mul, Function.comp_apply, hσ', hσ]
    · simp only [Equiv.Perm.coe_mul, Function.comp_apply, hτ', hτ]
    · simp only [Equiv.Perm.coe_mul, Function.comp_apply, hq, hq']
  one_mem' := ⟨fun _ _ => rfl, 1, fun _ _ => rfl, fun _ => rfl⟩
  inv_mem' := by
    rintro σ ⟨hσ, τ, hτ, hq⟩
    refine ⟨fun v w => ?_, τ⁻¹, fun x y => ?_, fun v => ?_⟩
    · apply σ.injective
      simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply, hσ]
    · apply τ.injective
      simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply, hτ]
    · apply τ.injective
      simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply, ← hq]

@[expose] def fn (σ : Equiv.Perm (Fin 64)) (v : ℕ) : ℕ := if h : v < 64 then (σ ⟨v, h⟩).val else 0

@[expose] def fn9 (τ : Equiv.Perm (Fin 512)) (x : ℕ) : ℕ :=
  if h : x < 512 then (τ ⟨x, h⟩).val else 0

@[expose] def tupleOf (σ : Equiv.Perm (Fin 64)) : List ℕ := (List.range 6).map fun j => fn σ (2 ^ j)

theorem fn_lt (σ : Equiv.Perm (Fin 64)) (v : ℕ) : fn σ v < 64 := by
  unfold fn; split
  · exact (σ _).2
  · norm_num

theorem fn9_lt (τ : Equiv.Perm (Fin 512)) (x : ℕ) : fn9 τ x < 512 := by
  unfold fn9; split
  · exact (τ _).2
  · norm_num

theorem fn_val (σ : Equiv.Perm (Fin 64)) (v : Fin 64) : fn σ v = (σ v).val := by
  unfold fn; rw [dite_eq_left v.2]

theorem fn9_val (τ : Equiv.Perm (Fin 512)) (x : Fin 512) : fn9 τ x = (τ x).val := by
  unfold fn9; rw [dite_eq_left x.2]

theorem fn_xor {σ : Equiv.Perm (Fin 64)} (hσ : ∀ v w, σ (fx v w) = fx (σ v) (σ w)) {v w : ℕ}
    (hv : v < 64) (hw : w < 64) : fn σ (v ^^^ w) = fn σ v ^^^ fn σ w := by
  have h := congrArg Fin.val (hσ ⟨v, hv⟩ ⟨w, hw⟩)
  unfold fn
  rw [dite_eq_left (Nat.xor_lt_two_pow (n := 6) hv hw), dite_eq_left hv, dite_eq_left hw]
  exact h

theorem fn9_xor {τ : Equiv.Perm (Fin 512)} (hτ : ∀ x y, τ (fx9 x y) = fx9 (τ x) (τ y)) {x y : ℕ}
    (hx : x < 512) (hy : y < 512) : fn9 τ (x ^^^ y) = fn9 τ x ^^^ fn9 τ y := by
  have h := congrArg Fin.val (hτ ⟨x, hx⟩ ⟨y, hy⟩)
  unfold fn9
  rw [dite_eq_left (Nat.xor_lt_two_pow (n := 9) hx hy), dite_eq_left hx, dite_eq_left hy]
  exact h

theorem map_zero_of_add {σ : Equiv.Perm (Fin 64)} (hσ : ∀ v w, σ (fx v w) = fx (σ v) (σ w)) :
    σ 0 = 0 := by
  have h := hσ 0 0
  have e : fx 0 0 = 0 := rfl
  rw [e] at h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [fx, Nat.xor_self] at this
  exact this

theorem fn_eq_zero {σ : Equiv.Perm (Fin 64)} (hσ : ∀ v w, σ (fx v w) = fx (σ v) (σ w)) {v : ℕ}
    (hv : v < 64) (h0 : fn σ v = 0) : v = 0 := by
  have h : σ ⟨v, hv⟩ = σ 0 := by
    rw [map_zero_of_add hσ]; apply Fin.ext; rw [← fn_val]; exact h0
  exact congrArg Fin.val (σ.injective h)

theorem evalV_tupleOf {σ : Equiv.Perm (Fin 64)} (hσ : ∀ v w, σ (fx v w) = fx (σ v) (σ w)) {v : ℕ}
    (hv : v < 64) : evalV (tupleOf σ) v = fn σ v := by
  rw [eq_xorBits (n := 6) (fun a b ha hb => fn_xor hσ ha hb) hv]
  unfold evalV
  refine xorBits_congr_bits fun j hj _ => ?_
  rw [List.getD_eq_getElem _ _ (by simpa [tupleOf] using hj)]
  simp [tupleOf]

theorem two_pow_lt_64 {j : ℕ} (hj : j ∈ List.range 6) : 2 ^ j < 64 :=
  calc 2 ^ j < 2 ^ 6 := Nat.pow_lt_pow_right Nat.one_lt_two (List.mem_range.1 hj)
    _ = 64 := by norm_num

theorem fn_mul (σ σ' : Equiv.Perm (Fin 64)) {v : ℕ} (hv : v < 64) :
    fn (σ * σ') v = fn σ (fn σ' v) := by
  have e : v = (⟨v, hv⟩ : Fin 64).val := rfl
  rw [e, fn_val, fn_val, fn_val]
  rfl

theorem tupleOf_mul {σ σ' : Equiv.Perm (Fin 64)} (hσ : ∀ v w, σ (fx v w) = fx (σ v) (σ w)) :
    tupleOf (σ * σ') = compT (tupleOf σ) (tupleOf σ') := by
  rw [compT]
  conv_lhs => rw [tupleOf]
  conv_rhs => rw [show tupleOf σ' = (List.range 6).map fun j => fn σ' (2 ^ j) from rfl,
    List.map_map]
  refine List.map_congr_left fun j hj => ?_
  simp only [Function.comp_apply]
  rw [fn_mul _ _ (two_pow_lt_64 hj), evalV_tupleOf hσ (fn_lt _ _)]

theorem tupleOf_injective {σ σ' : Equiv.Perm (Fin 64)} (hσ : ∀ v w, σ (fx v w) = fx (σ v) (σ w))
    (hσ' : ∀ v w, σ' (fx v w) = fx (σ' v) (σ' w)) (h : tupleOf σ = tupleOf σ') : σ = σ' :=
  Equiv.ext fun v => Fin.ext (by
    rw [← fn_val, ← fn_val, ← evalV_tupleOf hσ v.2, ← evalV_tupleOf hσ' v.2, h])

theorem tupleOf_mem_oqSearch {u : Bool} {σ : Equiv.Perm (Fin 64)} (hσ : σ ∈ Gq u) :
    tupleOf σ ∈ oqSearch u := by
  obtain ⟨hadd, τ, hτ, hq⟩ := hσ
  refine mem_oqSearch (A := fn σ) (B := fn9 τ) (fun v w hv hw => fn_xor hadd hv hw)
    (fun v _ => fn_lt σ v) (fun v hv h0 => fn_eq_zero hadd hv h0)
    (fun x y hx hy => fn9_xor hτ hx hy) fun v hv => ?_
  have h := congrArg Fin.val (hq ⟨v, hv⟩)
  rw [fn, dite_eq_left hv, fn9, dite_eq_left (qOf_lt u v)]
  exact h

theorem xorBits_two_pow_single {n j : ℕ} (f : ℕ → ℕ) (hj : j < n) : xorBits n f (2 ^ j) = f j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [xorBits_succ, Nat.testBit_two_pow]
    by_cases hjn : j = n
    · subst hjn
      have h0 : xorBits j f (2 ^ j) = 0 := by
        have key : ∀ m, m ≤ j → xorBits m f (2 ^ j) = 0 := by
          intro m hm
          induction m with
          | zero => rfl
          | succ m ihm =>
            rw [xorBits_succ, ihm (by omega), Nat.testBit_two_pow]
            simp [show j ≠ m by omega]
        exact key j le_rfl
      simp [h0]
    · rw [ih (by omega)]
      simp [hjn]

theorem evalV_two_pow {l : List ℕ} {j : ℕ} (hj : j < 6) : evalV l (2 ^ j) = l.getD j 0 :=
  xorBits_two_pow_single _ hj

theorem spanW_spec : ∀ u : Bool, ∀ k, k < 9 →
    ((spanW u).getD k (0, 0, 0)).1 < 64 ∧ ((spanW u).getD k (0, 0, 0)).2.1 < 64 ∧
    ((spanW u).getD k (0, 0, 0)).2.2 < 64 ∧
    qOf u ((spanW u).getD k (0, 0, 0)).1 ^^^ qOf u ((spanW u).getD k (0, 0, 0)).2.1 ^^^
      qOf u ((spanW u).getD k (0, 0, 0)).2.2 = 2 ^ k := by
  decide

theorem bOf_lt (u : Bool) (l : List ℕ) : ∀ a ∈ bOf u l, a < 512 := by
  intro a ha
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 ha
  exact Nat.xor_lt_two_pow (n := 9) (Nat.xor_lt_two_pow (qOf_lt u _) (qOf_lt u _)) (qOf_lt u _)

theorem evalE_surj {u : Bool} {B : List ℕ} (hq : ∀ w, w < 64 → ∃ x, x < 512 ∧ evalE B x = qOf u w)
    {y : ℕ} (hy : y < 512) : ∃ x, x < 512 ∧ evalE B x = y := by
  have hxor : ∀ y y', (∃ x, x < 512 ∧ evalE B x = y) → (∃ x, x < 512 ∧ evalE B x = y') →
      ∃ x, x < 512 ∧ evalE B x = y ^^^ y' := by
    rintro y y' ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩
    exact ⟨x ^^^ x', Nat.xor_lt_two_pow (n := 9) hx hx', evalE_xor B x x'⟩
  have hbasis : ∀ k, k < 9 → ∃ x, x < 512 ∧ evalE B x = 2 ^ k := by
    intro k hk
    obtain ⟨ha, hb, hc, he⟩ := spanW_spec u k hk
    rw [← he]
    exact hxor _ _ (hxor _ _ (hq _ ha) (hq _ hb)) (hq _ hc)
  have key : ∀ m, m ≤ 9 → ∃ x, x < 512 ∧ evalE B x = xorBits m (fun j => 2 ^ j) y := by
    intro m
    induction m with
    | zero => intro _; exact ⟨0, by norm_num, rfl⟩
    | succ m ih =>
      intro hm
      rw [xorBits_succ]
      refine hxor _ _ (ih (by omega)) ?_
      split
      · exact hbasis m (by omega)
      · exact ⟨0, by norm_num, rfl⟩
  obtain ⟨x, hx, he⟩ := key 9 le_rfl
  exact ⟨x, hx, he.trans (xorBits_two_pow_of_lt hy)⟩

theorem exists_of_validT {u : Bool} {l : List ℕ} (h : validT u l = true) :
    ∃ σ ∈ Gq u, tupleOf σ = l := by
  simp only [validT, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨hlen, hlt⟩, hinj⟩, hqB⟩ := h
  have hval : ∀ v, evalV l v < 64 := evalV_lt hlt
  let σf : Fin 64 → Fin 64 := fun v => ⟨evalV l v, hval v⟩
  have hσf : Function.Injective σf := by
    intro v w hvw
    have h1 : evalV l v = evalV l w := congrArg Fin.val hvw
    have h2 : evalV l (v.val ^^^ w.val) = 0 := by
      rw [evalV_xor, h1, Nat.xor_self]
    rcases hinj _ (Nat.xor_lt_two_pow (n := 6) v.2 w.2) with h3 | h3
    · exact Fin.ext (Nat.eq_of_xor_eq_zero h3)
    · exact absurd h2 h3
  let σ : Equiv.Perm (Fin 64) := Equiv.ofBijective σf (Finite.injective_iff_bijective.1 hσf)
  have hσv : ∀ v : Fin 64, (σ v).val = evalV l v := fun _ => rfl
  have hsurj : ∀ w, w < 64 → ∃ v, v < 64 ∧ evalV l v = w := by
    intro w hw
    obtain ⟨v, hv⟩ := σ.surjective ⟨w, hw⟩
    exact ⟨v.val, v.2, by rw [← hσv, hv]⟩
  let B := bOf u l
  have hBlt : ∀ x, evalE B x < 512 := evalE_lt (bOf_lt u l)
  let τf : Fin 512 → Fin 512 := fun x => ⟨evalE B x, hBlt x⟩
  have hτf : Function.Surjective τf := by
    intro y
    obtain ⟨x, hx, he⟩ := evalE_surj (u := u) (B := B) (fun w hw => by
      obtain ⟨v, hv, rfl⟩ := hsurj w hw
      exact ⟨qOf u v, qOf_lt u v, (hqB v hv).symm⟩) y.2
    exact ⟨⟨x, hx⟩, Fin.ext he⟩
  let τ : Equiv.Perm (Fin 512) := Equiv.ofBijective τf (Finite.surjective_iff_bijective.1 hτf)
  refine ⟨σ, ⟨fun v w => Fin.ext (evalV_xor l v w), τ, fun x y => Fin.ext (evalE_xor B x y),
    fun v => Fin.ext (hqB v v.2)⟩, ?_⟩
  apply List.ext_getElem
  · simp [tupleOf, hlen]
  · intro j hj _
    simp only [tupleOf, List.getElem_map, List.getElem_range]
    have hj6 : j < 6 := by simpa [tupleOf] using hj
    rw [fn, dite_eq_left (two_pow_lt_64 (List.mem_range.2 hj6)), hσv, evalV_two_pow hj6,
      List.getD_eq_getElem _ _ (by omega)]

theorem strictSorted_pairwise : ∀ l : List ℕ, strictSorted l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [strictSorted, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := strictSorted_pairwise (b :: l) h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact lt_trans h.1 (List.rel_of_pairwise_cons ih hc)

theorem head_oqStatesFrom (u : Bool) (t : ℕ) :
    ∀ m, ∀ st ∈ oqStatesFrom u t m, ∃ r, st.1 = t :: r := by
  intro m
  induction m with
  | zero =>
    intro st hst
    simp only [oqStatesFrom, List.range_zero, List.foldl_nil] at hst
    rcases h : addNew u [t] 0 [] with _ | rs
    · rw [h] at hst; simp at hst
    · rw [h] at hst
      simp only [Option.map_some, Option.toList_some, List.mem_singleton] at hst
      exact ⟨[], by rw [hst]⟩
  | succ m ih =>
    intro st hst
    rw [oqStatesFrom, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hst
    obtain ⟨st₀, hst₀, hst'⟩ := List.mem_flatMap.1 hst
    obtain ⟨r, hr⟩ := ih st₀ hst₀
    unfold oqStep at hst'
    obtain ⟨a, -, ha⟩ := List.mem_filterMap.1 hst'
    rcases h : addNew u (st₀.1 ++ [a]) (m + 1) st₀.2 with _ | rs
    · rw [h] at ha; simp at ha
    · rw [h] at ha
      simp only [Option.map_some, Option.some.injEq] at ha
      exact ⟨r ++ [a], by rw [← ha, hr]; rfl⟩

theorem head_oqFrom {u : Bool} {t : ℕ} {l : List ℕ} (hl : l ∈ oqFrom u t) : ∃ r, l = t :: r := by
  obtain ⟨st, hst, rfl⟩ := List.mem_map.1 hl
  exact head_oqStatesFrom u t 5 st hst

theorem head_tupleOf (σ : Equiv.Perm (Fin 64)) : (tupleOf σ).head? = some (fn σ 1) := by
  simp [tupleOf, List.range_succ_eq_map]

theorem fn_of_tupleOf {σ : Equiv.Perm (Fin 64)} {a : ℕ} {l : List ℕ} (h : tupleOf σ = a :: l) :
    fn σ 1 = a := by
  have h1 := head_tupleOf σ
  rw [h, List.head?_cons, Option.some.injEq] at h1
  exact h1.symm

theorem fn_one_eq {σ : Equiv.Perm (Fin 64)} {r : ℕ} (h : tupleOf σ = unpack6 r) :
    fn σ 1 = r % 64 := by
  have h1 := head_tupleOf σ
  rw [h] at h1
  simp [unpack6, List.range_succ_eq_map] at h1
  omega

theorem mem_oqFrom_fn {u : Bool} {σ : Equiv.Perm (Fin 64)} (hσ : σ ∈ Gq u) :
    tupleOf σ ∈ oqFrom u (fn σ 1) := by
  obtain ⟨t, -, ht⟩ := List.mem_flatMap.1 (tupleOf_mem_oqSearch hσ)
  obtain ⟨r, hr⟩ := head_oqFrom ht
  rw [fn_of_tupleOf hr]
  exact ht

theorem card_mem_list {α : Type} [DecidableEq α] {L : List α} (h : L.Nodup) :
    Nat.card {x // x ∈ L} = L.length := by
  rw [← List.toFinset_card_of_nodup h, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun l => List.mem_toFinset.symm)

theorem two_pow_lt_512 {k : ℕ} (hk : k < 9) : 2 ^ k < 512 :=
  calc 2 ^ k < 2 ^ 9 := Nat.pow_lt_pow_right Nat.one_lt_two hk
    _ = 512 := by norm_num

theorem evalE_two_pow {l : List ℕ} {j : ℕ} (hj : j < 9) : evalE l (2 ^ j) = l.getD j 0 :=
  xorBits_two_pow_single _ hj

theorem length_bOf (u : Bool) (l : List ℕ) : (bOf u l).length = 9 := by simp [bOf, spanW]

theorem fn9_mul (τ τ' : Equiv.Perm (Fin 512)) {x : ℕ} (hx : x < 512) :
    fn9 (τ * τ') x = fn9 τ (fn9 τ' x) := by
  have e : x = (⟨x, hx⟩ : Fin 512).val := rfl
  rw [e, fn9_val, fn9_val, fn9_val]
  rfl

theorem bOf_getD (u : Bool) (l : List ℕ) {k : ℕ} (hk : k < 9) :
    (bOf u l).getD k 0 = qOf u (evalV l ((spanW u).getD k (0, 0, 0)).1) ^^^
      qOf u (evalV l ((spanW u).getD k (0, 0, 0)).2.1) ^^^
        qOf u (evalV l ((spanW u).getD k (0, 0, 0)).2.2) := by
  have hk' : k < (spanW u).length := by simpa [spanW] using hk
  unfold bOf
  rw [List.getD_eq_getElem _ _ (by simpa using hk'), List.getElem_map,
    List.getD_eq_getElem _ _ hk']

theorem evalE_bOf {u : Bool} {σ : Equiv.Perm (Fin 64)} {τ : Equiv.Perm (Fin 512)}
    (hσ : ∀ v w, σ (fx v w) = fx (σ v) (σ w)) (hτ : ∀ x y, τ (fx9 x y) = fx9 (τ x) (τ y))
    (hq : ∀ v, qF u (σ v) = τ (qF u v)) {x : ℕ} (hx : x < 512) :
    evalE (bOf u (tupleOf σ)) x = fn9 τ x := by
  have hqn : ∀ v, v < 64 → qOf u (evalV (tupleOf σ) v) = fn9 τ (qOf u v) := fun v hv => by
    have h := congrArg Fin.val (hq ⟨v, hv⟩)
    rw [evalV_tupleOf hσ hv, fn, dite_eq_left hv, fn9, dite_eq_left (qOf_lt u v)]
    exact h
  have hb : ∀ k, k < 9 → evalE (bOf u (tupleOf σ)) (2 ^ k) = fn9 τ (2 ^ k) := by
    intro k hk
    obtain ⟨ha, hb, hc, he⟩ := spanW_spec u k hk
    rw [evalE_two_pow hk, bOf_getD u _ hk, hqn _ ha, hqn _ hb, hqn _ hc,
      ← fn9_xor hτ (qOf_lt u _) (qOf_lt u _),
      ← fn9_xor hτ (Nat.xor_lt_two_pow (n := 9) (qOf_lt u _) (qOf_lt u _)) (qOf_lt u _), he]
  rw [eq_xorBits (n := 9) (F := evalE (bOf u (tupleOf σ))) (fun a b _ _ => evalE_xor _ a b) hx,
    eq_xorBits (n := 9) (F := fn9 τ) (fun a b ha hb => fn9_xor hτ ha hb) hx]
  exact xorBits_congr_bits fun k hk _ => hb k hk

theorem validT_of_mem {u : Bool} {σ : Equiv.Perm (Fin 64)} (hσ : σ ∈ Gq u) :
    validT u (tupleOf σ) = true := by
  obtain ⟨hadd, τ, hτ, hq⟩ := hσ
  simp only [validT, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq]
  refine ⟨⟨⟨by simp [tupleOf], fun a ha => ?_⟩, fun v hv => ?_⟩, fun v hv => ?_⟩
  · obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
    exact fn_lt σ _
  · by_cases h0 : v = 0
    · exact Or.inl h0
    · refine Or.inr fun h => h0 (fn_eq_zero hadd hv ?_)
      rwa [evalV_tupleOf hadd hv] at h
  · rw [evalE_bOf hadd hτ hq (qOf_lt u v), evalV_tupleOf hadd hv]
    have h := congrArg Fin.val (hq ⟨v, hv⟩)
    rw [fn, dite_eq_left hv, fn9, dite_eq_left (qOf_lt u v)]
    exact h

theorem bOf_mul {u : Bool} {σ σ' : Equiv.Perm (Fin 64)} (hσ : σ ∈ Gq u) (hσ' : σ' ∈ Gq u) :
    bOf u (tupleOf (σ * σ')) = bMul (bOf u (tupleOf σ)) (bOf u (tupleOf σ')) := by
  obtain ⟨hadd, τ, hτ, hq⟩ := hσ
  obtain ⟨hadd', τ', hτ', hq'⟩ := hσ'
  have hadd2 : ∀ v w, (σ * σ') (fx v w) = fx ((σ * σ') v) ((σ * σ') w) := fun v w => by
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, hadd', hadd]
  have hτ2 : ∀ x y, (τ * τ') (fx9 x y) = fx9 ((τ * τ') x) ((τ * τ') y) := fun x y => by
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, hτ', hτ]
  have hq2 : ∀ v, qF u ((σ * σ') v) = (τ * τ') (qF u v) := fun v => by
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, hq, hq']
  apply List.ext_getElem
  · rw [bMul, List.length_map, length_bOf, length_bOf]
  · intro k hk _
    have hk9 : k < 9 := by rwa [length_bOf] at hk
    have e1 := evalE_bOf hadd2 hτ2 hq2 (two_pow_lt_512 hk9)
    rw [evalE_two_pow hk9, List.getD_eq_getElem _ _ hk] at e1
    have e2 := evalE_bOf hadd' hτ' hq' (two_pow_lt_512 hk9)
    rw [evalE_two_pow hk9, List.getD_eq_getElem _ _ (by rw [length_bOf]; exact hk9)] at e2
    simp only [bMul, List.getElem_map]
    rw [e1, e2, evalE_bOf hadd hτ hq (fn9_lt _ _), fn9_mul _ _ (two_pow_lt_512 hk9)]

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
