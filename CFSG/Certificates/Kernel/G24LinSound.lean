module

public import Certificates.Data.Kernel.G24LinK
public import Certificates.Data.G24LinEq

public section

namespace CFSG.KC.G24Lin

open CFSG.KD.G24Lin CFSG.Quasithin.St84.G24LE Matrix

@[expose] def bz (x i : ℕ) : ZMod 2 := if bitK x i then 1 else 0

theorem bitK_eq (x i : ℕ) : bitK x i = x.testBit i := by
  have h : Nat.land (Nat.shiftRight x i) 1 = x / 2 ^ i % 2 := by
    change (x >>> i) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  unfold bitK
  rw [h, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with e | e <;> rw [e] <;> rfl

theorem bz_xor (a b i : ℕ) : bz (Nat.xor a b) i = bz a i + bz b i := by
  unfold bz
  rw [bitK_eq, bitK_eq, bitK_eq]
  change (if (a ^^^ b).testBit i then _ else _) = _
  rw [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> decide

theorem bz_zero (i : ℕ) : bz 0 i = 0 := by
  unfold bz
  rw [bitK_eq, Nat.zero_testBit]
  rfl

theorem bz_two_pow (a b : ℕ) : bz (Nat.shiftLeft 1 a) b = if a = b then 1 else 0 := by
  unfold bz
  rw [bitK_eq]
  change (if (1 <<< a).testBit b then _ else _) = _
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : a = b
  · rw [if_pos h, decide_eq_true h]
    rfl
  · rw [if_neg h, decide_eq_false h]
    rfl

theorem xorK_succ (x : ℕ) (F : ℕ → ℕ) (n : ℕ) :
    xorK x F (n + 1) = cond (bitK x n) (Nat.xor (xorK x F n) (F n)) (xorK x F n) := rfl

theorem sum_bz_xorK (x : ℕ) (F : ℕ → ℕ) (i n : ℕ) :
    ∑ j : Fin n, bz x j * bz (F j) i = bz (xorK x F n) i := by
  induction n with
  | zero =>
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact (bz_zero i).symm
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih, xorK_succ]
    cases h : bitK x n
    · have h0 : bz x n = 0 := by
        unfold bz
        rw [h]
        rfl
      rw [h0, zero_mul, add_zero]
      rfl
    · have h1 : bz x n = 1 := by
        unfold bz
        rw [h]
        rfl
      rw [h1, one_mul, cond_true, bz_xor]

theorem mul_bz {I C J : Type*} [Fintype C] {n : ℕ} (e : C ≃ Fin n) (A : Matrix I C (ZMod 2))
    (B : Matrix C J (ZMod 2)) (a : I → ℕ) (F : ℕ → ℕ) (kj : J → ℕ)
    (hA : ∀ i c, A i c = bz (a i) (e c)) (hB : ∀ c j, B c j = bz (F (e c)) (kj j)) (i : I) (j : J) :
    (A * B) i j = bz (xorK (a i) F n) (kj j) := by
  rw [Matrix.mul_apply, ← sum_bz_xorK]
  exact Fintype.sum_equiv e _ _ fun c => by rw [hA, hB]

theorem mulVec_bz {n : ℕ} {I : Type*} (A : Matrix I (Fin n) (ZMod 2)) (col : ℕ → ℕ) (ki : I → ℕ)
    (hA : ∀ i j, A i j = bz (col j) (ki i)) (T : ℕ) (i : I) :
    (A *ᵥ fun j => bz T j) i = bz (xorK T col n) (ki i) := by
  rw [Matrix.mulVec, dotProduct, ← sum_bz_xorK]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hA, mul_comm]

theorem natRec_all (f : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true (fun a acc => acc && f a) n = true → ∀ a < n, f a = true
  | 0, _ => fun a ha => absurd ha (Nat.not_lt_zero a)
  | n + 1, h => by
    have h' : (Nat.rec (motive := fun _ => Bool) true (fun a acc => acc && f a) n && f n) = true := h
    rw [Bool.and_eq_true] at h'
    intro a ha
    rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
    · exact natRec_all f n h'.1 a ha
    · exact h'.2

theorem spanK_spec {D : ℕ → ℕ} {np nc nr : ℕ} (h : spanK D np nc nr = true) :
    ∀ a < nc, Nat.xor (xorK (D (np + nc + a)) (fun r => D (np + (nc + nc) + r)) nr)
      (xorK (D (np + a)) D np) = Nat.shiftLeft 1 a := by
  intro a ha
  exact Nat.beq_eq.mp (natRec_all _ nc h a ha)

theorem spanOK_of {R C K : Type*} [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C]
    [Fintype K] [DecidableEq K] {m t : Matrix R C (ZMod 2)} {k : Matrix C K (ZMod 2)}
    {p : Matrix K C (ZMod 2)} {y : Matrix C R (ZMod 2)} {np nc nr : ℕ} (eR : R ≃ Fin nr)
    (eC : C ≃ Fin nc) (eK : K ≃ Fin np) (D : ℕ → ℕ) (ht : t = m)
    (hm : ∀ r u, m r u = bz (D (np + (nc + nc) + eR r)) (eC u))
    (hk : ∀ c κ, k c κ = bz (D (np + eC c)) (eK κ))
    (hp : ∀ κ c, p κ c = bz (D (eK κ)) (eC c))
    (hy : ∀ c r, y c r = bz (D (np + nc + eC c)) (eR r))
    (hs : spanK D np nc nr = true) : spanOK m t k p y = true := by
  unfold spanOK
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  refine ⟨ht, ?_⟩
  rw [ht]
  ext a b
  rw [Matrix.add_apply,
    mul_bz eK k p (fun c => D (np + eC c)) D (fun c => eC c) hk (fun κ c => hp κ c) a b,
    mul_bz eR y m (fun c => D (np + nc + eC c)) (fun r => D (np + (nc + nc) + r)) (fun c => eC c)
      hy (fun r u => hm r u) a b,
    add_comm, ← bz_xor, spanK_spec hs _ (eC a).isLt, bz_two_pow, Matrix.one_apply]
  by_cases h : a = b
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg fun e => h (eC.injective (Fin.ext e))]

@[expose] noncomputable def eqvOf {α : Type*} [Fintype α] (L : List α) (key : α → ℕ)
    (hL : ∀ x, L[key x]? = some x) (hc : Fintype.card α = L.length) : α ≃ Fin L.length :=
  Equiv.ofBijective (fun x => ⟨key x, (List.getElem?_eq_some_iff.1 (hL x)).1⟩) <| by
    have hi : Function.Injective (fun x => (⟨key x, (List.getElem?_eq_some_iff.1 (hL x)).1⟩ :
        Fin L.length)) := by
      intro x y e
      have e' : key x = key y := congrArg Fin.val e
      have := hL x
      rw [e', hL y] at this
      exact (Option.some.inj this).symm
    exact (Fintype.bijective_iff_injective_and_card _).2 ⟨hi, by rw [hc, Fintype.card_fin]⟩

theorem foldl_push_toList {R β : Type*} (g : R → β) :
    ∀ (rows : List R) (A : Array β),
      (rows.foldl (fun A r => A.push (g r)) A).toList = A.toList ++ rows.map g
  | [], A => by simp
  | r :: rs, A => by
    rw [List.foldl_cons, foldl_push_toList g rs, Array.toList_push, List.map_cons,
      List.append_assoc, List.singleton_append]

theorem getD_toList {β : Type*} (A : Array β) (i : ℕ) (d : β) : A.getD i d = A.toList.getD i d := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

theorem ent_tab {R C : Type*} (rows : List R) (cols : List C) (f : R → C → ZMod 2)
    (kr : R → ℕ) (kc : C → ℕ) (hr : ∀ r, rows[kr r]? = some r) (hc : ∀ u, cols[kc u]? = some u) :
    ent (tab rows cols f) kr kc = Matrix.of f := by
  ext r u
  have e : (tab rows cols f).toList = rows.map fun r => (cols.map fun c => f r c).toArray := by
    unfold tab
    rw [foldl_push_toList (fun r => (cols.map fun c => f r c).toArray)]
    rfl
  have e2 : (tab rows cols f)[kr r]? = some (cols.map fun c => f r c).toArray := by
    rw [← Array.getElem?_toList, e, List.getElem?_map, hr r]
    rfl
  unfold ent
  simp [e2, hc u]

theorem packC_cons (c : Char) (l : List Char) :
    packC (c :: l) = cond (Nat.beq c.toNat 49) 1 0 + 2 * packC l := rfl

theorem bitK_packC : ∀ (l : List Char) (j : ℕ),
    bitK (packC l) j = (l.getD j ' ' == '1')
  | [], j => by
    rw [bitK_eq]
    change Nat.testBit 0 j = _
    rw [Nat.zero_testBit]
    rfl
  | c :: l, 0 => by
    rw [bitK_eq, packC_cons, Nat.testBit_zero, List.getD_cons_zero]
    cases e : Nat.beq c.toNat 49
    · have h : c ≠ '1' := fun h => by
        rw [h] at e
        exact absurd e (by decide)
      rw [beq_eq_false_iff_ne.2 h]
      simp
    · have h : c = '1' := by
        rw [← Char.ofNat_toNat c, Nat.eq_of_beq_eq_true e]
      rw [h]
      simp
  | c :: l, j + 1 => by
    rw [bitK_eq, packC_cons, Nat.testBit_succ, List.getD_cons_succ, ← bitK_packC l j, bitK_eq]
    congr 1
    cases Nat.beq c.toNat 49 <;> simp <;> omega

end CFSG.KC.G24Lin

end
