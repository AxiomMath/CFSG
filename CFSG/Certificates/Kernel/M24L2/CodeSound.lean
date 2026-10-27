module

public import Certificates.Data.Kernel.M24L2.Letters

public section

namespace CFSG.KC.M24L2

open CFSG.KC.Loop CFSG.Sporadic.Th.Native CFSG.CGT.M24R

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem all_mem_congr {α : Type} : ∀ {l : List α} {f g : α → Bool}, (∀ a ∈ l, f a = g a) →
    l.all f = l.all g
  | [], _, _, _ => rfl
  | a :: l, f, g, h => by
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      all_mem_congr fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem any_mem_congr {α : Type} : ∀ {l : List α} {f g : α → Bool}, (∀ a ∈ l, f a = g a) →
    l.any f = l.any g
  | [], _, _, _ => rfl
  | a :: l, f, g, h => by
    rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
      any_mem_congr fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem foldL_eq {α β : Type} (f : β → α → β) : ∀ (L : List α) (s : β), foldL f L s = L.foldl f s
  | [], _ => rfl
  | a :: L, s => by
    change foldL f L (f s a) = _
    rw [foldL_eq f L, List.foldl_cons]

theorem allL_eq {α : Type} (p : α → Bool) : ∀ L : List α, allL p L = L.all p
  | [] => rfl
  | a :: L => by
    change bAnd(p a, allL p L) = _
    rw [allL_eq p L, List.all_cons]
    cases p a <;> rfl

theorem anyL_eq {α : Type} (p : α → Bool) : ∀ L : List α, anyL p L = L.any p
  | [] => rfl
  | a :: L => by
    change bIf(p a, true, anyL p L) = _
    rw [anyL_eq p L, List.any_cons]
    cases p a <;> rfl

theorem nib_eq (m k : Nat) : nib m k = m / 2 ^ (4 * k) % 16 := by
  unfold nib
  change (m >>> (k <<< 2)) &&& (2 ^ 4 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  congr 3
  omega

theorem nib_lt (m k : Nat) : nib m k < 16 := by
  rw [nib_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem bitM_eq (x j y : Nat) : bitM x j y = if x.testBit j then y else 0 := by
  unfold bitM
  change ((x >>> j) &&& 1) * y = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ j) with h | h <;> simp [h]

theorem ite_lt16 {b : Bool} {n : Nat} (h : n < 16) : (if b then n else 0) < 16 := by
  cases b <;> simp [h]

theorem xor_lt16 {a b : Nat} (ha : a < 16) (hb : b < 16) : a ^^^ b < 16 :=
  Nat.xor_lt_two_pow (n := 4) ha hb

theorem lap_eq (m x : Nat) : lap m x =
    ((if x.testBit 0 then nib m 0 else 0) ^^^ (if x.testBit 1 then nib m 1 else 0)) ^^^
      ((if x.testBit 2 then nib m 2 else 0) ^^^ (if x.testBit 3 then nib m 3 else 0)) := by
  unfold lap
  simp only [bitM_eq]
  rfl

theorem lap_lt (m x : Nat) : lap m x < 16 := by
  rw [lap_eq]
  exact xor_lt16 (xor_lt16 (ite_lt16 (nib_lt _ _)) (ite_lt16 (nib_lt _ _)))
    (xor_lt16 (ite_lt16 (nib_lt _ _)) (ite_lt16 (nib_lt _ _)))

theorem xor4 (a b c d : Nat) : (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  rw [Nat.xor_assoc a b, ← Nat.xor_assoc b c d, Nat.xor_comm b c, Nat.xor_assoc c b d,
    ← Nat.xor_assoc a c]

theorem ite_xor (a b : Bool) (n : Nat) :
    (if (a ^^ b) = true then n else 0) = (if a = true then n else 0) ^^^ (if b = true then n else 0) := by
  cases a <;> cases b <;> simp

theorem lap_xor (m x y : Nat) : lap m (x ^^^ y) = lap m x ^^^ lap m y := by
  simp only [lap_eq, Nat.testBit_xor, ite_xor]
  generalize (if x.testBit 0 = true then nib m 0 else 0) = a0
  generalize (if x.testBit 1 = true then nib m 1 else 0) = a1
  generalize (if x.testBit 2 = true then nib m 2 else 0) = a2
  generalize (if x.testBit 3 = true then nib m 3 else 0) = a3
  generalize (if y.testBit 0 = true then nib m 0 else 0) = b0
  generalize (if y.testBit 1 = true then nib m 1 else 0) = b1
  generalize (if y.testBit 2 = true then nib m 2 else 0) = b2
  generalize (if y.testBit 3 = true then nib m 3 else 0) = b3
  rw [xor4 a0 b0 a1 b1, xor4 a2 b2 a3 b3, xor4 (a0 ^^^ a1)]

theorem lap_zero (m : Nat) : lap m 0 = 0 := by
  simp [lap_eq]

theorem lap_ite (m n : Nat) (b : Bool) :
    lap m (if b then n else 0) = if b then lap m n else 0 := by
  cases b <;> simp [lap_zero]

theorem lap_lap (ma mb x : Nat) : lap ma (lap mb x) =
    ((if x.testBit 0 then lap ma (nib mb 0) else 0) ^^^ (if x.testBit 1 then lap ma (nib mb 1) else 0)) ^^^
      ((if x.testBit 2 then lap ma (nib mb 2) else 0) ^^^
        (if x.testBit 3 then lap ma (nib mb 3) else 0)) := by
  rw [lap_eq mb, lap_xor, lap_xor, lap_xor, lap_ite, lap_ite, lap_ite, lap_ite]

theorem aff_eq (c x : Nat) : aff c x = c % 16 ^^^ lap (c / 16) x := by
  unfold aff
  change c &&& (2 ^ 4 - 1) ^^^ lap (c >>> 4) x = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem aff_lt (c x : Nat) : aff c x < 16 := by
  rw [aff_eq]
  exact xor_lt16 (Nat.mod_lt _ (by norm_num)) (lap_lt _ _)

theorem lor_shl4 {a b : Nat} (ha : a < 16) : Nat.lor a (Nat.shiftLeft b 4) = a + 16 * b := by
  change a ||| b <<< 4 = _
  rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt (i := 4) ha, Nat.shiftLeft_eq]
  omega

theorem fldT_eq (T y : Nat) : fldT T y = T / 16 ^ y % 16 := by
  unfold fldT
  change (T >>> (y <<< 2)) &&& (2 ^ 4 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    show (2 : Nat) ^ (y * 2 ^ 2) = 16 ^ y by rw [pow_mul']; norm_num]

theorem packN_cons (v : Nat) (l : List Nat) :
    packN (v :: l) = Nat.lor v (Nat.shiftLeft (packN l) 4) := rfl

theorem fldT_packN : ∀ (l : List Nat), (∀ v ∈ l, v < 16) → ∀ y < l.length,
    fldT (packN l) y = l[y]!
  | [], _, y, hy => absurd hy (by simp)
  | v :: l, hl, y, hy => by
    have hv := hl v List.mem_cons_self
    rw [packN_cons, lor_shl4 hv, fldT_eq]
    cases y with
    | zero =>
      simp only [pow_zero, Nat.div_one, List.getElem!_cons_zero]
      omega
    | succ y =>
      rw [pow_succ', ← Nat.div_div_eq_div_mul, show (v + 16 * packN l) / 16 = packN l by omega,
        ← fldT_eq, fldT_packN l (fun v' hv' => hl v' (List.mem_cons_of_mem _ hv')) y
          (by simp at hy; omega), List.getElem!_cons_succ]

theorem xor_eq' (a b : Nat) : Nat.xor a b = a ^^^ b := rfl

theorem lapT_fld (m : Nat) : ∀ y < 16, fldT (lapT m) y = lap m y := by
  intro y hy
  unfold lapT
  simp only [strictN_eq]
  have h0 := nib_lt m 0
  have h1 := nib_lt m 1
  have h2 := nib_lt m 2
  have h3 := nib_lt m 3
  rw [fldT_packN _ (by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> (try simp only [xor_eq']) <;>
      repeat (first | apply xor_lt16 | assumption | norm_num)) y (by simp; omega)]
  interval_cases y <;> simp [lap_eq, Nat.testBit_eq_decide_div_mod_eq, xor_eq']

theorem mulC_eq (a b : Nat) : mulC a b = aff a (b % 16) + 16 * (lap (a / 16) (nib (b / 16) 0) +
    16 * (lap (a / 16) (nib (b / 16) 1) + 16 * (lap (a / 16) (nib (b / 16) 2) +
      16 * lap (a / 16) (nib (b / 16) 3)))) := by
  unfold mulC
  have hb : Nat.land b 15 < 16 := by
    change b &&& (2 ^ 4 - 1) < 16
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by norm_num)
  rw [strictN_eq, strictN_eq, lapT_fld _ _ (nib_lt _ 0), lapT_fld _ _ (nib_lt _ 1),
    lapT_fld _ _ (nib_lt _ 2), lapT_fld _ _ (nib_lt _ 3), lapT_fld _ _ hb]
  rw [lor_shl4 (lap_lt _ _), lor_shl4 (lap_lt _ _), lor_shl4 (lap_lt _ _)]
  have hv : Nat.xor (Nat.land a 15) (lap (Nat.shiftRight a 4) (Nat.land b 15)) = aff a (b % 16) := by
    rw [aff_eq]
    change a &&& (2 ^ 4 - 1) ^^^ lap (a >>> 4) (b &&& (2 ^ 4 - 1)) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  have h16 : ∀ x : Nat, Nat.shiftRight x 4 = x / 16 := fun x => Nat.shiftRight_eq_div_pow x 4
  rw [hv, lor_shl4 (aff_lt _ _), h16 a, h16 b]

theorem mulC_lt (a b : Nat) : mulC a b < 2 ^ 20 := by
  rw [mulC_eq]
  have := aff_lt a (b % 16)
  have := lap_lt (a / 16) (nib (b / 16) 0)
  have := lap_lt (a / 16) (nib (b / 16) 1)
  have := lap_lt (a / 16) (nib (b / 16) 2)
  have := lap_lt (a / 16) (nib (b / 16) 3)
  omega

theorem nib_pack {c0 c1 c2 c3 : Nat} (h0 : c0 < 16) (h1 : c1 < 16) (h2 : c2 < 16)
    (h3 : c3 < 16) : nib (c0 + 16 * (c1 + 16 * (c2 + 16 * c3))) 0 = c0 ∧
      nib (c0 + 16 * (c1 + 16 * (c2 + 16 * c3))) 1 = c1 ∧
      nib (c0 + 16 * (c1 + 16 * (c2 + 16 * c3))) 2 = c2 ∧
      nib (c0 + 16 * (c1 + 16 * (c2 + 16 * c3))) 3 = c3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [nib_eq] <;> norm_num <;> omega

theorem aff_mulC (a b x : Nat) : aff (mulC a b) x = aff a (aff b x) := by
  have h1 := aff_lt a (b % 16)
  obtain ⟨e0, e1, e2, e3⟩ := nib_pack (lap_lt (a / 16) (nib (b / 16) 0))
    (lap_lt (a / 16) (nib (b / 16) 1)) (lap_lt (a / 16) (nib (b / 16) 2))
    (lap_lt (a / 16) (nib (b / 16) 3))
  generalize hC : lap (a / 16) (nib (b / 16) 0) + 16 * (lap (a / 16) (nib (b / 16) 1) +
    16 * (lap (a / 16) (nib (b / 16) 2) + 16 * lap (a / 16) (nib (b / 16) 3))) = C at e0 e1 e2 e3
  rw [aff_eq (mulC a b), mulC_eq, hC, show (aff a (b % 16) + 16 * C) % 16 = aff a (b % 16) by omega,
    show (aff a (b % 16) + 16 * C) / 16 = C by omega, lap_eq C, e0, e1, e2, e3, ← lap_lap,
    aff_eq a (b % 16)]
  conv_rhs => rw [aff_eq b x, aff_eq a]
  rw [lap_xor, Nat.xor_assoc]

theorem lap_basis (m : Nat) : lap m 1 = nib m 0 ∧ lap m 2 = nib m 1 ∧ lap m 4 = nib m 2 ∧
    lap m 8 = nib m 3 := by
  simp [lap_eq, Nat.testBit_eq_decide_div_mod_eq]

theorem codeF_eq (f : Nat → Nat) : codeF f = f 0 + 16 * ((f 1 ^^^ f 0) + 16 * ((f 2 ^^^ f 0) +
    16 * ((f 4 ^^^ f 0) + 16 * (f 8 ^^^ f 0)))) := rfl

theorem codeF_aff {c : Nat} (hc : c < 2 ^ 20) : codeF (aff c) = c := by
  obtain ⟨b1, b2, b4, b8⟩ := lap_basis (c / 16)
  have hx : ∀ v n : Nat, (v ^^^ n) ^^^ v = n := fun v n => by
    rw [Nat.xor_comm, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rw [codeF_eq]
  simp only [aff_eq, lap_zero, Nat.xor_zero, b1, b2, b4, b8, hx, nib_eq]
  norm_num
  omega

theorem aff_idC {x : Nat} (hx : x < 16) : aff idC x = x := by
  have h : ∀ x < 16, aff idC x = x := by decide +kernel
  exact h x hx

@[expose] noncomputable def tabC (c : Nat) : Table := Array.ofFn (n := 16) fun p => UInt32.ofNat (aff c p.val)

theorem tabC_size (c : Nat) : (tabC c).size = 16 := Array.size_ofFn

theorem getElem!_tabC (c : Nat) {p : Nat} (hp : p < 16) :
    (tabC c)[p]! = UInt32.ofNat (aff c p) := by
  rw [getElem!_pos (tabC c) p (by rw [tabC_size]; exact hp)]
  simp only [tabC, Array.getElem_ofFn]

theorem toNat_aff (c x : Nat) : (UInt32.ofNat (aff c x)).toNat = aff c x := by
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (lt_trans (aff_lt c x) (by norm_num))]

theorem ap_tabC (c : Nat) {p : Nat} (hp : p < 16) : ap (tabC c) p = aff c p := by
  unfold ap
  rw [getElem!_tabC c hp, toNat_aff]

theorem compT_tabC (a b : Nat) : compT 16 (tabC a) (tabC b) = tabC (mulC a b) := by
  apply Array.ext
  · simp [compT, tabC]
  · intro i h1 h2
    have hi : i < 16 := by simpa [compT] using h1
    simp only [compT, Array.getElem_ofFn]
    rw [getElem!_tabC b hi, toNat_aff, getElem!_tabC a (aff_lt b i)]
    simp only [tabC, Array.getElem_ofFn, aff_mulC]

theorem eq_tabC {X : Table} {c : Nat} (hs : X.size = 16) (h : ∀ p < 16, ap X p = aff c p) :
    X = tabC c := by
  apply Array.ext (by rw [hs, tabC_size])
  intro i h1 h2
  have hi : i < 16 := by rwa [hs] at h1
  have e := h i hi
  unfold ap at e
  rw [getElem!_pos X i h1] at e
  rw [← getElem!_pos (tabC c) i h2, getElem!_tabC c hi]
  apply UInt32.toNat_inj.1
  rw [e, toNat_aff]

theorem codeOf_tabC {c : Nat} (hc : c < 2 ^ 20) : codeOf (tabC c) = c := by
  have h : codeOf (tabC c) = codeF (aff c) := by
    simp only [codeOf, ap_tabC c (by norm_num : 0 < 16), ap_tabC c (by norm_num : 1 < 16),
      ap_tabC c (by norm_num : 2 < 16), ap_tabC c (by norm_num : 4 < 16),
      ap_tabC c (by norm_num : 8 < 16)]
    rfl
  rw [h, codeF_aff hc]

theorem tabC_inj {a b : Nat} (ha : a < 2 ^ 20) (hb : b < 2 ^ 20) (h : tabC a = tabC b) : a = b := by
  rw [← codeOf_tabC ha, ← codeOf_tabC hb, h]

theorem beq_tabC {a b : Nat} (ha : a < 2 ^ 20) (hb : b < 2 ^ 20) :
    (tabC a == tabC b) = Nat.beq a b := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]
  exact ⟨tabC_inj ha hb, fun h => h ▸ rfl⟩

theorem idT_tabC : idT 16 = tabC idC := by
  refine eq_tabC (by simp [idT]) fun p hp => ?_
  rw [aff_idC hp]
  unfold ap idT
  rw [getElem!_pos _ p (by simpa using hp), Array.getElem_ofFn, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (by omega)]

theorem letTab_size (l : Fin 10 × Bool) : (letTab l).size = 16 := by
  obtain ⟨j, b⟩ := l
  have h1 : gTc[j.val]! = gT j := by
    unfold gTc
    rw [getElem!_pos _ j.val (by simp), Array.getElem_ofFn]
  have h2 : gTic[j.val]! = gTi j := by
    unfold gTic
    rw [getElem!_pos _ j.val (by simp), Array.getElem_ofFn]
  cases b
  · simp only [letTab, Bool.false_eq_true, ↓reduceIte, h2, gTi, Array.size_ofFn]
  · simp only [letTab, ↓reduceIte, h1, gT, Array.size_ofFn]

theorem letTab_aff : ∀ j : Fin 10, ∀ b : Bool, ∀ p : Fin 16,
    ap (letTab (j, b)) p.val = aff (lcC (j, b)) p.val := by
  decide +kernel

theorem letTab_tabC (l : Fin 10 × Bool) : letTab l = tabC (lcC l) :=
  eq_tabC (letTab_size l) fun p hp => letTab_aff l.1 l.2 ⟨p, hp⟩

theorem foldl_tabC (w : List (Fin 10 × Bool)) : ∀ c : Nat,
    w.foldl (fun X l => compT 16 X (letTab l)) (tabC c) =
      tabC (w.foldl (fun c l => mulC c (lcC l)) c) := by
  induction w with
  | nil => intro c; rfl
  | cons l w ih =>
    intro c
    rw [List.foldl_cons, List.foldl_cons, letTab_tabC, compT_tabC, ih]

theorem cwK_eq (w : List (Fin 10 × Bool)) : cwK w = w.foldl (fun c l => mulC c (lcC l)) idC :=
  foldL_eq _ _ _

theorem wTab_tabC (w : List (Fin 10 × Bool)) : wTab w = tabC (cwK w) := by
  unfold wTab
  rw [cwK_eq, idT_tabC, foldl_tabC]

theorem foldl_mulC_lt {α : Type} (g : α → Nat) (w : List α) :
    ∀ c, c < 2 ^ 20 → w.foldl (fun c l => mulC c (g l)) c < 2 ^ 20 := by
  induction w with
  | nil => intro c hc; exact hc
  | cons l w ih => intro c _; exact ih _ (mulC_lt _ _)

theorem cwK_lt (w : List (Fin 10 × Bool)) : cwK w < 2 ^ 20 := by
  rw [cwK_eq]
  exact foldl_mulC_lt _ w _ (by decide)

end CFSG.KC.M24L2
