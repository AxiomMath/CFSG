module

public import Certificates.Data.Kernel.EvenSporDS81.ExtDefs

public section

namespace CFSG.KC.EvenSporDS81

@[expose] def digsK (k : Nat) : List Nat := (List.range 10).map (colK k)

@[expose] def bitsD (ds : List Nat) (i : Nat) : Nat :=
  ds.foldr (fun d acc => (if d.testBit i then 1 else 0) + 1024 * acc) 0

@[expose] def trK (k : Nat) : List Nat := (List.range 10).map (bitsD (digsK k))

@[expose] def mulT : List Nat → List Nat → Nat
  | a :: as, s :: ss => a * s ^^^ mulT as ss
  | _, _ => 0

inductive KTree (α : Type) where
  | leaf : KTree α
  | node : KTree α → Nat → α → KTree α → KTree α

@[expose] def KTree.ins {α : Type} (k : Nat) (v : α) : KTree α → KTree α
  | .leaf => .node .leaf k v .leaf
  | .node l k' v' r =>
    if k < k' then .node (l.ins k v) k' v' r
    else if k' < k then .node l k' v' (r.ins k v) else .node l k' v' r

@[expose] def KTree.find {α : Type} (x : Nat) : KTree α → Option α
  | .leaf => none
  | .node l k v r => if x < k then l.find x else if k < x then r.find x else some v

@[expose] def KTree.toList {α : Type} : KTree α → List (Nat × α)
  | .leaf => []
  | .node l k v r => l.toList ++ (k, v) :: r.toList

@[expose] def insAll : KTree Nat → Nat → List Nat → KTree Nat
  | t, _, [] => t
  | t, i, k :: ks => insAll (t.ins k i) (i + 1) ks

@[expose] def idxTree (K : List Nat) : KTree Nat := insAll .leaf 0 K

@[expose] def treeOK (K : List Nat) (t : KTree Nat) : Bool :=
  t.toList.all fun p => K.idxOf p.1 == p.2

@[expose] def idxF (K : List Nat) (t : KTree Nat) (x : Nat) : Nat := (t.find x).getD (K.idxOf x)

@[expose] def tabG (K : List Nat) (t : KTree Nat) (KT : List (List Nat)) : List (List Nat) :=
  K.map fun a => KT.map fun s => idxF K t (mulT (digsK a) s)

@[expose] def tabF (K : List Nat) (t : KTree Nat) : List (List Nat) := tabG K t (K.map trK)

@[expose] def horL (l : List Nat) (d : Nat → Nat) : Nat := l.foldr (fun j acc => d j + 1024 * acc) 0

theorem colK_lt (k i : Nat) : colK k i < 1024 := by
  induction i generalizing k with
  | zero => simp only [colK]; omega
  | succ i ih => simp only [colK]; exact ih _

theorem xor_digit {x y x' y' : Nat} (hx : x < 1024) (hx' : x' < 1024) :
    (x + 1024 * y) ^^^ (x' + 1024 * y') = (x ^^^ x') + 1024 * (y ^^^ y') := by
  have h2 : (1024 : Nat) = 2 ^ 10 := rfl
  have h1 : x < 2 ^ 10 := by omega
  have h1' : x' < 2 ^ 10 := by omega
  have hxx : x ^^^ x' < 2 ^ 10 := Nat.xor_lt_two_pow h1 h1'
  apply Nat.eq_of_testBit_eq
  intro i
  rw [h2, Nat.add_comm x, Nat.add_comm x', Nat.add_comm (x ^^^ x'), Nat.testBit_xor]
  simp only [Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h1',
    Nat.testBit_two_pow_mul_add _ hxx, Nat.testBit_xor]
  split <;> rfl

theorem horL_xor (l : List Nat) {d e : Nat → Nat} (hd : ∀ j ∈ l, d j < 1024)
    (he : ∀ j ∈ l, e j < 1024) : horL l d ^^^ horL l e = horL l (fun j => d j ^^^ e j) := by
  induction l with
  | nil => simp [horL]
  | cons j l ih =>
    simp only [horL, List.foldr_cons] at ih ⊢
    rw [xor_digit (hd j List.mem_cons_self) (he j List.mem_cons_self),
      ih (fun i hi => hd i (List.mem_cons_of_mem _ hi)) (fun i hi => he i (List.mem_cons_of_mem _ hi))]

theorem horL_mul (l : List Nat) (c : Nat) (d : Nat → Nat) :
    c * horL l d = horL l (fun j => c * d j) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [horL, List.foldr_cons] at ih ⊢
    rw [Nat.mul_add, Nat.mul_left_comm, ih]

theorem horL_zero (l : List Nat) : horL l (fun _ => 0) = 0 := by
  induction l with
  | nil => rfl
  | cons j l ih => simp only [horL, List.foldr_cons] at ih ⊢; rw [ih]

theorem horL_congr (l : List Nat) {d e : Nat → Nat} (h : ∀ j ∈ l, d j = e j) :
    horL l d = horL l e := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [horL, List.foldr_cons] at ih ⊢
    rw [h j List.mem_cons_self, ih (fun i hi => h i (List.mem_cons_of_mem _ hi))]

theorem foldr_xor_lt (L : List Nat) (f : Nat → Nat) (h : ∀ i ∈ L, f i < 1024) :
    L.foldr (fun i acc => f i ^^^ acc) 0 < 1024 := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.foldr_cons]
    exact Nat.xor_lt_two_pow (n := 10) (h i List.mem_cons_self)
      (ih fun k hk => h k (List.mem_cons_of_mem _ hk))

theorem foldr_horL (L R : List Nat) (d : Nat → Nat → Nat) (h : ∀ i, ∀ j ∈ R, d i j < 1024) :
    L.foldr (fun i acc => horL R (d i) ^^^ acc) 0 =
      horL R (fun j => L.foldr (fun i acc => d i j ^^^ acc) 0) := by
  induction L with
  | nil => simp only [List.foldr_nil]; exact (horL_zero R).symm
  | cons i L ih =>
    simp only [List.foldr_cons]
    rw [ih, horL_xor R (h i) (fun j hj => foldr_xor_lt L _ (fun k _ => h k j hj))]

theorem mulT_map (l : List Nat) (f g : Nat → Nat) :
    mulT (l.map f) (l.map g) = l.foldr (fun i acc => f i * g i ^^^ acc) 0 := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.map_cons, mulT, List.foldr_cons, ih]

theorem bitsD_digsK (k i : Nat) :
    bitsD (digsK k) i = horL (List.range 10) (fun j => if (colK k j).testBit i then 1 else 0) := by
  simp only [bitsD, digsK, horL, List.foldr_map]

theorem prodK_horL (ka kr : Nat) :
    prodK ka kr = horL (List.range 10) (fun j => linK ka (colK kr j)) := by
  simp only [prodK, horL, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.foldr_cons, List.foldr_nil, Nat.mul_zero, Nat.add_zero]

theorem prodK_eq_mulT (ka kr : Nat) : prodK ka kr = mulT (digsK ka) (trK kr) := by
  rw [prodK_horL, digsK, trK, mulT_map]
  simp only [bitsD_digsK, horL_mul]
  rw [foldr_horL _ _ _ (fun i j _ => ?_)]
  · refine horL_congr _ fun j _ => ?_
    unfold linK
    congr 1
    funext i acc
    split <;> simp_all
  · have := colK_lt ka i
    split <;> omega


theorem KTree.find_mem {α : Type} {x : Nat} {v : α} :
    ∀ {t : KTree α}, t.find x = some v → (x, v) ∈ t.toList
  | .leaf, h => by simp [KTree.find] at h
  | .node l k w r, h => by
    simp only [KTree.find] at h
    simp only [KTree.toList, List.mem_append, List.mem_cons]
    split at h
    · exact Or.inl (find_mem h)
    · split at h
      · exact Or.inr (Or.inr (find_mem h))
      · cases h
        exact Or.inr (Or.inl (by rw [show x = k by omega]))

theorem idxF_eq {K : List Nat} {t : KTree Nat} (h : treeOK K t = true) (x : Nat) :
    idxF K t x = K.idxOf x := by
  unfold idxF
  cases hf : t.find x with
  | none => rfl
  | some v =>
    have := List.all_eq_true.1 h _ (KTree.find_mem hf)
    simp only [beq_iff_eq] at this
    exact this.symm

theorem tabK_eq {K : List Nat} {t : KTree Nat} (h : treeOK K t = true) : tabK K = tabF K t := by
  unfold tabK tabF tabG
  refine List.map_congr_left fun a _ => ?_
  rw [List.map_map]
  refine List.map_congr_left fun r _ => ?_
  simp only [Function.comp_apply, idxF_eq h, prodK_eq_mulT]

inductive VT (α : Type) where
  | leaf : α → VT α
  | node : VT α → VT α → VT α

@[expose] def VT.ofL {α : Type} (z : α) : Nat → List α → VT α
  | 0, l => .leaf (l.headD z)
  | d + 1, l => .node (VT.ofL z d (l.take (2 ^ d))) (VT.ofL z d (l.drop (2 ^ d)))

@[expose] def VT.get {α : Type} (z : α) : Nat → VT α → Nat → α
  | 0, .leaf x, _ => x
  | d + 1, .node l r, i => if i < 2 ^ d then VT.get z d l i else VT.get z d r (i - 2 ^ d)
  | _, _, _ => z

@[expose] def vgetL {α : Type} (z : α) (d : Nat) (t : VT α) (l : List α) (i : Nat) : α :=
  if i < 2 ^ d then VT.get z d t i else l.getD i z

@[expose] def getF (K : List Nat) (t : KTree Nat) (d : Nat) (VK : VT Nat) (VS : VT (List Nat))
    (KS : List (List Nat)) (y x : Nat) : Nat :=
  if y < K.length ∧ x < K.length then
    idxF K t (mulT (digsK (vgetL 0 d VK K y)) (vgetL [] d VS KS x))
  else 0

@[expose] def extOKH (g : Nat → Nat → Nat) (e n : Nat) (F : List (List Nat))
    (memF : List Nat → Bool) : Bool :=
  F.all fun Y => (List.range n).all fun y =>
    !(g y y == e && !Y.contains y && Y.all fun x => g y x == g x y) ||
      memF (isortN (Y ++ Y.map fun x => g y x))

@[expose] def codeL (L : List Nat) : Nat :=
  L.foldr (fun x acc => 2 ^ x ||| acc) 0 *
    0x9E3779B97F4A7C15F39CC0605CEDC8341082276BF3A27251F86C6A11D0C18E95 % 2 ^ 256

@[expose] def famTree (fam : List (List Nat)) : KTree (List Nat) :=
  fam.foldl (fun t L => t.ins (codeL L) L) .leaf

@[expose] def famF (FT : KTree (List Nat)) (fam : List (List Nat)) (L : List Nat) : Bool :=
  match FT.find (codeL L) with
  | some L' => L' == L || fam.contains L
  | none => fam.contains L

theorem VT.get_ofL {α : Type} (z : α) :
    ∀ (d : Nat) (l : List α) (i : Nat), i < 2 ^ d → VT.get z d (VT.ofL z d l) i = l.getD i z
  | 0, l, i, hi => by
    have : i = 0 := by simp at hi; omega
    subst this
    cases l <;> rfl
  | d + 1, l, i, hi => by
    simp only [VT.ofL, VT.get]
    split
    · rw [VT.get_ofL z d _ i (by omega)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
      simp [*]
    · rw [VT.get_ofL z d _ (i - 2 ^ d) (by rw [Nat.pow_succ] at hi; omega)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
      congr 2
      omega

theorem vgetL_ofL {α : Type} (z : α) (d : Nat) (l : List α) (i : Nat) :
    vgetL z d (VT.ofL z d l) l i = l.getD i z := by
  unfold vgetL
  split
  · exact VT.get_ofL z d l i ‹_›
  · rfl

theorem getT_tabF (K : List Nat) (t : KTree Nat) (d : Nat) (y x : Nat) :
    getT (tabF K t) y x =
      getF K t d (VT.ofL 0 d K) (VT.ofL [] d (K.map trK)) (K.map trK) y x := by
  unfold getT getF tabF tabG
  rw [vgetL_ofL, vgetL_ofL]
  by_cases hy : y < K.length
  · by_cases hx : x < K.length
    · simp [List.getD_eq_getElem?_getD, hx, hy]
    · simp [List.getD_eq_getElem?_getD, hx, hy]
  · simp [List.getD_eq_getElem?_getD, hy]

theorem KTree.mem_ins {α : Type} {k : Nat} {v : α} {p : Nat × α} :
    ∀ {t : KTree α}, p ∈ (t.ins k v).toList → p ∈ t.toList ∨ p = (k, v)
  | .leaf, h => by simpa [KTree.ins, KTree.toList] using h
  | .node l k' v' r, h => by
    simp only [KTree.ins] at h
    split at h
    · simp only [KTree.toList, List.mem_append, List.mem_cons] at h ⊢
      rcases h with h | h | h
      · rcases mem_ins h with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inl (Or.inr (Or.inr h))
    · split at h
      · simp only [KTree.toList, List.mem_append, List.mem_cons] at h ⊢
        rcases h with h | h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr (Or.inl h))
        · rcases mem_ins h with h | h
          · exact Or.inl (Or.inr (Or.inr h))
          · exact Or.inr h
      · exact Or.inl h

theorem famTree_sound (fam : List (List Nat)) {k : Nat} {L : List Nat}
    (h : (k, L) ∈ (famTree fam).toList) : L ∈ fam := by
  unfold famTree at h
  suffices H : ∀ (G : List (List Nat)) (t : KTree (List Nat)),
      (∀ p ∈ t.toList, p.2 ∈ fam) → (∀ M ∈ G, M ∈ fam) →
        ∀ p ∈ (G.foldl (fun t L => t.ins (codeL L) L) t).toList, p.2 ∈ fam from
    H fam .leaf (by simp [KTree.toList]) (fun M hM => hM) _ h
  intro G
  induction G with
  | nil => intro t ht _; simpa using ht
  | cons M G ih =>
    intro t ht hG
    simp only [List.foldl_cons]
    refine ih _ (fun p hp => ?_) (fun N hN => hG N (List.mem_cons_of_mem _ hN))
    rcases KTree.mem_ins hp with hp | hp
    · exact ht p hp
    · rw [hp]; exact hG M List.mem_cons_self

theorem famF_eq (fam : List (List Nat)) (L : List Nat) :
    famF (famTree fam) fam L = fam.contains L := by
  unfold famF
  split
  · rename_i L' hf
    have hL' := famTree_sound fam (KTree.find_mem hf)
    cases hb : (L' == L)
    · rfl
    · simp only [beq_iff_eq] at hb
      subst hb
      simp [List.contains_iff_mem, hL']
  · rfl

theorem extOKG_tabK {K : List Nat} {t : KTree Nat} (h : treeOK K t = true) (d e n : Nat)
    (F fam : List (List Nat)) :
    extOKG (tabK K) e n F fam =
      extOKH (getF K t d (VT.ofL 0 d K) (VT.ofL [] d (K.map trK)) (K.map trK)) e n F
        (famF (famTree fam) fam) := by
  have hg : getT (tabK K) = getF K t d (VT.ofL 0 d K) (VT.ofL [] d (K.map trK)) (K.map trK) := by
    funext y x
    rw [tabK_eq h, getT_tabF]
  have hf : (fun L => fam.contains L) = famF (famTree fam) fam := by
    funext L
    rw [famF_eq]
  unfold extOKG extOKH extL
  rw [hg, ← hf]

end CFSG.KC.EvenSporDS81
