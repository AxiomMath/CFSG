module

public import Certificates.Data.Kernel.WrPack
public import CFSG.Certificates.Kernel.WrTwinSound
public import CFSG.ClassicalInvolution.Q3.AE.PermElt

public section

namespace CFSG.KC.WrPack

open CFSG.KC.WrTwin CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117

variable {n e pp : Nat}

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem land15 (a : Nat) : a &&& 15 = a % 16 := by
  have h := Nat.and_two_pow_sub_one_eq_mod a 4
  norm_num at h
  exact h

theorem pmK_eq : ∀ (m x y : Nat), pmK m x y = pmul m x y
  | 0, _, _ => rfl
  | m + 1, x, y => by
    change ((x >>> (4 * (y &&& 15))) &&& 15) + 16 * pmK m x (y >>> 4) = _
    rw [pmK_eq m, pmul, land15, land15, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]

theorem pm_enc (hn : n ≤ 8) (a b : Wr n) : pm n (enc a) (enc b) = enc (a * b) := by
  unfold pm
  rw [pmK_eq]
  exact (enc_mul hn a b).symm

theorem enc_inj (hn : n ≤ 8) {a b : Wr n} (h : enc a = enc b) : a = b := enc_injective hn h

theorem lvl_mul (hn : n ≤ 8) (σ τ : Equiv.Perm (Fin n)) :
    pairMul n (lvl σ) (lvl τ) = lvl (σ * τ) := by
  simp only [pairMul, lvl, pm_enc hn, ← mul_inv_rev, ofPerm_mul]

theorem prods_eq (hn : n ≤ 8) (he : enc (1 : Wr n) = e) (L : List (List (Equiv.Perm (Fin n)))) :
    prods n e (L.map (·.map lvl)) = (chainProds L).map lvl := by
  induction L with
  | nil =>
    rw [List.map_nil, prods, chainProds, List.map_cons, List.map_nil, ← he]
    simp only [lvl, ofPerm_one, inv_one]
  | cons E L ih =>
    rw [List.map_cons, prods, chainProds, ih, List.flatMap_map, List.map_flatMap]
    congr 1
    funext σ
    simp only [List.map_map]
    exact List.map_congr_left fun τ _ => lvl_mul hn σ τ

theorem mem_allL : ∀ (n : Nat) (l : List (ZMod 2)), l.length = n → l ∈ allL n
  | 0, [], _ => List.mem_singleton_self _
  | n + 1, x :: l, h => by
    simp only [allL, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨l, mem_allL n l (by simpa using h), ?_⟩
    rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) x with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem vecL_ofFn (v : Fin n → ZMod 2) : vecL (List.ofFn v) = v := by
  funext i
  simp [vecL, List.getD_eq_getElem?_getD]

theorem mem_Vall (v : Fin n → ZMod 2) : enc (ofVec v) ∈ Vall n := by
  have h1 : List.ofFn v ∈ allL n := mem_allL n (List.ofFn v) List.length_ofFn
  refine List.mem_map.2 ⟨List.ofFn v, h1, ?_⟩
  rw [vecL_ofFn]

theorem mem_VevenW {v : Fin n → ZMod 2} (hv : ∑ i, v i = 0) : ofVec v ∈ VevenW n := by
  have h1 : List.ofFn v ∈ allL n := mem_allL n (List.ofFn v) List.length_ofFn
  refine List.mem_map.2 ⟨List.ofFn v, List.mem_filter.2 ⟨h1, ?_⟩, ?_⟩
  · rw [vecL_ofFn]
    exact decide_eq_true hv
  · rw [vecL_ofFn]

theorem Veven_eq : Veven n = (VevenW n).map enc := rfl

theorem eqPi_iff' {x y : Wr n} : eqPi x y = true ↔ x = y ∨ x * allOnes n = y := by
  simp only [eqPi, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by rw [h, mul_assoc, allOnes_mul_self n, mul_one])
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by rw [← h, mul_assoc, allOnes_mul_self n, mul_one])

theorem eqPi_perm' {x y : Wr n} (h : eqPi x y = true) : x.perm = y.perm := by
  rcases eqPi_iff'.1 h with h | h
  · rw [h]
  · rw [← h, mul_perm]
    exact (mul_one _).symm

theorem beq_enc (hn : n ≤ 8) (x y : Wr n) : Nat.beq (enc x) (enc y) = decide (x = y) := by
  refine Bool.eq_iff_iff.2 ?_
  rw [Nat.beq_eq, decide_eq_true_eq]
  exact ⟨enc_inj hn, congrArg enc⟩

theorem eqPiP_enc (hn : n ≤ 8) (hp : enc (allOnes n) = pp) (x y : Wr n) :
    eqPiP n pp (enc x) (enc y) = eqPi x y := by
  rw [← hp]
  unfold eqPiP eqPi
  rw [pm_enc hn, beq_enc hn, beq_enc hn]

theorem inModPi_iff (hn : n ≤ 8) (hp : enc (allOnes n) = pp) (x : Wr n) (B : List (Wr n)) :
    inModPi n pp (enc x) (B.map enc) = true ↔ ∃ y ∈ B, eqPi x y = true := by
  unfold inModPi
  rw [List.any_map, List.any_eq_true]
  simp only [Function.comp_apply, eqPiP_enc hn hp]

theorem nib_enc_perm (hn : n ≤ 8) (a : Wr n) (i : Nat) (hi : i < n) :
    nib (enc a) (2 * i) / 2 = (a.perm ⟨i, hi⟩).val := by
  have h1 : nib (enc a) (2 * i) = img a (2 * i) := nib_enc hn a (by omega)
  have h2 : img a (2 * i) =
      2 * (a.perm ⟨i, hi⟩).val + ((0 : ZMod 2) + a.vec (a.perm ⟨i, hi⟩)).val := by
    have := img_pt a ⟨i, hi⟩ 0
    rwa [ZMod.val_zero, add_zero] at this
  have h3 := ZMod.val_lt ((0 : ZMod 2) + a.vec (a.perm ⟨i, hi⟩))
  rw [h1, h2]
  omega

theorem samePerm_iff (hn : n ≤ 8) (a b : Wr n) :
    samePerm n (enc a) (enc b) = true ↔ a.perm = b.perm := by
  simp only [samePerm, List.all_eq_true, List.mem_range, Nat.beq_eq]
  constructor
  · intro h
    refine Equiv.ext fun i => Fin.ext ?_
    have := h i.val i.isLt
    rw [nib_enc_perm hn a i.val i.isLt, nib_enc_perm hn b i.val i.isLt] at this
    exact this
  · intro h i hi
    rw [nib_enc_perm hn a i hi, nib_enc_perm hn b i hi, h]

theorem ofVec_mul_ofPerm (a : Wr n) : ofVec a.vec * ofPerm a.perm = a := by
  refine Wr.ext (funext fun i => ?_) (one_mul _)
  change a.vec i + 0 = a.vec i
  rw [add_zero]

theorem lvl_fst (σ : Equiv.Perm (Fin n)) : (lvl σ).1 = enc (ofPerm σ) := rfl

theorem lvl_snd (σ : Equiv.Perm (Fin n)) : (lvl σ).2 = enc (ofPerm σ)⁻¹ := rfl

theorem pm_lvl (hn : n ≤ 8) (a : Wr n) : pm n (enc (ofVec a.vec)) (lvl a.perm).1 = enc a := by
  rw [lvl_fst, pm_enc hn, ofVec_mul_ofPerm]

theorem perm_comm_of_eqPi {x y : Wr n} (h : eqPi (y * x) (x * y) = true) :
    x.perm * y.perm = y.perm * x.perm := by
  have h3 : (y * x).perm = (x * y).perm := eqPi_perm' h
  rw [mul_perm, mul_perm] at h3
  exact h3.symm

theorem centOK_sound (hn : n ≤ 8) (hp : enc (allOnes n) = pp) {P : List (Nat × Nat)}
    {V : List Nat} {G C : List (Wr n)} (h : centOK n pp (G.map enc) P V (C.map enc) = true)
    (a : Wr n) (hP : lvl a.perm ∈ P) (hV : enc (ofVec a.vec) ∈ V)
    (hc : ∀ s ∈ G, eqPi (s * a) (a * s) = true) : ∃ c ∈ C, eqPi a c = true := by
  have h1 := List.all_eq_true.1 h _ hP
  beta_reduce at h1
  have hA : ((G.map enc).all fun s => samePerm n (pm n (lvl a.perm).1 s) (pm n s (lvl a.perm).1)) =
      true := by
    rw [List.all_eq_true]
    intro s0 hs0
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hs0
    rw [lvl_fst, pm_enc hn, pm_enc hn, samePerm_iff hn, mul_perm, mul_perm]
    change a.perm * s.perm = s.perm * a.perm
    exact perm_comm_of_eqPi (hc s hs)
  rw [hA, Bool.not_true, Bool.false_or] at h1
  have h2 := List.all_eq_true.1 h1 _ hV
  dsimp only at h2
  rw [pm_lvl hn] at h2
  have hB : ((G.map enc).all fun s => eqPiP n pp (pm n s (enc a)) (pm n (enc a) s)) = true := by
    rw [List.all_eq_true]
    intro s0 hs0
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hs0
    rw [pm_enc hn, pm_enc hn, eqPiP_enc hn hp]
    exact hc s hs
  rw [hB, Bool.not_true, Bool.false_or, inModPi_iff hn hp] at h2
  exact h2

theorem sqOK_sound (hn : n ≤ 8) (hp : enc (allOnes n) = pp) {P : List (Nat × Nat)}
    {V : List Nat} {G Y : List (Wr n)} (h : sqOK n pp (G.map enc) P V (Y.map enc) = true)
    (c : Wr n) (hP : lvl c.perm ∈ P) (hV : enc (ofVec c.vec) ∈ V)
    (hc : ∀ s ∈ G, eqPi (c * c * (c * c) * s) (s * (c * c * (c * c))) = true) :
    ∃ y ∈ Y, eqPi (c * c * y) (y * (c * c)) = true := by
  have h1 := List.all_eq_true.1 h _ hP
  simp only [strictB_eq, lvl_fst, pm_enc hn] at h1
  have hA : ((G.map enc).all fun s =>
      samePerm n (pm n (enc (ofPerm c.perm * ofPerm c.perm * (ofPerm c.perm * ofPerm c.perm))) s)
        (pm n s (enc (ofPerm c.perm * ofPerm c.perm * (ofPerm c.perm * ofPerm c.perm))))) =
      true := by
    rw [List.all_eq_true]
    intro s0 hs0
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hs0
    rw [pm_enc hn, pm_enc hn, samePerm_iff hn]
    have h3 := perm_comm_of_eqPi (hc s hs)
    simp only [mul_perm] at h3 ⊢
    exact h3.symm
  rw [hA, Bool.not_true, Bool.false_or] at h1
  have h2 := List.all_eq_true.1 h1 _ hV
  beta_reduce at h2
  simp only [pm_enc hn, ofVec_mul_ofPerm] at h2
  have hB : ((G.map enc).all fun s =>
      eqPiP n pp (pm n (enc (c * c * (c * c))) s) (pm n s (enc (c * c * (c * c))))) = true := by
    rw [List.all_eq_true]
    intro s0 hs0
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hs0
    rw [pm_enc hn, pm_enc hn, eqPiP_enc hn hp]
    exact hc s hs
  rw [hB, Bool.not_true, Bool.false_or, List.any_map, List.any_eq_true] at h2
  obtain ⟨y, hy, hyc⟩ := h2
  refine ⟨y, hy, ?_⟩
  simpa only [Function.comp_apply, pm_enc hn, eqPiP_enc hn hp] using hyc

@[expose] def ord4W (x : Wr n) : Bool := !inPi (x * x) && inPi (x * x * (x * x))

@[expose] def q8W (x y : Wr n) : Bool :=
  ord4W x && eqPi (y * y) (x * x) && eqPi (x * y * (x * y)) (x * x) && !eqPi y x &&
    !eqPi y (x * x * x)

theorem inPiP_enc (hn : n ≤ 8) (he : enc (1 : Wr n) = e) (hp : enc (allOnes n) = pp) (x : Wr n) :
    inPiP e pp (enc x) = inPi x := by
  rw [← he, ← hp]
  unfold inPiP inPi
  rw [beq_enc hn, beq_enc hn]

theorem ord4P_enc (hn : n ≤ 8) (he : enc (1 : Wr n) = e) (hp : enc (allOnes n) = pp) (x : Wr n) :
    ord4P n e pp (enc x) = ord4W x := by
  unfold ord4P ord4W
  rw [strictB_eq, pm_enc hn, pm_enc hn, inPiP_enc hn he hp, inPiP_enc hn he hp]

theorem q8P_enc (hn : n ≤ 8) (he : enc (1 : Wr n) = e) (hp : enc (allOnes n) = pp) (x y : Wr n) :
    q8P n e pp (enc x) (enc y) = q8W x y := by
  unfold q8P q8W
  rw [strictB_eq, strictB_eq, ord4P_enc hn he hp]
  simp only [pm_enc hn, eqPiP_enc hn hp]

theorem q8OK_sound (hn : n ≤ 8) (he : enc (1 : Wr n) = e) (hp : enc (allOnes n) = pp)
    {P : List (Nat × Nat)} {V : List Nat} {M : List (List (Wr n))}
    (h : q8OK n e pp P V (M.map (·.map enc)) = true) (x y : Wr n)
    (hPx : lvl x.perm ∈ P) (hVx : enc (ofVec x.vec) ∈ V) (hPy : lvl y.perm ∈ P)
    (hVy : enc (ofVec y.vec) ∈ V) (hq : q8W x y = true) :
    ∃ m ∈ M, (∃ a ∈ m, eqPi a x = true) ∧ ∃ a ∈ m, eqPi a y = true := by
  have hq' := hq
  simp only [q8W, Bool.and_eq_true] at hq'
  obtain ⟨⟨⟨⟨hx4, hyy⟩, hxy⟩, -⟩, -⟩ := hq'
  have h1 := List.all_eq_true.1 h _ hPx
  have h2 := List.all_eq_true.1 h1 _ hVx
  simp only [strictB_eq, pm_lvl hn, ord4P_enc hn he hp, hx4, Bool.not_true, Bool.false_or,
    pm_enc hn] at h2
  have h3 := List.all_eq_true.1 h2 _ hPy
  have hpre : (samePerm n (pm n (lvl y.perm).1 (lvl y.perm).1) (enc (x * x)) &&
      samePerm n (pm n (enc (x * ofPerm y.perm)) (enc (x * ofPerm y.perm))) (enc (x * x))) = true := by
    rw [Bool.and_eq_true, lvl_fst, pm_enc hn, pm_enc hn, samePerm_iff hn, samePerm_iff hn]
    refine ⟨?_, ?_⟩
    · have := eqPi_perm' hyy
      simp only [mul_perm] at this ⊢
      exact this
    · have := eqPi_perm' hxy
      simp only [mul_perm] at this ⊢
      exact this
  simp only [strictB_eq, lvl_fst, pm_enc hn] at h3 hpre
  rw [hpre, Bool.not_true, Bool.false_or] at h3
  have h4 := List.all_eq_true.1 h3 _ hVy
  simp only [strictB_eq, pm_enc hn, ofVec_mul_ofPerm, q8P_enc hn he hp, hq, Bool.not_true,
    Bool.false_or, List.any_map, List.any_eq_true, Bool.and_eq_true, Function.comp_apply,
    eqPiP_enc hn hp] at h4
  exact h4

end CFSG.KC.WrPack

end
