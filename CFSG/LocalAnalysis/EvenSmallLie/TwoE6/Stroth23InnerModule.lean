module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23InnerData
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeTraceCent
public import CFSG.Monster.B.TwoA.Unitary.TwentyBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6.Stroth23Inner

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.VisCert CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Unitary

@[expose] noncomputable def genN (k : ℕ) : Usig := if h : k < 17 then genU ⟨k, h⟩ else 1

@[expose] noncomputable def wordElt (w : List ℕ) : Usig := (w.map genN).prod

theorem wordElt_nil : wordElt [] = 1 := rfl

theorem wordElt_cons (k : ℕ) (w : List ℕ) : wordElt (k :: w) = genN k * wordElt w := by
  simp [wordElt]

theorem wordAct_cons (k : ℕ) (w : List ℕ) (c : ℕ) :
    wordAct (k :: w) c = wordAct w (Native.actD 22 n6RowArr[k]! c) := rfl

theorem wAct_wordElt_decW (w : List ℕ) (hw : ∀ k ∈ w, k < 17) (c : ℕ) :
    wAct v0 (wordElt w : Kstab v0) (decW c) = decW (wordAct w c) := by
  induction w generalizing c with
  | nil => simp [wordElt_nil, wAct_one, wordAct]
  | cons k w ih =>
    have hk : k < 17 := hw k (List.mem_cons_self ..)
    rw [wordElt_cons, Subgroup.coe_mul, wAct_mul, Module.End.mul_apply, wordAct_cons,
      ← ih (fun k' hk' => hw k' (List.mem_cons_of_mem _ hk'))]
    congr 1
    rw [genN, dite_eq_left hk]
    exact wAct_genK_decW ⟨k, hk⟩ c

theorem rowsAct_getElem (w : List ℕ) (t : Fin 22) :
    (rowsAct w)[(t : ℕ)]! = wordAct w (1 <<< (t : ℕ)) := by
  simp [rowsAct]

theorem wAct_wordElt_rows (w : List ℕ) (hw : ∀ k ∈ w, k < 17) (c : ℕ) :
    wAct v0 (wordElt w : Kstab v0) (decW c) = decW (Native.actD 22 (rowsAct w) c) :=
  end_decW (fun t => by
    rw [rowsAct_getElem, ← wAct_wordElt_decW w hw, CFSG.Monster.B.Co2.decW_one_shiftLeft]) c

theorem decW_foldl_xorSel (f : ℕ → ℕ) (m : ℕ) (l : List ℕ) (a : ℕ) :
    decW (l.foldl (fun a j => if m.testBit j then a ^^^ f j else a) a) =
      decW a + (l.map fun j => if m.testBit j then decW (f j) else 0).sum := by
  induction l generalizing a with
  | nil => simp
  | cons j l ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, ← add_assoc]
    congr 1
    split_ifs <;> simp [decW_xor]

theorem decW_xorSel (f : ℕ → ℕ) (m : ℕ) :
    decW (xorSel f m) = ∑ j ∈ Finset.range 21, if m.testBit j then decW (f j) else 0 := by
  rw [xorSel, decW_foldl_xorSel, decW_zero, zero_add, Finset.sum_range, ← List.sum_ofFn]
  congr 1

theorem xorSel_lt (f : ℕ → ℕ) (m : ℕ) (hf : ∀ j < 21, f j < 2 ^ 22) : xorSel f m < 2 ^ 22 := by
  have key : ∀ (l : List ℕ) (a : ℕ), a < 2 ^ 22 → (∀ j ∈ l, j < 21) →
      l.foldl (fun a j => if m.testBit j then a ^^^ f j else a) a < 2 ^ 22 := by
    intro l
    induction l with
    | nil => intro a ha _; exact ha
    | cons j l ih =>
      intro a ha hl
      refine ih _ ?_ fun j' hj' => hl j' (List.mem_cons_of_mem _ hj')
      show (if m.testBit j then a ^^^ f j else a) < 2 ^ 22
      split_ifs
      · exact Nat.xor_lt_two_pow ha (hf j (hl j (List.mem_cons_self ..)))
      · exact ha
  exact key _ 0 (by norm_num) fun j hj => List.mem_range.1 hj

theorem actGo_lt (rows : Array ℕ) (v : ℕ) (hr : ∀ i < 22, rows[i]! < 2 ^ 22) :
    ∀ d ≤ 22, ∀ acc < 2 ^ 22, VisCert.Native.actGo rows v d acc < 2 ^ 22
  | 0, _, acc, h => h
  | d + 1, hd, acc, h => by
    rw [VisCert.Native.actGo]
    refine actGo_lt rows v hr d (by omega) _ ?_
    split_ifs
    · exact Nat.xor_lt_two_pow h (hr d (by omega))
    · exact h

theorem actD_lt {rows : Array ℕ} (hr : ∀ i < 22, rows[i]! < 2 ^ 22) (c : ℕ) :
    Native.actD 22 rows c < 2 ^ 22 :=
  actGo_lt rows c hr 22 le_rfl 0 (by norm_num)

@[expose] noncomputable def uOf (k : ℕ) : SUh ⧸ Zh :=
  if h : k < 17 then (b6SU ⟨k, h⟩ : SUh ⧸ Zh) else 1

@[expose] noncomputable def uWord (w : List ℕ) : SUh ⧸ Zh := (w.map uOf).prod

theorem uWord_cons (k : ℕ) (w : List ℕ) : uWord (k :: w) = uOf k * uWord w := by
  simp [uWord]

theorem uWord_append (w w' : List ℕ) : uWord (w ++ w') = uWord w * uWord w' := by
  simp [uWord]

theorem uWord_singleton (k : ℕ) : uWord [k] = uOf k := by simp [uWord]

theorem b6Frob_eq_zero : ∀ k : Fin 17, (k : ℕ) ≠ 5 → b6Frob k = 0 := by decide

theorem slElt_eq_inl {k : Fin 17} (hk : (k : ℕ) ≠ 5) :
    slElt k = SemidirectProduct.inl (b6SU k : SUh ⧸ Zh) := by
  refine SemidirectProduct.ext rfl ?_
  change Multiplicative.ofAdd (b6Frob k) = 1
  rw [b6Frob_eq_zero k hk]
  rfl

theorem phiU_symm_inl_uOf {k : ℕ} (hk : k < 17) (h5 : k ≠ 5) :
    phiU.symm (SemidirectProduct.inl (uOf k)) = genN k := by
  rw [uOf, dite_eq_left hk, genN, dite_eq_left hk, ← slElt_eq_inl (k := ⟨k, hk⟩) h5,
    ← phiU_genU, MulEquiv.symm_apply_apply]

theorem phiU_symm_inl_uWord (w : List ℕ) (hw : ∀ k ∈ w, k < 17 ∧ k ≠ 5) :
    phiU.symm (SemidirectProduct.inl (uWord w)) = wordElt w := by
  induction w with
  | nil => simp [uWord, wordElt]
  | cons k w ih =>
    have hk := hw k (List.mem_cons_self ..)
    rw [uWord_cons, map_mul, map_mul, ih fun k' hk' => hw k' (List.mem_cons_of_mem _ hk'),
      phiU_symm_inl_uOf hk.1 hk.2, wordElt_cons]

@[expose] noncomputable def rhoU (u : SUh ⧸ Zh) : Module.End (ZMod 2) sigmaPerp :=
  perpEnd (phiU.symm (SemidirectProduct.inl u))

theorem rhoU_mul (u u' : SUh ⧸ Zh) : rhoU (u * u') = rhoU u' * rhoU u := by
  rw [rhoU, map_mul, map_mul, perpEnd_mul]
  rfl

theorem rhoU_one : rhoU 1 = 1 := by
  rw [rhoU, map_one, map_one, perpEnd_one]

theorem rhoU_uWord (w : List ℕ) (hw : ∀ k ∈ w, k < 17 ∧ k ≠ 5) :
    rhoU (uWord w) = perpEnd (wordElt w) := by
  rw [rhoU, phiU_symm_inl_uWord w hw]

theorem getElem!_map_of_lt {α β : Type} [Inhabited α] [Inhabited β] (a : Array α) (f : α → β)
    {j : ℕ} (hj : j < a.size) : (a.map f)[j]! = f a[j]! := by
  rw [getElem!_pos (a.map f) j (by simpa using hj), getElem!_pos a j hj, Array.getElem_map]

theorem getElem!_ofFn22 (f : Fin 22 → ℕ) (t : Fin 22) :
    (Array.ofFn (n := 22) f)[(t : ℕ)]! = f t := by
  simp

theorem decW_actD_sumRows (R : ℕ → Array ℕ) (m n : ℕ) :
    decW (Native.actD 22 (Array.ofFn (n := 22) fun t => xorSel (fun j => (R j)[(t : ℕ)]!) m) n) =
      decW (xorSel (fun j => Native.actD 22 (R j) n) m) := by
  have hact : ∀ (rows : Array ℕ) (c : ℕ), decW (Native.actD 22 rows c) =
      ∑ i ∈ Finset.range 22, if c.testBit i then decW rows[i]! else 0 := fun rows c => by
    rw [Native.actD, xorHom_actGo decW decW_xor, decW_zero, zero_add]
  rw [hact, decW_xorSel]
  simp_rw [hact]
  have e : ∀ i ∈ Finset.range 22,
      (if n.testBit i then decW (Array.ofFn (n := 22) fun t =>
        xorSel (fun j => (R j)[(t : ℕ)]!) m)[i]! else 0) =
      ∑ j ∈ Finset.range 21, if m.testBit j then
        (if n.testBit i then decW (R j)[i]! else 0) else 0 := by
    intro i hi
    have hi' : i < 22 := Finset.mem_range.1 hi
    have := getElem!_ofFn22 (fun t => xorSel (fun j => (R j)[(t : ℕ)]!) m) ⟨i, hi'⟩
    simp only at this
    rw [this, decW_xorSel]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl e, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem n6RowArr_zero_lt : ∀ t < 22, (n6RowArr[0]!)[t]! < 2 ^ 22 := by decide

theorem decW155_mem : decW 155 ∈ sigmaPerp := (bW_sigmaW_decW _).trans (by decide +kernel)

theorem decW714762_mem : decW 714762 ∈ sigmaPerp := (bW_sigmaW_decW _).trans (by decide +kernel)

theorem cycWordsD_letters : ∀ j < 21, ∀ k ∈ cycWordsD[j]!, k = 0 ∨ k = 4 ∨ k = 6 ∨ k = 7 ∨
    k = 8 ∨ k = 9 ∨ k = 16 := by decide

theorem deltaWordD_inner : ∀ j < 21, ∀ k ∈ deltaWord cycWordsD[j]!, k < 17 ∧ k ≠ 5 := by decide

theorem cycWordsI_inner : ∀ j < 21, ∀ k ∈ cycWordsI[j]!, k < 17 ∧ k ≠ 5 := by decide

theorem cycWordsD_size : cycWordsD.size = 21 := rfl

theorem cycWordsI_size : cycWordsI.size = 21 := rfl

theorem intertwine_word {β : (SUh ⧸ Zh) →* (SUh ⧸ Zh)} {A : Module.End (ZMod 2) sigmaPerp}
    (hA : ∀ u x, A (rhoU u x) = rhoU (β u) (A x)) {w w' : List ℕ}
    (hw : ∀ k ∈ w, k < 17 ∧ k ≠ 5) (hw' : ∀ k ∈ w', k < 17 ∧ k ≠ 5) (hβ : β (uWord w) = uWord w')
    (x : sigmaPerp) : A (perpEnd (wordElt w) x) = perpEnd (wordElt w') (A x) := by
  calc A (perpEnd (wordElt w) x) = A (rhoU (uWord w) x) := by rw [rhoU_uWord w hw]
    _ = rhoU (β (uWord w)) (A x) := hA _ _
    _ = rhoU (uWord w') (A x) := congrArg (fun u => rhoU u (A x)) hβ
    _ = perpEnd (wordElt w') (A x) := by rw [rhoU_uWord w' hw']

theorem deltaWord_cons (k : ℕ) (x : List ℕ) : deltaWord (k :: x) = deltaLetter k ++ deltaWord x :=
  List.flatMap_cons

theorem map_uWord_delta {β : (SUh ⧸ Zh) →* (SUh ⧸ Zh)}
    (hβ : ∀ k, (k = 0 ∨ k = 4 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 16) →
      β (uOf k) = uWord (deltaLetter k)) (x : List ℕ)
    (hx : ∀ k ∈ x, k = 0 ∨ k = 4 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 16) :
    β (uWord x) = uWord (deltaWord x) := by
  induction x with
  | nil => simp [uWord, deltaWord]
  | cons k x ih =>
    rw [uWord_cons, map_mul, hβ k (hx k (List.mem_cons_self ..)),
      ih fun k' hk' => hx k' (List.mem_cons_of_mem _ hk'), deltaWord_cons, uWord_append]

theorem coe_sum_ite (b : ℕ → sigmaPerp) (m : ℕ) :
    ((∑ j ∈ Finset.range 21, if m.testBit j then b j else 0 : sigmaPerp) : Wv v0) =
      ∑ j ∈ Finset.range 21, if m.testBit j then (b j : Wv v0) else 0 := by
  rw [Submodule.coe_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> rfl

theorem map_sum_ite (A : Module.End (ZMod 2) sigmaPerp) (b : ℕ → sigmaPerp) (m : ℕ) :
    A (∑ j ∈ Finset.range 21, if m.testBit j then b j else 0) =
      ∑ j ∈ Finset.range 21, if m.testBit j then A (b j) else 0 := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem eq_sum_ite {b : ℕ → sigmaPerp} {f : ℕ → ℕ} (hb : ∀ j < 21, (b j : Wv v0) = decW (f j))
    {x : sigmaPerp} {m : ℕ} (hx : (x : Wv v0) = decW (xorSel f m)) :
    x = ∑ j ∈ Finset.range 21, if m.testBit j then b j else 0 := by
  refine Subtype.ext ?_
  rw [hx, coe_sum_ite, decW_xorSel]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hb j (Finset.mem_range.1 hj)]

theorem wordElt_zero : wordElt [0] = genU 0 := by
  simp [wordElt, genN]

theorem RD_getElem {j : ℕ} (hj : j < 21) : RD[j]! = rowsAct (deltaWord cycWordsD[j]!) :=
  getElem!_map_of_lt _ _ (by rw [cycWordsD_size]; exact hj)

theorem RI_getElem {j : ℕ} (hj : j < 21) : RI[j]! = rowsAct cycWordsI[j]! :=
  getElem!_map_of_lt _ _ (by rw [cycWordsI_size]; exact hj)

theorem actD_RD_lt {j : ℕ} (hj : j < 21) (n : ℕ) : Native.actD 22 RD[j]! n < 2 ^ 22 :=
  actD_lt (RD_lt j hj) n

theorem actD_RI_lt {j : ℕ} (hj : j < 21) (n : ℕ) : Native.actD 22 RI[j]! n < 2 ^ 22 :=
  actD_lt (RI_lt j hj) n

theorem cycWordsD_inner : ∀ j < 21, ∀ k ∈ cycWordsD[j]!, k < 17 ∧ k ≠ 5 := by decide

@[expose] noncomputable def v0D : sigmaPerp := ⟨decW 155, decW155_mem⟩

@[expose] noncomputable def bD (j : ℕ) : sigmaPerp := perpEnd (wordElt cycWordsD[j]!) v0D

theorem coe_bD {j : ℕ} (hj : j < 21) : (bD j : Wv v0) = decW (vecD j) := by
  rw [bD, perpEnd_apply, vecD, ← wAct_wordElt_decW _ fun k hk => (cycWordsD_inner j hj k hk).1]
  rfl

theorem sigmaP_eq_sum_bD :
    sigmaP = ∑ j ∈ Finset.range 21, if (3112 : ℕ).testBit j then bD j else 0 :=
  eq_sum_ite (fun j hj => coe_bD hj) (by rw [cycD_sigma]; exact sigmaW_eq_decW)

theorem perpEnd_bD_eq_sum {i : ℕ} (hi : i < 21) :
    perpEnd (genU 0) (bD i) = ∑ j ∈ Finset.range 21, if gen0D[i]!.testBit j then bD j else 0 := by
  refine eq_sum_ite (fun j hj => coe_bD hj) ?_
  rw [perpEnd_apply, coe_bD hi, ← cycD_gen0 i hi]
  exact wAct_genK_decW 0 _

section Twist

variable {β : (SUh ⧸ Zh) →* (SUh ⧸ Zh)}
  (hβ : ∀ k, (k = 0 ∨ k = 4 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 16) →
    β (uOf k) = uWord (deltaLetter k))
  {A : Module.End (ZMod 2) sigmaPerp} (hA : ∀ u x, A (rhoU u x) = rhoU (β u) (A x))
  {n : ℕ} (hzn : decW n = (A v0D : Wv v0))

include hβ hA hzn

theorem A_bD {j : ℕ} (hj : j < 21) : (A (bD j) : Wv v0) = decW (Native.actD 22 RD[j]! n) := by
  rw [bD, intertwine_word hA (cycWordsD_inner j hj) (deltaWordD_inner j hj)
    (map_uWord_delta hβ _ (cycWordsD_letters j hj)), perpEnd_apply, ← hzn,
    wAct_wordElt_rows _ fun k hk => (deltaWordD_inner j hj k hk).1, RD_getElem hj]

theorem A_sum_bD (m : ℕ) : (A (∑ j ∈ Finset.range 21, if m.testBit j then bD j else 0) : Wv v0) =
    decW (xorSel (fun j => Native.actD 22 RD[j]! n) m) := by
  rw [map_sum_ite, coe_sum_ite, decW_xorSel]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [A_bD hβ hA hzn (Finset.mem_range.1 hj)]

end Twist

theorem SD_lt : ∀ t < 22, SD[t]! < 2 ^ 22 := fun t ht => by
  rw [SD, getElem!_ofFn22 _ ⟨t, ht⟩]
  exact xorSel_lt _ _ fun j hj => RD_lt j hj t ht

theorem actD_SD {β : (SUh ⧸ Zh) →* (SUh ⧸ Zh)}
    (hβ : ∀ k, (k = 0 ∨ k = 4 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 16) →
      β (uOf k) = uWord (deltaLetter k))
    {A : Module.End (ZMod 2) sigmaPerp} (hA : ∀ u x, A (rhoU u x) = rhoU (β u) (A x))
    {n : ℕ} (hzn : decW n = (A v0D : Wv v0)) (hσ : A sigmaP = sigmaP) :
    Native.actD 22 SD n = 6144 := by
  have h1 := A_sum_bD hβ hA hzn 3112
  rw [← sigmaP_eq_sum_bD, hσ] at h1
  change sigmaW = _ at h1
  rw [sigmaW_eq_decW, ← decW_actD_sumRows] at h1
  exact decW_injective (actD_lt SD_lt n) (by norm_num) h1.symm

theorem gen0_cond {β : (SUh ⧸ Zh) →* (SUh ⧸ Zh)}
    (hβ : ∀ k, (k = 0 ∨ k = 4 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 16) →
      β (uOf k) = uWord (deltaLetter k))
    {A : Module.End (ZMod 2) sigmaPerp} (hA : ∀ u x, A (rhoU u x) = rhoU (β u) (A x))
    {n : ℕ} (hzn : decW n = (A v0D : Wv v0)) {i : ℕ} (hi : i < 21) :
    xorSel (fun j => Native.actD 22 RD[j]! n) gen0D[i]! =
      Native.actD 22 n6RowArr[0]! (Native.actD 22 RD[i]! n) := by
  have e2 : A (perpEnd (genU 0) (bD i)) = perpEnd (genU 0) (A (bD i)) := by
    rw [← wordElt_zero]
    exact intertwine_word hA (by decide) (by decide) (map_uWord_delta hβ [0] (by decide)) _
  have h1 := A_sum_bD hβ hA hzn gen0D[i]!
  rw [← perpEnd_bD_eq_sum hi, e2, perpEnd_apply, A_bD hβ hA hzn hi] at h1
  change wAct v0 (genK 0) _ = _ at h1
  rw [wAct_genK_decW 0 (Native.actD 22 RD[i]! n)] at h1
  exact decW_injective (xorSel_lt _ _ fun j hj => actD_RD_lt hj n)
    (actD_lt n6RowArr_zero_lt _) h1.symm

theorem no_twist_of_delta {β : (SUh ⧸ Zh) →* (SUh ⧸ Zh)}
    (hβ : ∀ k, (k = 0 ∨ k = 4 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 16) →
      β (uOf k) = uWord (deltaLetter k))
    {A : Module.End (ZMod 2) sigmaPerp} (hA : ∀ u x, A (rhoU u x) = rhoU (β u) (A x))
    (hσ : A sigmaP = sigmaP) : False := by
  obtain ⟨n, hn, hzn⟩ := Amalgam.exists_decW_eq ((A v0D : sigmaPerp) : Wv v0)
  obtain ⟨i, hi, hne⟩ := checkD_twist n hn (actD_SD hβ hA hzn hσ)
  exact hne (gen0_cond hβ hA hzn hi)

@[expose] noncomputable def v0I : sigmaPerp := ⟨decW 714762, decW714762_mem⟩

@[expose] noncomputable def bI (j : ℕ) : sigmaPerp := perpEnd (wordElt cycWordsI[j]!) v0I

theorem coe_bI {j : ℕ} (hj : j < 21) : (bI j : Wv v0) = decW (vecI j) := by
  rw [bI, perpEnd_apply, vecI, ← wAct_wordElt_decW _ fun k hk => (cycWordsI_inner j hj k hk).1]
  rfl

theorem sigmaP_eq_sum_bI :
    sigmaP = ∑ j ∈ Finset.range 21, if (3989 : ℕ).testBit j then bI j else 0 :=
  eq_sum_ite (fun j hj => coe_bI hj) (by rw [cycI_sigma]; exact sigmaW_eq_decW)

theorem perpEnd_bI_eq_sum {i : ℕ} (hi : i < 21) :
    perpEnd (genU 0) (bI i) = ∑ j ∈ Finset.range 21, if gen0I[i]!.testBit j then bI j else 0 := by
  refine eq_sum_ite (fun j hj => coe_bI hj) ?_
  rw [perpEnd_apply, coe_bI hi, ← cycI_gen0 i hi]
  exact wAct_genK_decW 0 _

theorem SI_lt : ∀ t < 22, SI[t]! < 2 ^ 22 := fun t ht => by
  rw [SI, getElem!_ofFn22 _ ⟨t, ht⟩]
  exact xorSel_lt _ _ fun j hj => RI_lt j hj t ht

section Ident

variable {A : Module.End (ZMod 2) sigmaPerp} (hA : ∀ u x, A (rhoU u x) = rhoU u (A x))

include hA

theorem intertwine_word_id {w : List ℕ} (hw : ∀ k ∈ w, k < 17 ∧ k ≠ 5) (x : sigmaPerp) :
    A (perpEnd (wordElt w) x) = perpEnd (wordElt w) (A x) :=
  intertwine_word (β := MonoidHom.id _) hA hw hw rfl x

theorem A_bI {n : ℕ} (hzn : decW n = (A v0I : Wv v0)) {j : ℕ} (hj : j < 21) :
    (A (bI j) : Wv v0) = decW (Native.actD 22 RI[j]! n) := by
  rw [bI, intertwine_word_id hA (cycWordsI_inner j hj), perpEnd_apply, ← hzn,
    wAct_wordElt_rows _ fun k hk => (cycWordsI_inner j hj k hk).1, RI_getElem hj]

theorem A_sum_bI {n : ℕ} (hzn : decW n = (A v0I : Wv v0)) (m : ℕ) :
    (A (∑ j ∈ Finset.range 21, if m.testBit j then bI j else 0) : Wv v0) =
      decW (xorSel (fun j => Native.actD 22 RI[j]! n) m) := by
  rw [map_sum_ite, coe_sum_ite, decW_xorSel]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [A_bI hA hzn (Finset.mem_range.1 hj)]

theorem A_v0I (hσ : A sigmaP = sigmaP) : A v0I = v0I := by
  obtain ⟨n, hn, hzn⟩ := Amalgam.exists_decW_eq ((A v0I : sigmaPerp) : Wv v0)
  have hS : Native.actD 22 SI n = 6144 := by
    have h1 := A_sum_bI hA hzn 3989
    rw [← sigmaP_eq_sum_bI, hσ] at h1
    change sigmaW = _ at h1
    rw [sigmaW_eq_decW, ← decW_actD_sumRows] at h1
    exact decW_injective (actD_lt SI_lt n) (by norm_num) h1.symm
  have hgen : ∀ i < 21, xorSel (fun j => Native.actD 22 RI[j]! n) gen0I[i]! =
      Native.actD 22 n6RowArr[0]! (Native.actD 22 RI[i]! n) := fun i hi => by
    have e2 : A (perpEnd (genU 0) (bI i)) = perpEnd (genU 0) (A (bI i)) := by
      rw [← wordElt_zero]
      exact intertwine_word_id hA (by decide) _
    have h1 := A_sum_bI hA hzn gen0I[i]!
    rw [← perpEnd_bI_eq_sum hi, e2, perpEnd_apply, A_bI hA hzn hi] at h1
    change wAct v0 (genK 0) _ = _ at h1
    rw [wAct_genK_decW 0 (Native.actD 22 RI[i]! n)] at h1
    exact decW_injective (xorSel_lt _ _ fun j hj => actD_RI_lt hj n)
      (actD_lt n6RowArr_zero_lt _) h1.symm
  have h := checkI_unique n hn hS hgen
  subst h
  exact Subtype.ext hzn.symm

end Ident

theorem q20P_eq_sum (t : Fin 20) :
    q20P t = ∑ j ∈ Finset.range 21, if u20MaskI[(t : ℕ)]!.testBit j then bI j else 0 :=
  eq_sum_ite (fun j hj => coe_bI hj) (by rw [u20Basis_eq_xorSel t t.2]; rfl)

set_option maxHeartbeats 400000 in
theorem exists_decomp (x : sigmaPerp) :
    ∃ (c : Fin 20 → ZMod 2) (a : ZMod 2), x = ∑ t, c t • q20P t + a • sigmaP := by
  obtain ⟨c, hc⟩ : ∃ c : Fin 20 → ZMod 2, ∑ t, c t • b20 t = Submodule.Quotient.mk x :=
    ⟨b20.repr (Submodule.Quotient.mk x), b20.sum_repr _⟩
  have hmk : (Submodule.Quotient.mk x : W20) =
      Submodule.Quotient.mk (∑ t, c t • q20P t) := by
    rw [show (Submodule.Quotient.mk (∑ t, c t • q20P t) : W20) =
        ∑ t, Submodule.Quotient.mk (c t • q20P t) from map_sum sigLine.mkQ _ _, ← hc]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [b20_apply, b20v, Submodule.Quotient.mk_smul]
  have hxy : x - ∑ t, c t • q20P t ∈ sigLine := (Submodule.Quotient.eq sigLine).1 hmk
  rw [Unitary.sigLine, Submodule.mem_span_singleton] at hxy
  obtain ⟨a, ha⟩ := hxy
  exact ⟨c, a, (sub_eq_iff_eq_add'.1 ha.symm)⟩

set_option maxHeartbeats 1000000 in
theorem eq_id_of_intertwine {A : Module.End (ZMod 2) sigmaPerp}
    (hA : ∀ u x, A (rhoU u x) = rhoU u (A x)) (hσ : A sigmaP = sigmaP) (x : sigmaPerp) :
    A x = x := by
  have hbI : ∀ j < 21, A (bI j) = bI j := fun j hj => by
    rw [bI, intertwine_word_id hA (cycWordsI_inner j hj), A_v0I hA hσ]
  have hq : ∀ t, A (q20P t) = q20P t := fun t => by
    rw [q20P_eq_sum, map_sum_ite]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hbI j (Finset.mem_range.1 hj)]
  obtain ⟨c, a, hx⟩ := exists_decomp x
  have hs : A (∑ t, c t • q20P t) = ∑ t, c t • q20P t := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [map_smul, hq t]
  rw [hx, map_add, map_smul, hs, hσ]

end CFSG.EvenSmallLie.TwoE6.Stroth23Inner
