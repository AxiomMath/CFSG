module

public import Certificates.Data.Kernel.U4FFLoc
public import CFSG.HardMathSupport.U4FF.ClassLocCheck

public section

namespace CFSG.KC.U4FFLoc

open CFSG.HardMathSupport.U4FF Finset

theorem getD_toList (A : Array ℕ) (j : ℕ) : A.getD j 0 = A.toList.getD j 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem foldl_applyL (L : List ℕ) : ∀ (v acc : ℕ),
    (List.range L.length).foldl
        (fun acc j => acc ^^^ (if v.testBit j then L.getD j 0 else 0)) acc = acc ^^^ applyL L v := by
  induction L with
  | nil => intro v acc; simp [applyL]
  | cons a L ih =>
    intro v acc
    rw [List.length_cons, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    have h : ∀ j, v.testBit (j + 1) = (v / 2).testBit j := fun j => Nat.testBit_succ v j
    simp only [h, List.getD_cons_succ, List.getD_cons_zero]
    rw [ih, applyL, Nat.xor_assoc, Nat.testBit_zero]
    simp

theorem apply_eq (A : MCols) (v : ℕ) : MCols.apply A v = applyL A.toList v := by
  unfold MCols.apply
  simp only [getD_toList, ← Array.length_toList]
  rw [foldl_applyL, Nat.zero_xor]

theorem toList_mul (A B : MCols) : (MCols.mul A B).toList = mulL A.toList B.toList := by
  unfold MCols.mul mulL
  rw [Array.toList_map]
  congr 1
  funext v
  exact apply_eq A v

theorem toList_add (A B : MCols) : (MCols.add A B).toList = addL A.toList B.toList := by
  simp [MCols.add, addL, Array.toList_zipWith]

theorem toList_one (m : ℕ) : (MCols.one m).toList = oneL m := by
  apply List.ext_getElem <;> simp [MCols.one, oneL]

theorem toList_zero (m : ℕ) : (MCols.zero m).toList = zeroL m := by
  simp [MCols.zero, zeroL]

theorem toList_col (v : ℕ) : (MCols.col v).toList = [v] := rfl

theorem toList_zrowOf (n zeta : ℕ) : (zrowOf n zeta).toList = zrowL n zeta := by
  apply List.ext_getElem <;> simp [zrowOf, zrowL]

theorem bitF_ite (c : Prop) [Decidable c] (a x : ℕ) :
    bitF (if c then a else 0) x = if c then bitF a x else 0 := by
  split_ifs <;> simp [bitF_zero]

theorem bitF_ite_zero (c : Prop) [Decidable c] (a x : ℕ) :
    bitF (if c then 0 else a) x = if c then 0 else bitF a x := by
  split_ifs <;> simp [bitF_zero]

theorem bitF_shiftLeft (a d x : ℕ) : bitF (a <<< d) x = if x < d then 0 else bitF a (x - d) := by
  unfold bitF
  rw [Nat.testBit_shiftLeft]
  by_cases h : x < d
  · simp [h]
  · simp [h, Nat.le_of_not_lt h]

theorem bitF_one_shiftLeft (b x : ℕ) : bitF (1 <<< b) x = if x = b then 1 else 0 := by
  unfold bitF
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : x = b
  · simp [h]
  · simp [h, Ne.symm h]

theorem bitF_div_two (a k : ℕ) : bitF (a / 2) k = bitF a (k + 1) := by
  unfold bitF
  rw [Nat.testBit_succ]

theorem bitF_zero_eq (a : ℕ) : bitF a 0 = if a % 2 = 1 then 1 else 0 := by
  unfold bitF
  rw [Nat.testBit_zero]
  simp

theorem eq_of_bitF (a b : ℕ) (h : ∀ x, bitF a x = bitF b x) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro x
  have hx := h x
  unfold bitF at hx
  cases ha : a.testBit x <;> cases hb : b.testBit x <;> simp_all

theorem bitF_foldl_set (p : ℕ → Prop) [DecidablePred p] (i : ℕ) :
    ∀ (L : List ℕ) (acc : ℕ),
      bitF (L.foldl (fun acc a => if p a then acc ||| (1 <<< a) else acc) acc) i =
        if i ∈ L ∧ p i then 1 else bitF acc i := by
  intro L
  induction L with
  | nil => intro acc; simp
  | cons x L ih =>
    intro acc
    rw [List.foldl_cons, ih]
    by_cases hi : i = x
    · subst hi
      by_cases hP : p i
      · simp [hP, bitF_or_shift]
      · simp [hP]
    · by_cases hx : p x
      · simp [hx, hi, bitF_or_shift]
      · simp [hx, hi]

theorem kronCol_bit (d ca : ℕ) (hd : 0 < d) (hca : ∀ a, d ≤ a → bitF ca a = 0) :
    ∀ (n cb x : ℕ), bitF (kronCol d ca n cb) x =
      if x / d < n then bitF cb (x / d) * bitF ca (x % d) else 0 := by
  intro n
  induction n with
  | zero => intro cb x; simp [kronCol, bitF_zero]
  | succ n ih =>
    intro cb x
    rw [kronCol, bitF_xor, bitF_ite, bitF_shiftLeft]
    by_cases hx : x < d
    · have h1 : x / d = 0 := Nat.div_eq_of_lt hx
      have h2 : x % d = x := Nat.mod_eq_of_lt hx
      rw [if_pos hx, h1, h2, bitF_zero_eq]
      by_cases hc : cb % 2 = 1 <;> simp [hc]
    · obtain ⟨y, rfl⟩ : ∃ y, x = y + d := ⟨x - d, by omega⟩
      rw [if_neg hx, hca (y + d) (by omega), Nat.add_sub_cancel, ih, Nat.add_div_right y hd,
        Nat.add_mod_right, bitF_div_two]
      by_cases hc : cb % 2 = 1
      · simp [hc]
      · simp [hc]

def Rep (L : List ℕ) (N : ℕ) (M : ℕ → ℕ → ZMod 2) : Prop :=
  L.length = N ∧ ∀ y < N, ∀ x, bitF (L.getD y 0) x = if x < N then M x y else 0

theorem Rep.eq {L L' : List ℕ} {N : ℕ} {M : ℕ → ℕ → ZMod 2} (h : Rep L N M) (h' : Rep L' N M) :
    L = L' := by
  apply List.ext_getElem (h.1.trans h'.1.symm)
  intro y hy hy'
  have hyN : y < N := h.1 ▸ hy
  apply eq_of_bitF
  intro x
  have e1 := h.2 y hyN x
  have e2 := h'.2 y hyN x
  rw [List.getD_eq_getElem _ _ hy] at e1
  rw [List.getD_eq_getElem _ _ hy'] at e2
  rw [e1, e2]

def entD : List FK → Fin 4 → Fin 4 → ℕ → ℕ → ℕ → ZMod 2
  | [], _, _, r, _, _ => if r = 0 then 1 else 0
  | K :: fs, i, j, r, x, y =>
    (if x % K.dim = y % K.dim then 1 else 0) * entD fs i j r (x / K.dim) (y / K.dim) +
      (if r = 0 then 0 else
        derN K i j (x % K.dim) (y % K.dim) * entD fs i j (r - 1) (x / K.dim) (y / K.dim))

theorem FK.dim_pos (K : FK) : 0 < K.dim := by cases K <;> decide

theorem dimL_cons (K : FK) (fs : List FK) : dimL (K :: fs) = K.dim * dimL fs := by
  simp [dimL]

theorem dimL_eq (fs : List FK) : dimL fs = ambDim fs := by
  induction fs with
  | nil => simp [dimL, ambDim]
  | cons K fs ih => simp [dimL_cons, ih, ambDim, Fin.prod_univ_succ]

theorem derL_rep (K : FK) (i j : Fin 4) (b : ℕ) (hb : b < K.dim) (a : ℕ) :
    bitF ((derL K i j).getD b 0) a = derN K i j a b := by
  have hlen : b < (derL K i j).length := by simp [derL, hb]
  rw [List.getD_eq_getElem _ _ hlen]
  simp only [derL, List.getElem_map, List.getElem_range]
  rw [bitF_foldl_set, bitF_zero]
  by_cases ha : a < K.dim
  · simp only [List.mem_range, ha, true_and]
    split_ifs with h
    · exact h.symm
    · revert h
      generalize derN K i j a b = z
      revert z
      decide
  · have h0 : derN K i j a b = 0 := by simp [derN, ha]
    simp [ha, h0]

theorem tabDK_rep (i j : Fin 4) :
    ∀ (fs : List FK) (r : ℕ), Rep (tabDK fs i j r) (dimL fs) (entD fs i j r)
  | [], r => by
    refine ⟨rfl, fun y hy x => ?_⟩
    have hy0 : y = 0 := by simp [dimL] at hy; omega
    subst hy0
    rcases x with _ | x
    · by_cases hr : r = 0 <;> simp [tabDK, entD, dimL, hr, bitF, Nat.testBit_zero]
    · have h1 : ¬ (x + 1 < dimL []) := by simp [dimL]
      rw [if_neg h1]
      by_cases hr : r = 0 <;> simp [tabDK, hr, bitF, Nat.testBit_succ]
  | K :: fs, r => by
    have hP := tabDK_rep i j fs r
    have hQ := tabDK_rep i j fs (r - 1)
    have hd := FK.dim_pos K
    refine ⟨by simp [tabDK, kronStep, dimL_cons], fun y hy x => ?_⟩
    rw [dimL_cons] at hy ⊢
    have hlen : y < (tabDK (K :: fs) i j r).length := by simp [tabDK, kronStep, hy]
    have hyd : y / K.dim < dimL fs := by
      rw [Nat.div_lt_iff_lt_mul hd]
      rw [Nat.mul_comm]
      exact hy
    have hym : y % K.dim < K.dim := Nat.mod_lt _ hd
    rw [List.getD_eq_getElem _ _ hlen]
    simp only [tabDK, kronStep, List.getElem_map, List.getElem_range]
    rw [bitF_xor, bitF_ite_zero,
      kronCol_bit _ _ hd (fun a ha => by rw [bitF_one_shiftLeft, if_neg (by omega)]),
      kronCol_bit _ _ hd (fun a ha => by
        rw [derL_rep K i j _ hym]
        simp [derN, Nat.not_lt.mpr ha])]
    rw [hP.2 _ hyd, hQ.2 _ hyd, bitF_one_shiftLeft, derL_rep K i j _ hym]
    have hxd : x < K.dim * dimL fs ↔ x / K.dim < dimL fs := by
      rw [Nat.div_lt_iff_lt_mul hd, Nat.mul_comm]
    by_cases hx : x / K.dim < dimL fs
    · rw [if_pos (hxd.mpr hx), if_pos hx, if_pos hx, if_pos hx, entD]
      by_cases hr : r = 0
      · simp [hr, mul_comm]
      · simp [hr, mul_comm, Nat.not_le.mpr hx]
    · rw [if_neg (fun h => hx (hxd.mp h)), if_neg hx, if_neg hx]
      simp

theorem sum_split {R : Type*} [CommRing R] {m : ℕ} (r : ℕ) (D I : Fin (m + 1) → R) :
    ∑ S ∈ (univ : Finset (Finset (Fin (m + 1)))).filter (fun S => S.card = r),
        ∏ f, (if f ∈ S then D f else I f) =
      I 0 * ∑ T ∈ (univ : Finset (Finset (Fin m))).filter (fun T => T.card = r),
          ∏ f, (if f ∈ T then D f.succ else I f.succ) +
      (if r = 0 then 0 else D 0 * ∑ T ∈ (univ : Finset (Finset (Fin m))).filter
          (fun T => T.card = r - 1), ∏ f, (if f ∈ T then D f.succ else I f.succ)) := by
  have hf : ∀ (n k : ℕ), (univ : Finset (Finset (Fin n))).filter (fun S => S.card = k) =
      powersetCard k univ := by
    intro n k
    ext S
    simp [mem_powersetCard_univ]
  rw [hf, hf, hf]
  have h1 : ∀ T : Finset (Fin m), ∏ f, (if f ∈ T.map (Fin.succEmb m) then D f else I f) =
      I 0 * ∏ f, (if f ∈ T then D f.succ else I f.succ) := by
    intro T
    rw [Fin.prod_univ_succ]
    simp [Fin.succ_ne_zero]
  have h2 : ∀ T : Finset (Fin m),
      ∏ f, (if f ∈ insert 0 (T.map (Fin.succEmb m)) then D f else I f) =
        D 0 * ∏ f, (if f ∈ T then D f.succ else I f.succ) := by
    intro T
    rw [Fin.prod_univ_succ]
    simp [Fin.succ_ne_zero]
  have hu : (univ : Finset (Fin (m + 1))) = insert 0 (univ.map (Fin.succEmb m)) := by
    ext f
    refine ⟨fun _ => ?_, fun _ => mem_univ f⟩
    refine Fin.cases (by simp) (fun g => ?_) f
    simp
  have h0 : (0 : Fin (m + 1)) ∉ univ.map (Fin.succEmb m) := by simp [Fin.succ_ne_zero]
  rcases r with _ | s
  · simp [powersetCard_zero, Fin.prod_univ_succ]
  · have hpc : powersetCard (s + 1) (univ : Finset (Fin (m + 1))) =
        powersetCard (s + 1) (insert 0 (univ.map (Fin.succEmb m))) := congrArg _ hu
    rw [hpc, powersetCard_succ_insert h0, sum_union, sum_image, powersetCard_map, powersetCard_map,
      sum_map, sum_map]
    · rw [if_neg (Nat.succ_ne_zero s), Nat.add_sub_cancel, mul_sum, mul_sum]
      congr 1
      · exact sum_congr rfl fun T _ => h1 T
      · exact sum_congr rfl fun T _ => h2 T
    · intro A hA B hB hAB
      have hA0 : (0 : Fin (m + 1)) ∉ A := fun h => h0 ((mem_powersetCard.mp hA).1 h)
      have hB0 : (0 : Fin (m + 1)) ∉ B := fun h => h0 ((mem_powersetCard.mp hB).1 h)
      have := congrArg (fun S => S.erase 0) hAB
      simpa [erase_insert hA0, erase_insert hB0] using this
    · rw [disjoint_left]
      intro S hS hS'
      obtain ⟨T, -, rfl⟩ := mem_image.mp hS'
      exact h0 ((mem_powersetCard.mp hS).1 (mem_insert_self 0 T))

theorem ambD_apply (fs : List FK) (i j : Fin 4) (r : ℕ) (u v : AmbIdx fs) :
    ambD fs i j r u v = ∑ S ∈ (univ : Finset (Finset (Fin fs.length))).filter
        (fun S => S.card = r),
      ∏ f, (if f ∈ S then derK (fs.get f) i j (u f) (v f) else
        (1 : Matrix (Fin (fs.get f).dim) (Fin (fs.get f).dim) (ZMod 2)) (u f) (v f)) := by
  simp only [ambD, ambZ, Matrix.sum_apply, kronDep_apply]
  refine sum_congr rfl fun S _ => prod_congr rfl fun f _ => ?_
  split_ifs <;> rfl

theorem ambEq_cons (K : FK) (fs : List FK) (u : AmbIdx (K :: fs)) :
    (ambEq (K :: fs) u : ℕ) = (u 0 : ℕ) + K.dim * (ambEq fs (fun f => u f.succ) : ℕ) := by
  simp only [ambEq, finPiFinEquiv_apply]
  erw [Fin.sum_univ_succ (n := fs.length)]
  rw [Finset.mul_sum]
  congr 1
  · rw [Finset.prod_eq_one, mul_one]
    intro j _
    exact absurd j.isLt (by simp)
  · refine Finset.sum_congr rfl fun f _ => ?_
    have hP : ∏ j : Fin (f.succ : ℕ), ((K :: fs).get (Fin.castLE f.succ.is_lt.le j)).dim =
        K.dim * ∏ j : Fin (f : ℕ), (fs.get (Fin.castLE f.is_lt.le j)).dim := by
      rw [Fintype.prod_equiv (finCongr (Fin.val_succ f))
        (fun j => ((K :: fs).get (Fin.castLE f.succ.is_lt.le j)).dim)
        (fun j => ((K :: fs).get (Fin.castLE (Nat.succ_le_succ f.isLt.le) j)).dim) (fun j => rfl),
        Fin.prod_univ_succ]
      first
        | rfl
        | simp
    rw [hP]
    ring

theorem ambD_eq_entD (i j : Fin 4) :
    ∀ (fs : List FK) (r : ℕ) (u v : AmbIdx fs),
      ambD fs i j r u v = entD fs i j r (ambEq fs u) (ambEq fs v)
  | [], r, u, v => by
    rw [ambD_apply]
    have hU : (univ : Finset (Finset (Fin ([] : List FK).length))) = {∅} := by
      ext S
      simp only [mem_univ, mem_singleton, true_iff]
      ext f
      exact Fin.elim0 f
    rw [hU, Finset.sum_filter, Finset.sum_singleton]
    by_cases hr : r = 0
    · subst hr
      simp [entD]
    · have hr' : ¬ ((∅ : Finset (Fin ([] : List FK).length)).card = r) := by
        rw [Finset.card_empty]
        exact fun h => hr h.symm
      rw [if_neg hr']
      simp [entD, hr]
  | K :: fs, r, u, v => by
    have hE : ∀ r', ∑ T ∈ (univ : Finset (Finset (Fin fs.length))).filter (fun T => T.card = r'),
        ∏ f, (if f ∈ T then derK ((K :: fs).get f.succ) i j (u f.succ) (v f.succ) else
          (1 : Matrix (Fin ((K :: fs).get f.succ).dim) (Fin ((K :: fs).get f.succ).dim) (ZMod 2))
            (u f.succ) (v f.succ)) =
          entD fs i j r' (ambEq fs (fun f => u f.succ)) (ambEq fs (fun f => v f.succ)) := by
      intro r'
      rw [← ambD_eq_entD i j fs r' (fun f => u f.succ) (fun f => v f.succ), ambD_apply]
      rfl
    rw [ambD_apply]
    erw [sum_split r]
    rw [hE, hE, entD, ambEq_cons K fs u, ambEq_cons K fs v]
    have hd := FK.dim_pos K
    have hu0 : (u 0 : ℕ) < K.dim := (u 0).isLt
    have hv0 : (v 0 : ℕ) < K.dim := (v 0).isLt
    have e1 : ((u 0 : ℕ) + K.dim * (ambEq fs (fun f => u f.succ) : ℕ)) % K.dim = u 0 := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hu0
    have e2 : ((v 0 : ℕ) + K.dim * (ambEq fs (fun f => v f.succ) : ℕ)) % K.dim = v 0 := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hv0
    have e3 : ((u 0 : ℕ) + K.dim * (ambEq fs (fun f => u f.succ) : ℕ)) / K.dim =
        ambEq fs (fun f => u f.succ) := by
      rw [Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hu0, Nat.zero_add]
    have e4 : ((v 0 : ℕ) + K.dim * (ambEq fs (fun f => v f.succ) : ℕ)) / K.dim =
        ambEq fs (fun f => v f.succ) := by
      rw [Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hv0, Nat.zero_add]
    rw [e1, e2, e3, e4]
    have hI : (1 : Matrix (Fin ((K :: fs).get 0).dim) (Fin ((K :: fs).get 0).dim) (ZMod 2))
        (u 0) (v 0) = if (u 0 : ℕ) = v 0 then 1 else 0 := by
      rw [Matrix.one_apply]
      exact if_congr Fin.val_inj.symm rfl rfl
    have hD : derK ((K :: fs).get 0) i j (u 0) (v 0) = derN K i j (u 0) (v 0) := by
      rw [derN, dif_pos (And.intro hu0 hv0)]
      rfl
    rw [hI, hD]

theorem tabD_rep (fs : List FK) (i j : Fin 4) (r : ℕ) :
    Rep (tabD fs i j r).toList (ambDim fs) (entD fs i j r) := by
  refine ⟨by simp [tabD, tab_size], fun y hy x => ?_⟩
  have hlen : y < (tabD fs i j r).toList.length := by simp [tabD, tab_size, hy]
  rw [List.getD_eq_getElem _ _ hlen, Array.getElem_toList]
  have hcol : (tabD fs i j r)[y]'(by simpa using hlen) = (MCols.tab (ambDF fs i j r)).getD y 0 := by
    simp [tabD, Array.getD_eq_getD_getElem?, tab_size, hy]
  rw [hcol, tab_eq_tabR, getD_tabR (ambDF fs i j r) ⟨y, hy⟩]
  by_cases hx : x < ambDim fs
  · rw [if_pos hx]
    have := bitF_foldl_tab (ambDF fs i j r) ⟨y, hy⟩ ⟨x, hx⟩ (List.finRange (ambDim fs)) 0
    simp only at this
    rw [this, bitF_zero]
    simp only [List.mem_finRange, true_and]
    rw [zmod2_ite_self, ambDF, Matrix.submatrix_apply, ambD_eq_entD]
    simp
  · rw [if_neg hx]
    have key : ∀ (L : List (Fin (ambDim fs))) (acc : ℕ), bitF acc x = 0 →
        bitF (L.foldl (fun acc x' => if ambDF fs i j r x' ⟨y, hy⟩ = 1 then
          acc ||| (1 <<< (x' : ℕ)) else acc) acc) x = 0 := by
      intro L
      induction L with
      | nil => intro acc h; exact h
      | cons a L ih =>
        intro acc h
        rw [List.foldl_cons]
        apply ih
        split_ifs
        · rw [bitF_or_shift, if_neg (by omega)]
          exact h
        · exact h
    exact key _ 0 (bitF_zero x)

theorem tabDK_eq_tabD (fs : List FK) (i j : Fin 4) (r : ℕ) :
    tabDK fs i j r = (tabD fs i j r).toList := by
  have h := tabDK_rep i j fs r
  rw [dimL_eq] at h
  exact h.eq (tabD_rep fs i j r)

end CFSG.KC.U4FFLoc
