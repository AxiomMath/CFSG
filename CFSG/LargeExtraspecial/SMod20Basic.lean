module

public import Certificates.Certificate21260

public section

namespace CFSG.LargeExtraspecial.SMod20

open CFSG.SmithE CFSG.F4.Native

abbrev V := Fin 20 → ZMod 2

@[expose] def decode (c : Nat) : V := fun m => if c.testBit m.val then 1 else 0

theorem decode_apply (c : Nat) (m : Fin 20) : decode c m = if c.testBit m.val then 1 else 0 :=
  rfl

theorem decode_xor (a b : Nat) : decode (a ^^^ b) = decode a + decode b := by
  funext m
  simp only [decode_apply, Pi.add_apply, Nat.testBit_xor]
  cases a.testBit m.val <;> cases b.testBit m.val <;> decide

theorem decode_zero : decode 0 = 0 := by
  funext m
  simp [decode_apply]

theorem decode_two_pow (m : Fin 20) : decode (2 ^ m.val) = Pi.single m 1 := by
  funext i
  rw [decode_apply, Nat.testBit_two_pow, Pi.single_apply]
  by_cases h : i = m
  · subst h; simp
  · have : m.val ≠ i.val := fun e => h (Fin.ext e.symm)
    simp [h, this]

theorem eq_of_decode_eq {a b : Nat} (ha : a < 2 ^ 20) (hb : b < 2 ^ 20)
    (h : decode a = decode b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 20
  · have := congrFun h ⟨i, hi⟩
    simp only [decode_apply] at this
    cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num)
      (by omega))), Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right
      (by norm_num) (by omega)))]

@[expose] noncomputable def colsLin (cols : Array Nat) : V →ₗ[ZMod 2] V :=
  ∑ m : Fin 20, (LinearMap.proj m : V →ₗ[ZMod 2] ZMod 2).smulRight (decode cols[m.val]!)

theorem colsLin_apply (cols : Array Nat) (v : V) :
    colsLin cols v = ∑ m : Fin 20, v m • decode cols[m.val]! := by
  simp [colsLin, LinearMap.sum_apply]

theorem colsLin_single (cols : Array Nat) (m : Fin 20) :
    colsLin cols (Pi.single m 1) = decode cols[m.val]! := by
  rw [colsLin_apply, Finset.sum_eq_single m]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem decode_foldl (cols : Array Nat) (c : Nat) (n : Nat) :
    decode ((List.range n).foldl (fun acc m => if c.testBit m then acc ^^^ cols[m]! else acc) 0) =
      ∑ m ∈ Finset.range n, if c.testBit m then decode cols[m]! else 0 := by
  induction n with
  | zero => simp [decode_zero]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← ih]
    simp only [List.foldl_cons, List.foldl_nil]
    split_ifs
    · rw [decode_xor]
    · rw [add_zero]

theorem decode_applyCols {cols : Array Nat} (h : cols.size = 20) (c : Nat) :
    decode (applyCols cols c) = colsLin cols (decode c) := by
  unfold applyCols
  rw [h, decode_foldl, colsLin_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun m => if c.testBit m then decode cols[m]! else 0) 20]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [decode_apply]
  split_ifs <;> simp

theorem linearMap_ext_single {f g : V →ₗ[ZMod 2] V}
    (h : ∀ m : Fin 20, f (Pi.single m 1) = g (Pi.single m 1)) : f = g :=
  (Pi.basisFun (ZMod 2) (Fin 20)).ext fun m => by rw [Pi.basisFun_apply]; exact h m

theorem size_tvCols (k : Nat) : (tvCols k).size = 20 := by
  simp [tvCols]

theorem tvArr_get {k : Nat} (hk : k < 693) : tvArr[k]! = tvCols k := by
  simp [tvArr, getElem!_pos, hk]

theorem wtArr_get {i : Nat} (hi : i < 891) : wtArr[i]! = wt i := by
  simp [wtArr, getElem!_pos, hi]

@[expose] noncomputable def tvLin (k : Nat) : V →ₗ[ZMod 2] V := colsLin (tvCols k)

theorem tvLin_decode (k c : Nat) : tvLin k (decode c) = decode (applyCols (tvCols k) c) :=
  (decode_applyCols (size_tvCols k) c).symm

theorem tvLin_single (k : Nat) (m : Fin 20) :
    tvLin k (Pi.single m 1) = decode (tvCols k)[m.val]! :=
  colsLin_single _ m

theorem tvInvCheck_holds : chkTvInv = true :=
  Certificates.certificate21260.1

theorem tvConjCheck_holds : chkTvConj = true :=
  Certificates.certificate21260.2.1

theorem ptWordsCheck_holds : chkPtWords = true :=
  Certificates.certificate21260.2.2.1

theorem pairWordsCheck_holds : chkPairWords = true :=
  Certificates.certificate21260.2.2.2.1

theorem planeWordsCheck_holds : chkPlaneWords = true :=
  Certificates.certificate21260.2.2.2.2.1

theorem twCheck_holds : chkTW = true :=
  Certificates.certificate21260.2.2.2.2.2.1

theorem planesCheck_holds : chkPlanes = true :=
  Certificates.certificate21260.2.2.2.2.2.2.1

theorem gramCheck_holds : chkGram = true :=
  Certificates.certificate21260.2.2.2.2.2.2.2.1

theorem formInvCheck_holds : chkFormInv = true :=
  Certificates.certificate21260.2.2.2.2.2.2.2.2

theorem tvInv_parts {k : Nat} (hk : k < 693) :
    ∀ m < 20, (tvCols k)[m]! < 2 ^ 20 ∧ applyCols (tvCols k) (tvCols k)[m]! = 2 ^ m := by
  have h := tvInvCheck_holds
  simp only [chkTvInv, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨-, h2⟩ := h k hk
  rw [tvArr_get hk] at h2
  exact h2

theorem tvLin_tvLin {k : Nat} (hk : k < 693) (v : V) :
    tvLin k (tvLin k v) = v := by
  have : tvLin k ∘ₗ tvLin k = LinearMap.id := by
    apply linearMap_ext_single
    intro m
    rw [LinearMap.comp_apply, LinearMap.id_apply, tvLin_single, tvLin_decode,
      (tvInv_parts hk m m.2).2, decode_two_pow]
  exact LinearMap.congr_fun this v

@[expose] noncomputable def tvEquiv (k : Nat) :
    V ≃ₗ[ZMod 2] V :=
  if hk : k < 693 then LinearEquiv.ofInvolutive (tvLin k) (tvLin_tvLin hk)
  else LinearEquiv.refl (ZMod 2) V

theorem tvEquiv_apply {k : Nat} (hk : k < 693) (v : V) :
    tvEquiv k v = tvLin k v := by
  simp only [tvEquiv, hk, ↓reduceDIte]
  rfl

theorem tvEquiv_decode {k : Nat} (hk : k < 693) (c : Nat) :
    tvEquiv k (decode c) = decode (applyCols (tvCols k) c) := by
  rw [tvEquiv_apply hk, tvLin_decode]

theorem tvEquiv_single {k : Nat} (hk : k < 693) (m : Fin 20) :
    tvEquiv k (Pi.single m 1) = decode (tvCols k)[m.val]! := by
  rw [tvEquiv_apply hk, tvLin_single]

theorem linearEquiv_ext_single {f g : V ≃ₗ[ZMod 2] V}
    (h : ∀ m : Fin 20, f (Pi.single m 1) = g (Pi.single m 1)) : f = g :=
  LinearEquiv.toLinearMap_injective (linearMap_ext_single h)

theorem tvEquiv_mul_self {k : Nat} (hk : k < 693) :
    tvEquiv k * tvEquiv k = 1 := by
  ext v
  rw [LinearEquiv.mul_apply, tvEquiv_apply hk, tvEquiv_apply hk, tvLin_tvLin hk]
  rfl

theorem tvEquiv_inv {k : Nat} (hk : k < 693) :
    (tvEquiv k)⁻¹ = tvEquiv k :=
  inv_eq_of_mul_eq_one_right (tvEquiv_mul_self hk)

theorem tvConj_parts {j a : Nat} (hj : j < 693) (ha : a < 693) :
    ptImg j a < 693 ∧ ∀ m < 20, applyCols (tvCols j) (applyCols (tvCols a) (tvCols j)[m]!) =
      (tvCols (ptImg j a))[m]! := by
  have h := tvConjCheck_holds
  simp only [chkTvConj, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨hb, h2⟩ := h j hj a ha
  rw [tvArr_get hj, tvArr_get ha, tvArr_get hb] at h2
  exact ⟨hb, h2⟩

theorem ptImg_lt {j a : Nat} (hj : j < 693) (ha : a < 693) :
    ptImg j a < 693 :=
  (tvConj_parts hj ha).1

theorem tvEquiv_conj {j a : Nat} (hj : j < 693) (ha : a < 693) :
    tvEquiv j * tvEquiv a * tvEquiv j = tvEquiv (ptImg j a) := by
  obtain ⟨hb, h2⟩ := tvConj_parts hj ha
  apply linearEquiv_ext_single
  intro m
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, tvEquiv_single hj, tvEquiv_decode ha,
    tvEquiv_decode hj, h2 m m.2, tvEquiv_single hb]

theorem tvEquiv_conj_inv {j a : Nat} (hj : j < 693)
    (ha : a < 693) : tvEquiv j * tvEquiv a * (tvEquiv j)⁻¹ = tvEquiv (ptImg j a) := by
  rw [tvEquiv_inv hj, tvEquiv_conj hj ha]

theorem wordImg_nil (a : Nat) : wordImg [] a = a := by simp [wordImg]

theorem wordImg_cons (j : Nat) (w : List Nat) (a : Nat) :
    wordImg (j :: w) a = wordImg w (ptImg j a) := by simp only [wordImg, List.foldl_cons]

theorem wordImg_lt {w : List Nat} (hw : ∀ j ∈ w, j < 693)
    {a : Nat} (ha : a < 693) : wordImg w a < 693 := by
  induction w generalizing a with
  | nil => exact ha
  | cons j w ih =>
    rw [wordImg_cons]
    exact ih (fun j' h => hw j' (List.mem_cons_of_mem _ h)) (ptImg_lt (hw j List.mem_cons_self) ha)

theorem exists_ptWord {a : Nat} (ha : a < 693) :
    ∃ w : List Nat, (∀ j ∈ w, j < 693) ∧ wordImg w a = 0 := by
  have h := ptWordsCheck_holds
  simp only [chkPtWords, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h a ha
  exact ⟨_, h1, h2⟩

theorem exists_pairWord {l : Nat} (hl : l < 693)
    (h0 : hermC uPts[0]! uPts[l]! ≠ 0) :
    ∃ w : List Nat, (∀ j ∈ w, j < 693 ∧ ptImg j 0 = 0) ∧ wordImg w l = 1 := by
  have h := pairWordsCheck_holds
  simp only [chkPairWords, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h l hl with h1 | ⟨h1, h2⟩
  · exact absurd h1 h0
  · exact ⟨_, h1, h2⟩

theorem wordImg_zero_of_fix {w : List Nat} (hw : ∀ j ∈ w, ptImg j 0 = 0) : wordImg w 0 = 0 := by
  induction w with
  | nil => exact wordImg_nil 0
  | cons j w ih =>
    rw [wordImg_cons, hw j List.mem_cons_self]
    exact ih fun j' h => hw j' (List.mem_cons_of_mem _ h)

@[expose] def planeSet (i : Nat) : Finset (Fin 693) := Finset.univ.filter fun a => inPlane i a.val

theorem mem_planeSet {i : Nat} {a : Fin 693} : a ∈ planeSet i ↔ inPlane i a.val = true := by
  simp [planeSet]

@[expose] def wtV (i : Nat) : V := decode (wt i)

theorem planePtsArr_get {i : Nat} (hi : i < 891) : planePtsArr[i]! = planePts i := by
  simp [planePtsArr, getElem!_pos, hi]

theorem ptTab_get {k a : Nat} (hk : k < 693) (ha : a < 693) : (ptTab[k]!)[a]! = ptImg k a := by
  simp [ptTab, getElem!_pos, hk, ha]

theorem mem_planePts {i a : Nat} : a ∈ planePts i ↔ a < 693 ∧ inPlane i a = true := by
  simp [planePts, List.mem_filter]

theorem card_planeSet_eq (i : Nat) : (planeSet i).card = (planePts i).size := by
  have h : (planeSet i).map Fin.valEmbedding = (Finset.range 693).filter (inPlane i ·) := by
    ext a
    simp only [Finset.mem_map, mem_planeSet, Fin.valEmbedding_apply, Finset.mem_filter,
      Finset.mem_range]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.2, hb⟩
    · rintro ⟨ha, hb⟩
      exact ⟨⟨a, ha⟩, hb, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, h, Finset.card_def, Finset.filter_val,
    Finset.range_val, Multiset.range, Multiset.filter_coe, Multiset.coe_card]
  simp [planePts]

theorem card_planeSet {i : Nat} (hi : i < 891) :
    (planeSet i).card = 21 := by
  have h := planesCheck_holds
  simp only [chkPlanes, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  rw [card_planeSet_eq, ← planePtsArr_get hi]
  exact h.1 i hi

theorem planePts_congr {i j : Nat} (h : planeSet i = planeSet j) : planePts i = planePts j := by
  unfold planePts
  refine congrArg List.toArray (List.filter_congr fun a ha => ?_)
  have ha' : a < 693 := List.mem_range.mp ha
  have := congrArg (fun S => (⟨a, ha'⟩ : Fin 693) ∈ S) h
  simp only [mem_planeSet, eq_iff_iff] at this
  exact Bool.eq_iff_iff.mpr this

theorem planeSet_injective {i j : Nat} (hi : i < 891)
    (hj : j < 891) (h : planeSet i = planeSet j) : i = j := by
  have hc := planesCheck_holds
  simp only [chkPlanes, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq] at hc
  have he := planePts_congr h
  rcases lt_trichotomy i j with hlt | rfl | hlt
  · exact absurd (by rw [planePtsArr_get hi, planePtsArr_get hj, he]) (hc.2 j hj i hlt)
  · rfl
  · exact absurd (by rw [planePtsArr_get hi, planePtsArr_get hj, he]) (hc.2 i hi j hlt)

theorem tw_parts {k i : Nat} (hk : k < 693) (hi : i < 891) :
    planeImg k i < 891 ∧ wt (planeImg k i) = applyCols (tvCols k) (wt i) ∧
      ∀ a < 693, inPlane i a = true → inPlane (planeImg k i) (ptImg k a) = true := by
  have h := twCheck_holds
  simp only [chkTW, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, Array.all_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h k hk i hi
  rw [wtArr_get h1, wtArr_get hi, tvArr_get hk] at h2
  refine ⟨h1, h2, fun a ha hai => ?_⟩
  have := h3 a (by rw [planePtsArr_get hi]; exact mem_planePts.mpr ⟨ha, hai⟩)
  rwa [ptTab_get hk ha] at this

theorem tvEquiv_wtV {k i : Nat} (hk : k < 693) (hi : i < 891) :
    tvEquiv k (wtV i) = wtV (planeImg k i) := by
  rw [wtV, wtV, tvEquiv_decode hk, (tw_parts hk hi).2.1]

theorem planeWordImg_nil (i : Nat) : planeWordImg [] i = i := by simp [planeWordImg]

theorem planeWordImg_cons (k : Nat) (w : List Nat) (i : Nat) :
    planeWordImg (k :: w) i = planeWordImg w (planeImg k i) := by
  simp only [planeWordImg, List.foldl_cons]

theorem exists_planeWord {i : Nat} (hi : i < 891) :
    ∃ w : List Nat, (∀ k ∈ w, k < 693) ∧ planeWordImg w i = 0 := by
  have h := planeWordsCheck_holds
  simp only [chkPlaneWords, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h i hi
  exact ⟨_, h1, h2⟩

@[expose] def Opp (i j : Nat) : Prop := Disjoint (planeSet i) (planeSet j)

theorem oppB_iff {i j : Nat} (hi : i < 891) : oppB i j = true ↔ Opp i j := by
  rw [oppB, planePtsArr_get hi, Array.all_eq_true, Opp, Finset.disjoint_left]
  constructor
  · intro h a hai haj
    rw [mem_planeSet] at hai haj
    have hm : a.val ∈ planePts i := mem_planePts.mpr ⟨a.2, hai⟩
    obtain ⟨n, hn, hna⟩ := Array.mem_iff_getElem.mp hm
    have := h n hn
    rw [hna, haj] at this
    exact absurd this (by decide)
  · intro h n hn
    have hm : (planePts i)[n] ∈ planePts i := Array.getElem_mem hn
    obtain ⟨ha, hai⟩ := mem_planePts.mp hm
    have := h (a := ⟨_, ha⟩) (mem_planeSet.mpr hai)
    rw [mem_planeSet] at this
    simpa using this

@[expose] def fVal (v w : V) : ZMod 2 :=
  ∑ k : Fin 10, (v ⟨2 * k.val, by omega⟩ * w ⟨2 * k.val + 1, by omega⟩ +
    v ⟨2 * k.val + 1, by omega⟩ * w ⟨2 * k.val, by omega⟩)

@[expose] noncomputable def fModel : LinearMap.BilinForm (ZMod 2) V :=
  LinearMap.mk₂ (ZMod 2) fVal
    (fun v v' w => by
      simp only [fVal, Pi.add_apply, add_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun c v w => by
      simp only [fVal, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun v w w' => by
      simp only [fVal, Pi.add_apply, mul_add, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun c v w => by
      simp only [fVal, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring)

theorem fModel_apply (v w : V) : fModel v w = fVal v w := rfl

@[expose] def bit (b : Bool) : ZMod 2 := if b then 1 else 0

theorem bit_xor (a b : Bool) : bit (a ^^ b) = bit a + bit b := by
  cases a <;> cases b <;> decide

theorem bit_and (a b : Bool) : bit (a && b) = bit a * bit b := by
  cases a <;> cases b <;> decide

theorem bit_foldl (g : Nat → Bool) (n : Nat) :
    bit ((List.range n).foldl (fun acc k => acc ^^ g k) false) =
      ∑ k ∈ Finset.range n, bit (g k) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← ih]
    simp only [List.foldl_cons, List.foldl_nil, bit_xor]

theorem decode_apply_bit (c : Nat) (m : Fin 20) : decode c m = bit (c.testBit m.val) := rfl

theorem fModel_decode (u v : Nat) : fModel (decode u) (decode v) = bit (fB u v) := by
  rw [fModel_apply, fVal, fB, bit_foldl, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [decode_apply_bit, bit_xor, bit_and]

open Classical in
theorem fModel_wtV {i j : Nat} (hi : i < 891) (hj : j < 891) :
    fModel (wtV i) (wtV j) = if Opp i j then 1 else 0 := by
  have h := gramCheck_holds
  simp only [chkGram, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have e := h i hi j hj
  rw [wtArr_get hi, wtArr_get hj] at e
  rw [wtV, wtV, fModel_decode, e]
  by_cases ho : Opp i j
  · simp only [ho, ↓reduceIte, (oppB_iff hi).mpr ho]
    rfl
  · have : oppB i j = false := by
      cases hb : oppB i j
      · rfl
      · exact absurd ((oppB_iff hi).mp hb) ho
    simp only [ho, ↓reduceIte, this]
    rfl

theorem fModel_tvEquiv {k : Nat} (hk : k < 693) (v w : V) :
    fModel (tvEquiv k v) (tvEquiv k w) = fModel v w := by
  have h := formInvCheck_holds
  simp only [chkFormInv, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have key : fModel.compl₁₂ (tvEquiv k : V →ₗ[ZMod 2] V) (tvEquiv k : V →ₗ[ZMod 2] V) =
      fModel := by
    refine LinearMap.ext_basis (Pi.basisFun (ZMod 2) (Fin 20)) (Pi.basisFun (ZMod 2) (Fin 20))
      fun a b => ?_
    simp only [LinearMap.compl₁₂_apply, Pi.basisFun_apply, LinearEquiv.coe_coe]
    rw [tvEquiv_single hk, tvEquiv_single hk, fModel_decode, ← decode_two_pow, ← decode_two_pow,
      fModel_decode]
    have e := h k hk a a.2 b b.2
    rw [tvArr_get hk] at e
    rw [e]
  have := congrArg (fun B : LinearMap.BilinForm (ZMod 2) V => B v w) key
  simpa using this

theorem fModel_single_odd (v : V) (k : Fin 10) :
    fModel v (Pi.single ⟨2 * k.val + 1, by omega⟩ 1) = v ⟨2 * k.val, by omega⟩ := by
  rw [fModel_apply, fVal, Finset.sum_eq_single k]
  · simp [Fin.ext_iff]
  · intro b _ hb
    have h1 : (⟨2 * b.val + 1, by omega⟩ : Fin 20) ≠ ⟨2 * k.val + 1, by omega⟩ := by
      intro h
      exact hb (Fin.ext (by simp [Fin.ext_iff] at h; omega))
    have h2 : (⟨2 * b.val, by omega⟩ : Fin 20) ≠ ⟨2 * k.val + 1, by omega⟩ := by
      intro h
      simp [Fin.ext_iff] at h
      omega
    simp [h1, h2]
  · simp

theorem fModel_single_even (v : V) (k : Fin 10) :
    fModel v (Pi.single ⟨2 * k.val, by omega⟩ 1) = v ⟨2 * k.val + 1, by omega⟩ := by
  rw [fModel_apply, fVal, Finset.sum_eq_single k]
  · simp [Fin.ext_iff]
  · intro b _ hb
    have h1 : (⟨2 * b.val, by omega⟩ : Fin 20) ≠ ⟨2 * k.val, by omega⟩ := by
      intro h
      exact hb (Fin.ext (by simp [Fin.ext_iff] at h; omega))
    have h2 : (⟨2 * b.val + 1, by omega⟩ : Fin 20) ≠ ⟨2 * k.val, by omega⟩ := by
      intro h
      simp [Fin.ext_iff] at h
      omega
    simp [h1, h2]
  · simp

theorem fModel_nondegenerate {v : V} (h : ∀ w, fModel v w = 0) : v = 0 := by
  funext m
  obtain ⟨k, hk | hk⟩ : ∃ k : Fin 10, m.val = 2 * k.val ∨ m.val = 2 * k.val + 1 := by
    refine ⟨⟨m.val / 2, by omega⟩, ?_⟩
    simp only
    omega
  · have := h (Pi.single ⟨2 * k.val + 1, by omega⟩ 1)
    rw [fModel_single_odd] at this
    rw [show m = ⟨2 * k.val, by omega⟩ from Fin.ext hk, this]
    rfl
  · have := h (Pi.single ⟨2 * k.val, by omega⟩ 1)
    rw [fModel_single_even] at this
    rw [show m = ⟨2 * k.val + 1, by omega⟩ from Fin.ext hk, this]
    rfl

end CFSG.LargeExtraspecial.SMod20
