module

public import Certificates.Data.Kernel.SporSch.LyMat
public import CFSG.Certificates.Kernel.Spor.OrdSound
public import CFSG.Sporadic.Schreier.LyCheckCover
import CFSG.Certificates.Kernel.Spor.OrdCanon

public section

namespace CFSG.KS.SporSch.LyM

open CFSG.KC.Ord CFSG.KS.Ord CFSG.Sporadic.He.Native

@[expose] def unpackL (d w S X : Nat) : Array (Array Nat) :=
  Array.ofFn (n := d) fun i => Array.ofFn (n := d) fun j =>
    Nat.land (Nat.shiftRight X (S * i.val + w * j.val)) (2 ^ w - 1)

theorem ofFn_get! {α : Type} [Inhabited α] {n : Nat} (f : Fin n → α) {i : Nat} (h : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, h⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using h), Array.getElem_ofFn]

theorem land_eq (a b : Nat) : Nat.land a b = a &&& b := rfl

theorem unpackL_get {d w S X i j : Nat} (hi : i < d) (hj : j < d) :
    ((unpackL d w S X)[i]!)[j]! = X / 2 ^ (S * i + w * j) % 2 ^ w := by
  unfold unpackL
  rw [ofFn_get! _ hi, ofFn_get! _ hj, land_eq, Nat.and_two_pow_sub_one_eq_mod]
  change X >>> (S * i + w * j) % 2 ^ w = _
  rw [Nat.shiftRight_eq_div_pow]

theorem andB_true' {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem cfacts {p w S d T L H CM RM ONE LV HV : Nat}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true) :
    2 ≤ p ∧ S = d * w ∧ 0 < w ∧ p ≤ 2 ^ w := by
  unfold constsOK at hc
  obtain ⟨hp2, hc⟩ := andB_true' hc
  obtain ⟨hS, hc⟩ := andB_true' hc
  obtain ⟨-, hc⟩ := andB_true' hc
  obtain ⟨hT, -⟩ := andB_true' hc
  have hp : 2 ≤ p := Nat.le_of_ble_eq_true hp2
  have hT' : p * 2 ^ T ≤ 2 ^ (w - 1) := by
    have h : p <<< T ≤ 1 <<< (w - 1) := Nat.le_of_ble_eq_true hT
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul] at h
    exact h
  have hp' : p ≤ 2 ^ (w - 1) := Nat.le_trans (Nat.le_mul_of_pos_right p (Nat.two_pow_pos T)) hT'
  have hw : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · subst h0
      simp only [Nat.zero_sub, Nat.pow_zero] at hp'
      omega
    · exact h0
  refine ⟨hp, Nat.eq_of_beq_eq_true hS, hw, Nat.le_trans hp' (Nat.pow_le_pow_right (by norm_num) ?_)⟩
  omega

theorem canon_ent {p d w X : Nat} (hX : Canon p d w X) {i j : Nat} (hi : i < d) (hj : j < d) :
    X / 2 ^ (d * w * i + w * j) % 2 ^ w < p := by
  have e : d * w * i + w * j = w * (d * i + j) := by ring
  have h := hX.2 (d * i + j) (by nlinarith)
  unfold lane at h
  rw [e]
  exact h

theorem fold_sum (n : Nat) (g : Nat → Nat) :
    Nat.fold n (fun j _ acc => acc + g j) 0 = ∑ j ∈ Finset.range n, g j := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.fold_succ, ih, Finset.sum_range_succ]

theorem ordMat_apply (p d w S M : Nat) (i j : Fin d) :
    ordMat p d w S M i j = ((M / 2 ^ (S * i.val + w * j.val) % 2 ^ w : Nat) : ZMod p) := rfl

theorem eq_of_cast {p a b : Nat} (ha : a < p) (hb : b < p) (h : (a : ZMod p) = (b : ZMod p)) :
    a = b := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h

theorem mod_of_cast {p a b : Nat} (ha : a < p) (h : (a : ZMod p) = (b : ZMod p)) : a = b % p := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rwa [Nat.mod_eq_of_lt ha] at h

theorem mulR_eqL {p w S d T L H CM RM ONE LV HV X Y : Nat}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true)
    (hX : validM p (d * S) L H X = true) (hY : validM p (d * S) L H Y = true) :
    mulM p d (unpackL d w S X) (unpackL d w S Y) = unpackL d w S (mulR p w S d T L H CM RM X Y) ∧
      validM p (d * S) L H (mulR p w S d T L H CM RM X Y) = true := by
  obtain ⟨hp, hS, hw, hpw⟩ := cfacts hc
  have cX := validM_canon hc hX
  have cY := validM_canon hc hY
  obtain ⟨cZ, hZ⟩ := mulR_sound hc cX cY
  refine ⟨?_, CFSG.KS.OrdCanon.validM_of_canon hc cZ⟩
  unfold mulM
  conv_rhs => unfold unpackL
  refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun k => ?_))
  have hik := congrFun (congrFun hZ i) k
  rw [Matrix.mul_apply] at hik
  simp only [ordMat_apply] at hik
  unfold dot
  rw [fold_sum, land_eq, Nat.and_two_pow_sub_one_eq_mod]
  change _ = mulR p w S d T L H CM RM X Y >>> (S * i.val + w * k.val) % 2 ^ w
  rw [Nat.shiftRight_eq_div_pow]
  subst hS
  symm
  refine mod_of_cast (canon_ent cZ i.isLt k.isLt) ?_
  rw [hik, Nat.cast_sum, Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold col
  rw [ofFn_get! _ j.isLt, unpackL_get i.isLt j.isLt, unpackL_get j.isLt k.isLt, Nat.cast_mul]

theorem idM_eqL {p w S d T L H CM RM ONE LV HV : Nat}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true) :
    idM d = unpackL d w S ONE ∧ validM p (d * S) L H ONE = true := by
  obtain ⟨hp, hS, hw, hpw⟩ := cfacts hc
  obtain ⟨c1, h1⟩ := one_sound hc
  refine ⟨?_, CFSG.KS.OrdCanon.validM_of_canon hc c1⟩
  unfold idM
  conv_rhs => unfold unpackL
  refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun k => ?_))
  have hik := congrFun (congrFun h1 i) k
  rw [ordMat_apply, Matrix.one_apply] at hik
  rw [land_eq, Nat.and_two_pow_sub_one_eq_mod]
  change _ = ONE >>> (S * i.val + w * k.val) % 2 ^ w
  rw [Nat.shiftRight_eq_div_pow]
  subst hS
  symm
  refine eq_of_cast (canon_ent c1 i.isLt k.isLt) (by split <;> omega) ?_
  rw [hik]
  by_cases h : i = k
  · subst h
    simp
  · have h' : i.val ≠ k.val := fun e => h (Fin.ext e)
    simp [h, h']

theorem testBit_ent (X b w r : Nat) :
    (X / 2 ^ b % 2 ^ w).testBit r = (decide (r < w) && X.testBit (r + b)) := by
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]

theorem canon_ext {p d w X Y : Nat} (hX : Canon p d w X) (hY : Canon p d w Y)
    (h : ∀ i < d, ∀ j < d, X / 2 ^ (d * w * i + w * j) % 2 ^ w =
      Y / 2 ^ (d * w * i + w * j) % 2 ^ w) : X = Y := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < w * (d * d)
  · have hw : 0 < w := by
      rcases Nat.eq_zero_or_pos w with h0 | h0
      · subst h0
        simp at hb
      · exact h0
    have hd : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · subst h0
        simp at hb
      · exact h0
    have ht : b / w < d * d := by
      rw [Nat.div_lt_iff_lt_mul hw]
      linarith
    have hi : b / w / d < d := (Nat.div_lt_iff_lt_mul hd).2 ht
    have hj : b / w % d < d := Nat.mod_lt _ hd
    have e := h _ hi _ hj
    have eb : b = b % w + (d * w * (b / w / d) + w * (b / w % d)) := by
      have h1 := Nat.div_add_mod b w
      have h2 := Nat.div_add_mod (b / w) d
      nlinarith
    have e2 := congrArg (fun x => x.testBit (b % w)) e
    simp only [testBit_ent] at e2
    rw [← eb] at e2
    simpa [Nat.mod_lt _ hw] using e2
  · have h1 : X < 2 ^ b := Nat.lt_of_lt_of_le hX.1 (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : Y < 2 ^ b := Nat.lt_of_lt_of_le hY.1 (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_eq_false_of_lt h1, Nat.testBit_eq_false_of_lt h2]

theorem beq_eqL {p w S d T L H CM RM ONE LV HV X Y : Nat}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true)
    (hX : validM p (d * S) L H X = true) (hY : validM p (d * S) L H Y = true) :
    (unpackL d w S X == unpackL d w S Y) = Nat.beq X Y := by
  obtain ⟨hp, hS, hw, hpw⟩ := cfacts hc
  have cX := validM_canon hc hX
  have cY := validM_canon hc hY
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]
  constructor
  · intro h
    subst hS
    refine canon_ext cX cY fun i hi j hj => ?_
    have e := congrArg (fun A : Array (Array Nat) => (A[i]!)[j]!) h
    simp only [unpackL_get hi hj] at e
    exact e
  · rintro rfl
    rfl

@[expose] def pivS (p d c : Nat) (A : Array (Array Nat)) (piv r : Nat) : Nat :=
  if (piv == d && (A[r]!)[c]! % p != 0) = true then r else piv

@[expose] def pivF (p d c : Nat) (A : Array (Array Nat)) : Nat :=
  (List.range' c (d - c)).foldl (pivS p d c A) d

@[expose] def newRow (p d c : Nat) (A : Array (Array Nat)) (r : Nat) : Array Nat :=
  Array.ofFn (n := 2 * d) fun j => ((A[r]!)[j.val]! + (p - (A[r]!)[c]!) * (A[c]!)[j.val]!) % p

@[expose] def elimS (p d c : Nat) (A : Array (Array Nat)) (r : Nat) : Array (Array Nat) :=
  if (r != c) = true then
    (if ((A[r]!)[c]! != 0) = true then A.set! r (newRow p d c A r) else A)
  else A

@[expose] def swapR (A : Array (Array Nat)) (piv c : Nat) : Array (Array Nat) :=
  (A.set! piv A[c]!).set! c A[piv]!

@[expose] def scaleR (p c : Nat) (A : Array (Array Nat)) : Array (Array Nat) :=
  A.set! c (A[c]!.map fun x => x * ((A[c]!)[c]! ^ (p - 2) % p) % p)

@[expose] def stepS (p d : Nat) (A : Array (Array Nat)) (c : Nat) : Array (Array Nat) :=
  if pivF p d c A < d then
    (List.range d).foldl (elimS p d c) (scaleR p c (swapR A (pivF p d c A) c))
  else A

@[expose] def initG (p d : Nat) (X : Array (Array Nat)) : Array (Array Nat) :=
  Array.ofFn (n := d) fun i => Array.ofFn (n := 2 * d) fun j =>
    if j.val < d then (X[i.val]!)[j.val]! % p else if j.val - d = i.val then 1 else 0

@[expose] def invF (p d : Nat) (X : Array (Array Nat)) : Array (Array Nat) :=
  ((List.range d).foldl (stepS p d) (initG p d X)).map fun row => row.extract d (2 * d)

theorem ite_pure_yieldL {β : Type} (q : Prop) [Decidable q] (a b : β) :
    (if q then (pure (ForInStep.yield a) : Id (ForInStep β)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if q then a else b)) := by
  split <;> rfl

theorem invM_eq_invF (p d : Nat) (X : Array (Array Nat)) : invM p d X = invF p d X := by
  unfold invM
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', ite_pure_yieldL,
    List.forIn_pure_yield_eq_foldl, pure_bind]
  have h1 : ∀ a b : Nat, [a:b].size = b - a := fun a b => by simp [Std.Legacy.Range.size]
  simp only [h1, Nat.sub_zero, ← List.range_eq_range']
  rfl

theorem size_setR {α : Type} [Inhabited α] (A : Array α) (i : Nat) (x : α) :
    (A.set! i x).size = A.size := by
  simp [Array.set!]

theorem get_setR {α : Type} [Inhabited α] (A : Array α) (i : Nat) (x : α) {j : Nat}
    (hj : j < A.size) : (A.set! i x)[j]! = if j = i then x else A[j]! := by
  rw [getElem!_pos (A.set! i x) j (by rw [size_setR]; exact hj), getElem!_pos A j hj]
  simp only [Array.set!]
  rw [Array.getElem_setIfInBounds hj]
  by_cases h : i = j
  · subst h
    simp
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

theorem get_mapR {α β : Type} [Inhabited α] [Inhabited β] (a : Array α) (f : α → β) {j : Nat}
    (hj : j < a.size) : (a.map f)[j]! = f a[j]! := by
  rw [getElem!_pos (a.map f) j (by simpa using hj), getElem!_pos a j hj, Array.getElem_map]

theorem piv_fold (p d c : Nat) (A : Array (Array Nat)) (l : List Nat) (p0 : Nat)
    (hl : ∀ r ∈ l, r < d) :
    (l.foldl (pivS p d c A) p0 = p0 ∧ (p0 = d → ∀ r ∈ l, (A[r]!)[c]! % p = 0)) ∨
      (p0 = d ∧ l.foldl (pivS p d c A) p0 ∈ l ∧ (A[l.foldl (pivS p d c A) p0]!)[c]! % p ≠ 0) := by
  induction l generalizing p0 with
  | nil => left; simp
  | cons x l ih =>
    have hl' : ∀ r ∈ l, r < d := fun r hr => hl r (List.mem_cons_of_mem x hr)
    have hx : x < d := hl x (by simp)
    rw [List.foldl_cons]
    by_cases hp : p0 = d
    · by_cases ht : (A[x]!)[c]! % p ≠ 0
      · have e : pivS p d c A p0 x = x := by simp [pivS, hp, ht]
        rw [e]
        rcases ih x hl' with ⟨h1, _⟩ | ⟨h1, _⟩
        · right
          rw [h1]
          exact ⟨hp, by simp, ht⟩
        · omega
      · have e : pivS p d c A p0 x = p0 := by simp [pivS, ht]
        rw [e]
        rcases ih p0 hl' with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
        · left
          refine ⟨h1, fun _ r hr => ?_⟩
          rcases List.mem_cons.1 hr with rfl | hr
          · simpa using ht
          · exact h2 hp r hr
        · right
          exact ⟨h1, List.mem_cons_of_mem x h2, h3⟩
    · have e : pivS p d c A p0 x = p0 := by simp [pivS, hp]
      rw [e]
      rcases ih p0 hl' with ⟨h1, _⟩ | ⟨h1, _⟩
      · left
        exact ⟨h1, fun h => absurd h hp⟩
      · exact absurd h1 hp

theorem pivF_spec (p d c : Nat) (A : Array (Array Nat)) :
    (pivF p d c A < d ∧ c ≤ pivF p d c A ∧ (A[pivF p d c A]!)[c]! % p ≠ 0) ∨
      (pivF p d c A = d ∧ ∀ r, c ≤ r → r < d → (A[r]!)[c]! % p = 0) := by
  have hl : ∀ r ∈ List.range' c (d - c), r < d := fun r hr => by
    rw [List.mem_range'_1] at hr
    omega
  unfold pivF
  rcases piv_fold p d c A _ d hl with ⟨h1, h2⟩ | ⟨_, h2, h3⟩
  · right
    refine ⟨h1, fun r hr1 hr2 => h2 rfl r ?_⟩
    rw [List.mem_range'_1]
    omega
  · left
    rw [List.mem_range'_1] at h2
    exact ⟨by omega, by omega, h3⟩

theorem elim_fold (p d c : Nat) (A : Array (Array Nat)) (hA : A.size = d) (hc : c < d) :
    ∀ n ≤ d, ((List.range n).foldl (elimS p d c) A).size = d ∧
      ∀ r < d, ((List.range n).foldl (elimS p d c) A)[r]! =
        if r < n ∧ r ≠ c ∧ (A[r]!)[c]! ≠ 0 then newRow p d c A r else A[r]! := by
  intro n
  induction n with
  | zero => intro _; simp [hA]
  | succ n ih =>
    intro hn
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize hM : (List.range n).foldl (elimS p d c) A = M at ih1 ih2 ⊢
    have hn' : M[n]! = A[n]! := by
      rw [ih2 n (by omega)]
      simp
    have hc' : M[c]! = A[c]! := by
      rw [ih2 c hc]
      simp
    have hnr : newRow p d c M n = newRow p d c A n := by
      unfold newRow
      rw [hn', hc']
    unfold elimS
    by_cases h1 : n = c
    · have e1 : ¬ (n != c) = true := by simp [h1]
      rw [ite_eq_right e1]
      refine ⟨ih1, fun r hr => ?_⟩
      rw [ih2 r hr]
      by_cases hrn : r = n
      · subst hrn
        simp [h1]
      · have e : (r < n ↔ r < n + 1) := by omega
        simp only [e]
    · have e1 : (n != c) = true := by simpa using h1
      rw [ite_eq_left e1, hn']
      by_cases h2 : (A[n]!)[c]! = 0
      · have e2 : ¬ ((A[n]!)[c]! != 0) = true := by simp [h2]
        rw [ite_eq_right e2]
        refine ⟨ih1, fun r hr => ?_⟩
        rw [ih2 r hr]
        by_cases hrn : r = n
        · subst hrn
          simp [h2]
        · have e : (r < n ↔ r < n + 1) := by omega
          simp only [e]
      · have e2 : ((A[n]!)[c]! != 0) = true := by simpa using h2
        rw [ite_eq_left e2]
        refine ⟨by rw [size_setR, ih1], fun r hr => ?_⟩
        rw [get_setR M n _ (by rw [ih1]; exact hr)]
        by_cases hrn : r = n
        · subst hrn
          rw [ite_eq_left rfl, hnr, ite_eq_left ⟨by omega, h1, h2⟩]
        · rw [ite_eq_right hrn, ih2 r hr]
          have e : (r < n ↔ r < n + 1) := by omega
          simp only [e]

@[expose] def zE (p : Nat) (A : Array (Array Nat)) (r j : Nat) : ZMod p :=
  (((A[r]!)[j]! : Nat) : ZMod p)

@[expose] def BndG (p d : Nat) (A : Array (Array Nat)) : Prop :=
  A.size = d ∧ ∀ r < d, (A[r]!).size = 2 * d ∧ ∀ j < 2 * d, (A[r]!)[j]! < p

@[expose] def RelG (p d : Nat) (Xm : Nat → Nat → ZMod p) (A : Array (Array Nat)) : Prop :=
  ∀ r < d, ∀ j < d, zE p A r j = ∑ k ∈ Finset.range d, zE p A r (d + k) * Xm k j

@[expose] def InjG (p d : Nat) (A : Array (Array Nat)) : Prop :=
  ∀ v : Nat → ZMod p, (∀ r < d, ∑ j ∈ Finset.range d, zE p A r j * v j = 0) → ∀ j < d, v j = 0

@[expose] def DoneG (d c : Nat) (A : Array (Array Nat)) : Prop :=
  ∀ r < d, ∀ k < c, (A[r]!)[k]! = if r = k then 1 else 0

theorem swap_get {A : Array (Array Nat)} {d piv c r : Nat} (hA : A.size = d) (hr : r < d) :
    (swapR A piv c)[r]! = if r = c then A[piv]! else if r = piv then A[c]! else A[r]! := by
  unfold swapR
  rw [get_setR _ _ _ (by rw [size_setR]; omega), get_setR _ _ _ (by omega)]

theorem swap_inv {p d c piv : Nat} {Xm : Nat → Nat → ZMod p} {A : Array (Array Nat)}
    (hpv : piv < d) (hcp : c ≤ piv) (hB : BndG p d A) (hR : RelG p d Xm A) (hI : InjG p d A)
    (hD : DoneG d c A) :
    BndG p d (swapR A piv c) ∧ RelG p d Xm (swapR A piv c) ∧ InjG p d (swapR A piv c) ∧
      DoneG d c (swapR A piv c) ∧ ((swapR A piv c)[c]!)[c]! = (A[piv]!)[c]! := by
  have hc : c < d := Nat.lt_of_le_of_lt hcp hpv
  have hrow := fun r (hr : r < d) => swap_get (piv := piv) (c := c) (r := r) hB.1 hr
  have hz : ∀ r < d, ∀ j, zE p (swapR A piv c) r j =
      zE p A (if r = c then piv else if r = piv then c else r) j := by
    intro r hr j
    unfold zE
    rw [hrow r hr]
    split_ifs <;> rfl
  have hs : ∀ r < d, (if r = c then piv else if r = piv then c else r) < d := by
    intro r hr
    split_ifs <;> omega
  refine ⟨⟨?_, fun r hr => ?_⟩, fun r hr j hj => ?_, fun v hv => ?_, fun r hr k hk => ?_, ?_⟩
  · unfold swapR
    rw [size_setR, size_setR, hB.1]
  · rw [hrow r hr]
    split_ifs
    · exact hB.2 piv hpv
    · exact hB.2 c hc
    · exact hB.2 r hr
  · simp only [hz r hr]
    exact hR _ (hs r hr) j hj
  · refine hI v fun r hr => ?_
    have h := hv (if r = c then piv else if r = piv then c else r) (hs r hr)
    simp only [hz _ (hs r hr)] at h
    have e : (if (if r = c then piv else if r = piv then c else r) = c then piv
        else if (if r = c then piv else if r = piv then c else r) = piv then c
        else (if r = c then piv else if r = piv then c else r)) = r := by
      split_ifs <;> omega
    rw [e] at h
    exact h
  · rw [hrow r hr]
    by_cases h1 : r = c
    · rw [ite_eq_left h1, hD piv hpv k hk, ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_right h1]
      by_cases h2 : r = piv
      · rw [ite_eq_left h2, hD c hc k hk, ite_eq_right (by omega), ite_eq_right (by omega)]
      · rw [ite_eq_right h2]
        exact hD r hr k hk
  · rw [hrow c hc, ite_eq_left rfl]

theorem scale_get {A : Array (Array Nat)} {p d c r : Nat} (hA : A.size = d) (hr : r < d) :
    (scaleR p c A)[r]! = if r = c then
      A[c]!.map (fun x => x * ((A[c]!)[c]! ^ (p - 2) % p) % p) else A[r]! := by
  unfold scaleR
  rw [get_setR _ _ _ (by omega)]

theorem prime_inv {p a : Nat} (hp : p.Prime) (ha : a % p ≠ 0) :
    (a : ZMod p) * ((a ^ (p - 2) % p : Nat) : ZMod p) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h2 := hp.two_le
  have ha' : (a : ZMod p) ≠ 0 := by
    intro h
    rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff'] at h
    simp at h
    exact ha h
  rw [ZMod.natCast_mod, Nat.cast_pow, ← pow_succ']
  have e : p - 2 + 1 = p - 1 := by omega
  rw [e]
  exact ZMod.pow_card_sub_one_eq_one ha'

theorem scale_inv {p d c : Nat} {Xm : Nat → Nat → ZMod p} {A : Array (Array Nat)} (hp : p.Prime)
    (hc : c < d) (hB : BndG p d A) (hR : RelG p d Xm A) (hI : InjG p d A) (hD : DoneG d c A)
    (hcc : (A[c]!)[c]! % p ≠ 0) :
    BndG p d (scaleR p c A) ∧ RelG p d Xm (scaleR p c A) ∧ InjG p d (scaleR p c A) ∧
      DoneG d c (scaleR p c A) ∧ ((scaleR p c A)[c]!)[c]! = 1 := by
  have h2 := hp.two_le
  set iv := (A[c]!)[c]! ^ (p - 2) % p with hiv
  have hrow := fun r (hr : r < d) => scale_get (p := p) (c := c) (r := r) hB.1 hr
  have hsz : (A[c]!).size = 2 * d := (hB.2 c hc).1
  have hcj : ∀ j < 2 * d, ((scaleR p c A)[c]!)[j]! = (A[c]!)[j]! * iv % p := by
    intro j hj
    rw [hrow c hc, ite_eq_left rfl, get_mapR _ _ (by omega)]
  have hz : ∀ r < d, ∀ j < 2 * d, zE p (scaleR p c A) r j =
      if r = c then zE p A r j * (iv : ZMod p) else zE p A r j := by
    intro r hr j hj
    by_cases h : r = c
    · subst h
      unfold zE
      rw [hcj j hj, ite_eq_left rfl, ZMod.natCast_mod, Nat.cast_mul]
    · unfold zE
      rw [hrow r hr, ite_eq_right h, ite_eq_right h]
  have hinv : ((A[c]!)[c]! : ZMod p) * (iv : ZMod p) = 1 := prime_inv hp hcc
  refine ⟨⟨?_, fun r hr => ?_⟩, fun r hr j hj => ?_, fun v hv => ?_, fun r hr k hk => ?_, ?_⟩
  · unfold scaleR
    rw [size_setR, hB.1]
  · rw [hrow r hr]
    split_ifs with h
    · subst h
      refine ⟨by rw [Array.size_map, hsz], fun j hj => ?_⟩
      rw [get_mapR _ _ (by omega)]
      exact Nat.mod_lt _ (by omega)
    · exact hB.2 r hr
  · have e : ∀ k ∈ Finset.range d, zE p (scaleR p c A) r (d + k) * Xm k j =
        (if r = c then (iv : ZMod p) else 1) * (zE p A r (d + k) * Xm k j) := fun k hk => by
      rw [hz r hr (d + k) (by have := Finset.mem_range.1 hk; omega)]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, ← hR r hr j hj, hz r hr j (by omega)]
    split_ifs <;> ring
  · refine hI v fun r hr => ?_
    have h := hv r hr
    have e : ∑ j ∈ Finset.range d, zE p (scaleR p c A) r j * v j =
        (if r = c then (iv : ZMod p) else 1) * ∑ j ∈ Finset.range d, zE p A r j * v j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hz r hr j (by have := Finset.mem_range.1 hj; omega)]
      split_ifs <;> ring
    rw [e] at h
    split_ifs at h with hrc
    · have h' := congrArg (((A[c]!)[c]! : ZMod p) * ·) h
      simp only [mul_zero, ← mul_assoc, hinv, one_mul] at h'
      exact h'
    · simpa using h
  · rw [hrow r hr]
    by_cases h : r = c
    · rw [ite_eq_left h, get_mapR _ _ (by omega), ← h, hD r hr k hk, ite_eq_right (by omega)]
      simp
    · rw [ite_eq_right h]
      exact hD r hr k hk
  · rw [hcj c (by omega)]
    refine eq_of_cast (Nat.mod_lt _ (by omega)) (by omega) ?_
    rw [ZMod.natCast_mod, Nat.cast_mul, hinv, Nat.cast_one]

theorem elim_inv {p d c : Nat} {Xm : Nat → Nat → ZMod p} {A : Array (Array Nat)} (hp2 : 2 ≤ p)
    (hc : c < d) (hB : BndG p d A) (hR : RelG p d Xm A) (hI : InjG p d A) (hD : DoneG d c A)
    (hcc : (A[c]!)[c]! = 1) :
    BndG p d ((List.range d).foldl (elimS p d c) A) ∧
      RelG p d Xm ((List.range d).foldl (elimS p d c) A) ∧
      InjG p d ((List.range d).foldl (elimS p d c) A) ∧
      DoneG d (c + 1) ((List.range d).foldl (elimS p d c) A) := by
  obtain ⟨h1, h2⟩ := elim_fold p d c A hB.1 hc d le_rfl
  generalize hM : (List.range d).foldl (elimS p d c) A = M at h1 h2 ⊢
  have hent : ∀ r < d, ∀ j < 2 * d, (M[r]!)[j]! =
      if r ≠ c ∧ (A[r]!)[c]! ≠ 0 then ((A[r]!)[j]! + (p - (A[r]!)[c]!) * (A[c]!)[j]!) % p
      else (A[r]!)[j]! := by
    intro r hr j hj
    rw [h2 r hr]
    by_cases h : r ≠ c ∧ (A[r]!)[c]! ≠ 0
    · rw [ite_eq_left ⟨hr, h⟩, ite_eq_left h]
      unfold newRow
      rw [ofFn_get! _ hj]
    · rw [ite_eq_right (fun h' => h ⟨h'.2.1, h'.2.2⟩), ite_eq_right h]
  have hz : ∀ r < d, ∀ j < 2 * d, zE p M r j =
      zE p A r j - (if r = c then 0 else zE p A r c) * zE p A c j := by
    intro r hr j hj
    unfold zE
    rw [hent r hr j hj]
    by_cases h : r ≠ c ∧ (A[r]!)[c]! ≠ 0
    · rw [ite_eq_left h, ite_eq_right h.1, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul,
        Nat.cast_sub (Nat.le_of_lt ((hB.2 r hr).2 c (by omega))), ZMod.natCast_self]
      ring
    · rw [ite_eq_right h]
      by_cases hrc : r = c
      · rw [ite_eq_left hrc]
        ring
      · have h0 : (A[r]!)[c]! = 0 := by
          by_contra h0
          exact h ⟨hrc, h0⟩
        rw [ite_eq_right hrc, h0]
        simp
  have hBM : BndG p d M := by
    refine ⟨h1, fun r hr => ?_⟩
    rw [h2 r hr]
    split_ifs with h
    · unfold newRow
      refine ⟨by simp, fun j hj => ?_⟩
      rw [ofFn_get! _ hj]
      exact Nat.mod_lt _ (by omega)
    · exact hB.2 r hr
  refine ⟨hBM, fun r hr j hj => ?_, fun v hv => ?_, fun r hr k hk => ?_⟩
  · have e : ∀ k ∈ Finset.range d, zE p M r (d + k) * Xm k j =
        zE p A r (d + k) * Xm k j -
          (if r = c then 0 else zE p A r c) * (zE p A c (d + k) * Xm k j) := fun k hk => by
      rw [hz r hr (d + k) (by have := Finset.mem_range.1 hk; omega)]
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hR r hr j hj,
      ← hR c hc j hj, hz r hr j (by omega)]
  · have e : ∀ r < d, ∑ j ∈ Finset.range d, zE p M r j * v j =
        ∑ j ∈ Finset.range d, zE p A r j * v j -
          (if r = c then 0 else zE p A r c) * ∑ j ∈ Finset.range d, zE p A c j * v j := by
      intro r hr
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hz r hr j (by have := Finset.mem_range.1 hj; omega)]
      ring
    have hcz : ∑ j ∈ Finset.range d, zE p A c j * v j = 0 := by
      have h := hv c hc
      rw [e c hc, ite_eq_left rfl] at h
      simpa using h
    refine hI v fun r hr => ?_
    have h := hv r hr
    rw [e r hr, hcz, mul_zero, sub_zero] at h
    exact h
  · have hlt : (M[r]!)[k]! < p := (hBM.2 r hr).2 k (by omega)
    have hd : (if r = k then 1 else 0) < p := by split_ifs <;> omega
    refine eq_of_cast hlt hd ?_
    have hzk := hz r hr k (by omega)
    unfold zE at hzk
    rw [hzk]
    by_cases hkc : k < c
    · have e1 : (A[c]!)[k]! = 0 := by rw [hD c hc k hkc, ite_eq_right (by omega)]
      rw [e1, hD r hr k hkc]
      simp
    · have hk' : k = c := by omega
      subst hk'
      by_cases hrk : r = k
      · subst hrk
        rw [hcc]
        simp
      · rw [hcc, ite_eq_right hrk, ite_eq_right hrk]
        simp

theorem piv_exists {p d c : Nat} {A : Array (Array Nat)} (hp2 : 2 ≤ p) (hc : c < d)
    (hI : InjG p d A) (hD : DoneG d c A) (h0 : ∀ r, c ≤ r → r < d → (A[r]!)[c]! % p = 0) :
    False := by
  let v : Nat → ZMod p := fun j => if j = c then 1 else if j < c then -zE p A j c else 0
  have hv : ∀ r < d, ∑ j ∈ Finset.range d, zE p A r j * v j = 0 := by
    intro r hr
    have e : ∀ j ∈ Finset.range d, zE p A r j * v j =
        (if j = c then zE p A r c else 0) +
          (if r = j then (if r < c then -zE p A r c else 0) else 0) := by
      intro j hj
      have hj' := Finset.mem_range.1 hj
      by_cases hjc : j = c
      · subst hjc
        simp [v]
        omega
      · by_cases hlt : j < c
        · have hz : zE p A r j = if r = j then 1 else 0 := by
            unfold zE
            rw [hD r hr j hlt]
            split_ifs <;> simp
          rw [hz]
          by_cases hrj : r = j
          · subst hrj
            simp [v, hjc, hlt]
          · simp [v, hjc, hlt, hrj]
        · by_cases hrj : r = j
          · subst hrj
            simp [v, hjc, hlt]
          · simp [v, hjc, hlt, hrj]
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range d) c,
      Finset.sum_ite_eq (Finset.range d) r]
    rw [ite_eq_left (Finset.mem_range.2 hc), ite_eq_left (Finset.mem_range.2 hr)]
    by_cases hrc : r < c
    · rw [ite_eq_left hrc]
      ring
    · rw [ite_eq_right hrc, add_zero]
      unfold zE
      rw [← Nat.mod_add_div ((A[r]!)[c]!) p, h0 r (by omega) hr]
      simp
  have h := hI v hv c hc
  simp only [v, ite_true] at h
  have h' : ((1 : Nat) : ZMod p) = ((0 : Nat) : ZMod p) := by simpa using h
  have := eq_of_cast (by omega) (by omega) h'
  omega

theorem step_inv {p d c : Nat} {Xm : Nat → Nat → ZMod p} {A : Array (Array Nat)} (hp : p.Prime)
    (hc : c < d) (hB : BndG p d A) (hR : RelG p d Xm A) (hI : InjG p d A) (hD : DoneG d c A) :
    BndG p d (stepS p d A c) ∧ RelG p d Xm (stepS p d A c) ∧ InjG p d (stepS p d A c) ∧
      DoneG d (c + 1) (stepS p d A c) := by
  have hp2 := hp.two_le
  rcases pivF_spec p d c A with ⟨hpv, hcp, hnz⟩ | ⟨_, h0⟩
  · unfold stepS
    rw [ite_eq_left hpv]
    obtain ⟨b1, r1, i1, d1, e1⟩ := swap_inv (Xm := Xm) hpv hcp hB hR hI hD
    obtain ⟨b2, r2, i2, d2, e2⟩ := scale_inv hp hc b1 r1 i1 d1 (by rw [e1]; exact hnz)
    exact elim_inv hp2 hc b2 r2 i2 d2 e2
  · exact (piv_exists hp2 hc hI hD h0).elim

theorem init_inv {p d : Nat} (hp2 : 2 ≤ p) (X : Array (Array Nat))
    (hX : ∀ v : Nat → ZMod p, (∀ r < d, ∑ j ∈ Finset.range d,
      (((X[r]!)[j]! : Nat) : ZMod p) * v j = 0) → ∀ j < d, v j = 0) :
    BndG p d (initG p d X) ∧
      RelG p d (fun k j => (((X[k]!)[j]! : Nat) : ZMod p)) (initG p d X) ∧
      InjG p d (initG p d X) ∧ DoneG d 0 (initG p d X) := by
  have hent : ∀ r < d, ∀ j < 2 * d, ((initG p d X)[r]!)[j]! =
      if j < d then (X[r]!)[j]! % p else if j - d = r then 1 else 0 := by
    intro r hr j hj
    unfold initG
    rw [ofFn_get! _ hr, ofFn_get! _ hj]
  refine ⟨⟨by simp [initG], fun r hr => ⟨?_, fun j hj => ?_⟩⟩, fun r hr j hj => ?_,
    fun v hv => ?_, fun r _ k hk => absurd hk (Nat.not_lt_zero k)⟩
  · unfold initG
    rw [ofFn_get! _ hr]
    simp
  · rw [hent r hr j hj]
    split_ifs
    · exact Nat.mod_lt _ (by omega)
    · omega
    · omega
  · have e : ∀ k ∈ Finset.range d, zE p (initG p d X) r (d + k) * (((X[k]!)[j]! : Nat) : ZMod p) =
        if r = k then (((X[k]!)[j]! : Nat) : ZMod p) else 0 := by
      intro k hk
      have hk' := Finset.mem_range.1 hk
      unfold zE
      rw [hent r hr (d + k) (by omega), ite_eq_right (by omega), Nat.add_sub_cancel_left]
      by_cases h : k = r
      · subst h
        simp
      · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
        simp
    rw [Finset.sum_congr rfl e, Finset.sum_ite_eq (Finset.range d) r, ite_eq_left (Finset.mem_range.2 hr)]
    unfold zE
    rw [hent r hr j (by omega), ite_eq_left hj, ZMod.natCast_mod]
  · refine hX v fun r hr => ?_
    rw [← hv r hr]
    refine Finset.sum_congr rfl fun j hj => ?_
    unfold zE
    rw [hent r hr j (by have := Finset.mem_range.1 hj; omega),
      ite_eq_left (Finset.mem_range.1 hj), ZMod.natCast_mod]

theorem fold_inv {p d : Nat} {Xm : Nat → Nat → ZMod p} (hp : p.Prime) {A : Array (Array Nat)}
    (hB : BndG p d A) (hR : RelG p d Xm A) (hI : InjG p d A) (hD : DoneG d 0 A) :
    ∀ n ≤ d, BndG p d ((List.range n).foldl (stepS p d) A) ∧
      RelG p d Xm ((List.range n).foldl (stepS p d) A) ∧
      InjG p d ((List.range n).foldl (stepS p d) A) ∧
      DoneG d n ((List.range n).foldl (stepS p d) A) := by
  intro n
  induction n with
  | zero => intro _; exact ⟨hB, hR, hI, hD⟩
  | succ n ih =>
    intro hn
    obtain ⟨b, r, i, d'⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact step_inv hp (by omega) b r i d'

theorem inj_of_inv {p d : Nat} {Xm Ym : Nat → Nat → ZMod p}
    (h : ∀ i < d, ∀ j < d, ∑ k ∈ Finset.range d, Xm i k * Ym k j = if i = j then 1 else 0) :
    ∀ v : Nat → ZMod p, (∀ r < d, ∑ j ∈ Finset.range d, Xm r j * v j = 0) → ∀ j < d, v j = 0 := by
  let Mx : Matrix (Fin d) (Fin d) (ZMod p) := fun i j => Xm i.val j.val
  let My : Matrix (Fin d) (Fin d) (ZMod p) := fun i j => Ym i.val j.val
  have h1 : Mx * My = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have e := h i.val i.isLt j.val j.isLt
    rw [Finset.sum_range] at e
    rw [e]
    simp [Fin.ext_iff]
  have h2 : My * Mx = 1 := mul_eq_one_comm.1 h1
  intro v hv j hj
  let w : Fin d → ZMod p := fun m => v m.val
  have hw : Mx.mulVec w = 0 := by
    funext k
    have e := hv k.val k.isLt
    rw [Finset.sum_range] at e
    exact e
  have e2 : (My * Mx).mulVec w = 0 := by
    rw [← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
  rw [h2, Matrix.one_mulVec] at e2
  exact congrFun e2 ⟨j, hj⟩

theorem invM_spec {p d : Nat} (hp : p.Prime) {X : Array (Array Nat)} {y : Nat → Nat → Nat}
    (hy : ∀ i < d, ∀ j < d, y i j < p)
    (hXY : ∀ i < d, ∀ j < d, ∑ k ∈ Finset.range d,
      (((X[i]!)[k]! : Nat) : ZMod p) * ((y k j : Nat) : ZMod p) = if i = j then 1 else 0) :
    invM p d X = Array.ofFn (n := d) fun i => Array.ofFn (n := d) fun j => y i.val j.val := by
  have hp2 := hp.two_le
  obtain ⟨b0, r0, i0, d0⟩ := init_inv hp2 X (inj_of_inv hXY)
  obtain ⟨hB, hR, -, hD⟩ := fold_inv hp b0 r0 i0 d0 d le_rfl
  rw [invM_eq_invF]
  unfold invF
  generalize hA : (List.range d).foldl (stepS p d) (initG p d X) = A at hB hR hD
  have hRX : ∀ r < d, ∀ j < d, ∑ k ∈ Finset.range d, zE p A r (d + k) *
      (((X[k]!)[j]! : Nat) : ZMod p) = if r = j then 1 else 0 := by
    intro r hr j hj
    rw [← hR r hr j hj]
    unfold zE
    rw [hD r hr j hj]
    split_ifs <;> simp
  have hRY : ∀ r < d, ∀ j < d, zE p A r (d + j) = ((y r j : Nat) : ZMod p) := by
    intro r hr j hj
    calc zE p A r (d + j)
        = ∑ m ∈ Finset.range d, zE p A r (d + m) * (if m = j then 1 else 0) := by
          simp only [mul_ite, mul_one, mul_zero]
          rw [Finset.sum_ite_eq' (Finset.range d) j, ite_eq_left (Finset.mem_range.2 hj)]
      _ = ∑ m ∈ Finset.range d, zE p A r (d + m) * ∑ k ∈ Finset.range d,
            (((X[m]!)[k]! : Nat) : ZMod p) * ((y k j : Nat) : ZMod p) := by
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [hXY m (Finset.mem_range.1 hm) j hj]
      _ = ∑ k ∈ Finset.range d, (∑ m ∈ Finset.range d, zE p A r (d + m) *
            (((X[m]!)[k]! : Nat) : ZMod p)) * ((y k j : Nat) : ZMod p) := by
          simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
          exact Finset.sum_comm
      _ = ∑ k ∈ Finset.range d, (if r = k then 1 else 0) * ((y k j : Nat) : ZMod p) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [hRX r hr k (Finset.mem_range.1 hk)]
      _ = ((y r j : Nat) : ZMod p) := by
          simp only [ite_mul, one_mul, zero_mul]
          rw [Finset.sum_ite_eq (Finset.range d) r, ite_eq_left (Finset.mem_range.2 hr)]
  apply Array.ext
  · simp [hB.1]
  · intro i h1 h2
    have hi : i < d := by simpa using h2
    have hiA : i < A.size := by rw [hB.1]; exact hi
    simp only [Array.getElem_map, Array.getElem_ofFn]
    have hsz : (A[i]).size = 2 * d := by
      have := (hB.2 i hi).1
      rwa [getElem!_pos A i hiA] at this
    apply Array.ext
    · simp [hsz]
      omega
    · intro k k1 k2
      have hk : k < d := by simpa using k2
      have hkA : d + k < (A[i]).size := by omega
      simp only [Array.getElem_extract, Array.getElem_ofFn]
      have hv := hRY i hi k hk
      unfold zE at hv
      have hlt := (hB.2 i hi).2 (d + k) (by omega)
      rw [getElem!_pos A i hiA] at hv hlt
      rw [getElem!_pos (A[i]) (d + k) hkA] at hv hlt
      exact eq_of_cast hlt (hy i hi k hk) hv

theorem unpackL_ofFn (d w S X : Nat) : unpackL d w S X =
    Array.ofFn (n := d) fun i => Array.ofFn (n := d) fun j =>
      X / 2 ^ (S * i.val + w * j.val) % 2 ^ w := by
  unfold unpackL
  refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun k => ?_))
  rw [land_eq, Nat.and_two_pow_sub_one_eq_mod]
  change X >>> (S * i.val + w * k.val) % 2 ^ w = _
  rw [Nat.shiftRight_eq_div_pow]

theorem invM_eqL {p w S d T L H CM RM ONE LV HV X Y : Nat} (hpr : p.Prime)
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true)
    (hX : validM p (d * S) L H X = true) (hY : validM p (d * S) L H Y = true)
    (h : Nat.beq (mulR p w S d T L H CM RM X Y) ONE = true) :
    invM p d (unpackL d w S X) = unpackL d w S Y := by
  obtain ⟨hp, hS, hw, hpw⟩ := cfacts hc
  have cX := validM_canon hc hX
  have cY := validM_canon hc hY
  obtain ⟨-, hZ⟩ := mulR_sound hc cX cY
  obtain ⟨-, h1⟩ := one_sound hc
  rw [Nat.eq_of_beq_eq_true h, h1] at hZ
  rw [unpackL_ofFn d w S Y]
  subst hS
  refine invM_spec hpr (fun i hi j hj => canon_ent cY hi hj) fun i hi j hj => ?_
  have e := congrFun (congrFun hZ ⟨i, hi⟩) ⟨j, hj⟩
  rw [Matrix.mul_apply, Matrix.one_apply] at e
  rw [Finset.sum_range (fun k => ((((unpackL d w (d * w) X)[i]!)[k]! : Nat) : ZMod p) *
    ((Y / 2 ^ (d * w * k + w * j) % 2 ^ w : Nat) : ZMod p))]
  have e2 : ∀ k : Fin d, ((((unpackL d w (d * w) X)[i]!)[k.val]! : Nat) : ZMod p) *
      ((Y / 2 ^ (d * w * k.val + w * j) % 2 ^ w : Nat) : ZMod p) =
      ordMat p d w (d * w) X ⟨i, hi⟩ k * ordMat p d w (d * w) Y k ⟨j, hj⟩ := fun k => by
    rw [unpackL_get hi k.isLt]
    rfl
  simp only [e2]
  rw [← e]
  simp [Fin.ext_iff]

theorem strictN_valL (y : Nat) (k : Nat → Nat) : CFSG.KC.Enum.strictN y k = k y := by
  cases y <;> rfl

theorem powM_eqL {p w S d T L H CM RM ONE LV HV M : Nat}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true)
    (hM : validM p (d * S) L H M = true) (e : Nat) :
    powM p d (unpackL d w S M) e = unpackL d w S (powR p w S d T L H CM RM ONE M e) ∧
      validM p (d * S) L H (powR p w S d T L H CM RM ONE M e) = true := by
  induction e with
  | zero => exact idM_eqL hc
  | succ e ih =>
    obtain ⟨h1, h2⟩ := ih
    have e1 : powR p w S d T L H CM RM ONE M (e + 1) =
        mulR p w S d T L H CM RM (powR p w S d T L H CM RM ONE M e) M :=
      strictN_valL (powR p w S d T L H CM RM ONE M e) (fun a => mulR p w S d T L H CM RM a M)
    have e2 : powM p d (unpackL d w S M) (e + 1) =
        mulM p d (powM p d (unpackL d w S M) e) (unpackL d w S M) := rfl
    rw [e1, e2, h1]
    exact mulR_eqL hc h2 hM

theorem wordR_cons (p w S d T L H CM RM : Nat) (G GI : Nat → Nat) (X : Nat) (l : Int)
    (ws : List Int) : wordR p w S d T L H CM RM G GI X (l :: ws) =
      wordR p w S d T L H CM RM G GI (mulR p w S d T L H CM RM X (letterR G GI l)) ws :=
  strictN_valL (mulR p w S d T L H CM RM X (letterR G GI l))
    (fun X => wordR p w S d T L H CM RM G GI X ws)

open CFSG.Sporadic.LySchreier.Native in
theorem letter_eqL {w S L H : Nat} {G GI : Nat → Nat}
    {g gi : Nat → Array (Array Nat)}
    (hg : ∀ i, g i = unpackL 111 w S (G i) ∧ validM 5 (111 * S) L H (G i) = true)
    (hgi : ∀ i, gi i = unpackL 111 w S (GI i) ∧ validM 5 (111 * S) L H (GI i) = true)
    (l : Int) :
    letterM g gi l = unpackL 111 w S (letterR G GI l) ∧
      validM 5 (111 * S) L H (letterR G GI l) = true := by
  rcases l with (_ | k) | k
  · have e1 : letterR G GI (Int.ofNat 0) = GI 0 := rfl
    have e2 : letterM g gi (Int.ofNat 0) = gi 0 := by simp [letterM]
    rw [e1, e2]
    exact hgi 0
  · have e1 : letterR G GI (Int.ofNat (k + 1)) = G k := rfl
    have e2 : letterM g gi (Int.ofNat (k + 1)) = g k := by
      simp only [letterM]
      rw [ite_eq_left (by simp)]
      congr 1
    rw [e1, e2]
    exact hg k
  · have e1 : letterR G GI (Int.negSucc k) = GI k := rfl
    have e2 : letterM g gi (Int.negSucc k) = gi k := by
      simp only [letterM]
      rw [ite_eq_right (by omega)]
      congr 1
    rw [e1, e2]
    exact hgi k

open CFSG.Sporadic.LySchreier.Native in
theorem wordFromM_eqL {w S T L H CM RM ONE LV HV : Nat} {G GI : Nat → Nat}
    {g gi : Nat → Array (Array Nat)}
    (hc : constsOK 5 w S 111 T L H CM RM ONE LV HV = true)
    (hg : ∀ i, g i = unpackL 111 w S (G i) ∧ validM 5 (111 * S) L H (G i) = true)
    (hgi : ∀ i, gi i = unpackL 111 w S (GI i) ∧ validM 5 (111 * S) L H (GI i) = true)
    (ws : List Int) : ∀ X, validM 5 (111 * S) L H X = true →
    wordFromM g gi (unpackL 111 w S X) ws =
        unpackL 111 w S (wordR 5 w S 111 T L H CM RM G GI X ws) ∧
      validM 5 (111 * S) L H (wordR 5 w S 111 T L H CM RM G GI X ws) = true := by
  induction ws with
  | nil =>
    intro X hX
    refine ⟨?_, hX⟩
    simp only [wordFromM, List.foldl_nil]
    rfl
  | cons l ws ih =>
    intro X hX
    have e1 : wordFromM g gi (unpackL 111 w S X) (l :: ws) =
        wordFromM g gi (mulM 5 111 (unpackL 111 w S X) (letterM g gi l)) ws := by
      simp only [wordFromM, List.foldl_cons]
    have e2 := wordR_cons 5 w S 111 T L H CM RM G GI X l ws
    obtain ⟨hl1, hl2⟩ := letter_eqL hg hgi l
    obtain ⟨m1, m2⟩ := mulR_eqL hc hX hl2
    rw [e1, e2, hl1, m1]
    exact ih _ m2

theorem nIf_eqL (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem bAnd_eqL (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

@[expose] def digV (c : Nat) : Nat :=
  nIf(bAnd(Nat.ble (nat_lit 48) c, Nat.ble c (nat_lit 57)), Nat.sub c (nat_lit 48), nat_lit 0)

theorem pay_nil (p d w S ph idx M : Nat) : payRunP p d w S [] ph idx M = M := rfl

theorem pay0 (p d w S : Nat) (ch : Char) (cs : List Char) (idx M : Nat) :
    payRunP p d w S (ch :: cs) 0 idx M =
      if ch.toNat = 10 then payRunP p d w S cs 1 idx M else payRunP p d w S cs 0 idx M := by
  have e : payRunP p d w S (ch :: cs) 0 idx M = CFSG.KC.Enum.strictN (Char.toNat ch) (fun c =>
      Bool.rec (motive := fun _ => Nat) (payRunP p d w S cs 0 idx M) (payRunP p d w S cs 1 idx M)
        (Nat.beq c 10)) := rfl
  rw [e, strictN_valL, nIf_eqL]
  simp only [Nat.beq_eq]

theorem pay1 (p d w S : Nat) (ch : Char) (cs : List Char) (idx M : Nat) :
    payRunP p d w S (ch :: cs) 1 idx M =
      if CFSG.KS.SporSch.wsK ch.toNat = true then payRunP p d w S cs 1 idx M
      else payRunP p d w S cs 1 (idx + 1) (if idx < d * d then
        M ||| (digV ch.toNat % p) <<< (S * (idx / d) + w * (idx % d)) else M) := by
  have e : payRunP p d w S (ch :: cs) 1 idx M = CFSG.KC.Enum.strictN (Char.toNat ch) (fun c =>
      Bool.rec (motive := fun _ => Nat)
        (CFSG.KC.Enum.strictN (Bool.rec (motive := fun _ => Nat) M
            (Nat.lor M (Nat.shiftLeft (Nat.mod (digV c) p)
              (Nat.add (Nat.mul S (Nat.div idx d)) (Nat.mul w (Nat.mod idx d)))))
            (Nat.blt idx (Nat.mul d d)))
          (fun M' => CFSG.KC.Enum.strictN (Nat.succ idx) (fun idx' =>
            payRunP p d w S cs (nat_lit 1) idx' M')))
        (payRunP p d w S cs 1 idx M) (CFSG.KS.SporSch.wsK c)) := rfl
  rw [e, strictN_valL, nIf_eqL, strictN_valL, strictN_valL, nIf_eqL]
  simp only [Nat.blt_eq]
  rfl

theorem pay_ph0 (p d w S : Nat) : ∀ (cs : List Char) (idx M : Nat),
    payRunP p d w S cs 0 idx M = payRunP p d w S ((cs.dropWhile (· != '\n')).drop 1) 1 idx M := by
  intro cs
  induction cs with
  | nil => intro idx M; rfl
  | cons ch cs ih =>
    intro idx M
    rw [pay0]
    by_cases h : ch = '\n'
    · subst h
      have h10 : ('\n' : Char).toNat = 10 := rfl
      rw [ite_eq_left h10, List.dropWhile_cons_of_neg (by simp)]
      rfl
    · have h' : ch.toNat ≠ 10 := fun e => h (Char.toNat_inj.1 e)
      rw [ite_eq_right h', List.dropWhile_cons_of_pos (by simpa using h)]
      exact ih idx M

@[expose] def entL (d w S M t : Nat) : Nat := M / 2 ^ (S * (t / d) + w * (t % d)) % 2 ^ w

theorem divmod_uniq {B a b i j : Nat} (ha : a < B) (hb : b < B) (h : B * i + a = B * j + b) :
    i = j ∧ a = b := by
  have hB : 0 < B := by omega
  have h1 : (B * i + a) / B = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt ha, Nat.zero_add]
  have h2 : (B * j + b) / B = j := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hb, Nat.zero_add]
  have h3 : (B * i + a) % B = a := by rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  have h4 : (B * j + b) % B = b := by rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  rw [h] at h1 h3
  exact ⟨h1.symm.trans h2, h3.symm.trans h4⟩

theorem pos_inj {d w S t t' r r' : Nat} (hS : w * d ≤ S) (ht : t < d * d) (ht' : t' < d * d)
    (hr : r < w) (hr' : r' < w)
    (h : S * (t / d) + w * (t % d) + r = S * (t' / d) + w * (t' % d) + r') : t = t' := by
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0
      simp at ht
    · exact h0
  have hm : t % d < d := Nat.mod_lt _ hd
  have hm' : t' % d < d := Nat.mod_lt _ hd
  have a1 : w * (t % d) + r < S := by nlinarith
  have a2 : w * (t' % d) + r' < S := by nlinarith
  obtain ⟨e1, e2⟩ := divmod_uniq a1 a2 (by rw [← Nat.add_assoc, ← Nat.add_assoc]; exact h)
  obtain ⟨e3, -⟩ := divmod_uniq hr hr' e2
  rw [← Nat.div_add_mod t d, ← Nat.div_add_mod t' d, e1, e3]

theorem entL_put {d w S M v t t' : Nat} (hS : w * d ≤ S) (ht : t < d * d) (ht' : t' < d * d)
    (hv : v < 2 ^ w) :
    entL d w S (M ||| v <<< (S * (t' / d) + w * (t' % d))) t =
      if t = t' then entL d w S M t ||| v else entL d w S M t := by
  unfold entL
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_ent, Nat.testBit_lor, Nat.testBit_shiftLeft]
  by_cases htt : t = t'
  · subst htt
    rw [ite_eq_left rfl, Nat.testBit_lor, testBit_ent]
    by_cases hr : r < w
    · simp [hr]
    · have hv' : v.testBit r = false :=
        Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hr, hv']
  · rw [ite_eq_right htt, testBit_ent]
    by_cases hr : r < w
    · have hz : (decide (r + (S * (t / d) + w * (t % d)) ≥ S * (t' / d) + w * (t' % d)) &&
          v.testBit (r + (S * (t / d) + w * (t % d)) - (S * (t' / d) + w * (t' % d)))) = false := by
        by_cases hge : r + (S * (t / d) + w * (t % d)) ≥ S * (t' / d) + w * (t' % d)
        · have hlt : ¬ (r + (S * (t / d) + w * (t % d)) - (S * (t' / d) + w * (t' % d)) < w) := by
            intro hlt
            exact htt (pos_inj hS ht ht' hr hlt (by omega))
          have hv' := Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hv
            (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hlt)))
          simp [hv']
        · simp [hge]
      rw [hz, Bool.or_false]
    · simp [hr]

@[expose] def esL (cs : List Char) : List Nat :=
  (cs.filter fun c => !wsChar c).map fun c => if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0

theorem char_beqL (c d : Char) : (c == d) = (c.toNat == d.toNat) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, beq_iff_eq]
  exact Char.toNat_inj.symm

theorem wsK_eq (c : Char) : CFSG.KS.SporSch.wsK c.toNat = wsChar c := by
  unfold CFSG.KS.SporSch.wsK wsChar
  rw [char_beqL, char_beqL, char_beqL, char_beqL]
  have e1 : (' ' : Char).toNat = 32 := rfl
  have e2 : ('\t' : Char).toNat = 9 := rfl
  have e3 : ('\n' : Char).toNat = 10 := rfl
  have e4 : ('\r' : Char).toNat = 13 := rfl
  rw [e1, e2, e3, e4]
  generalize c.toNat = x
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, beq_iff_eq]
  by_cases h32 : x = 32
  · subst h32; decide
  by_cases h9 : x = 9
  · subst h9; decide
  by_cases h10 : x = 10
  · subst h10; decide
  by_cases h13 : x = 13
  · subst h13; decide
  by_cases h11 : x = 11
  · subst h11; decide
  by_cases h12 : x = 12
  · subst h12; decide
  have nb : ∀ {y : Nat}, x ≠ y → Nat.beq x y = false :=
    fun h => Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
  rw [nb h32, nb h9, nb h10, nb h13, nb h11, nb h12]
  simp [h32, h9, h10, h13, h11, h12]

theorem digV_eq (c : Char) :
    digV c.toNat = if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0 := by
  unfold digV
  rw [nIf_eqL, bAnd_eqL]
  have e1 : ('0' : Char).toNat = 48 := rfl
  have e2 : ('9' : Char).toNat = 57 := rfl
  have l1 : ('0' ≤ c) ↔ 48 ≤ c.toNat := by rw [← e1]; exact UInt32.le_iff_toNat_le
  have l2 : (c ≤ '9') ↔ c.toNat ≤ 57 := by rw [← e2]; exact UInt32.le_iff_toNat_le
  rw [e1]
  by_cases h : 48 ≤ c.toNat ∧ c.toNat ≤ 57
  · have hb : (Nat.ble 48 c.toNat && Nat.ble c.toNat 57) = true := by
      simp [Nat.ble_eq, h.1, h.2]
    have hc : ('0' ≤ c && c ≤ '9') = true := by
      simp [l1.2 h.1, l2.2 h.2]
    rw [ite_eq_left hb, ite_eq_left hc]
    rfl
  · have hb : ¬ (Nat.ble 48 c.toNat && Nat.ble c.toNat 57) = true := by
      simp only [Bool.and_eq_true, Nat.ble_eq]
      exact h
    have hc : ¬ ('0' ≤ c && c ≤ '9') = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      rw [l1, l2]
      exact h
    rw [ite_eq_right hb, ite_eq_right hc]

theorem pay_run1 {p d w S : Nat} (hp0 : 0 < p) (hp : p ≤ 2 ^ w) (hS : w * d ≤ S) :
    ∀ (cs : List Char) (idx M : Nat), (∀ t < d * d, idx ≤ t → entL d w S M t = 0) →
      ∀ t < d * d, entL d w S (payRunP p d w S cs 1 idx M) t =
        if idx ≤ t then (esL cs).getD (t - idx) 0 % p else entL d w S M t := by
  intro cs
  induction cs with
  | nil =>
    intro idx M hM t ht
    rw [pay_nil]
    split_ifs with h
    · rw [hM t ht h]
      simp [esL]
    · rfl
  | cons ch cs ih =>
    intro idx M hM t ht
    rw [pay1]
    by_cases hw : CFSG.KS.SporSch.wsK ch.toNat = true
    · rw [ite_eq_left hw]
      have e : esL (ch :: cs) = esL cs := by
        unfold esL
        rw [List.filter_cons_of_neg (by rw [← wsK_eq, hw]; simp)]
      rw [e]
      exact ih idx M hM t ht
    · rw [ite_eq_right hw]
      have e : esL (ch :: cs) = digV ch.toNat :: esL cs := by
        unfold esL
        rw [List.filter_cons_of_pos (by rw [← wsK_eq]; simpa using hw), List.map_cons, digV_eq]
      rw [e]
      have hv : digV ch.toNat % p < 2 ^ w := Nat.lt_of_lt_of_le (Nat.mod_lt _ hp0) hp
      set M' := (if idx < d * d then
        M ||| (digV ch.toNat % p) <<< (S * (idx / d) + w * (idx % d)) else M) with hM'
      have hent : ∀ t < d * d, entL d w S M' t =
          if t = idx then entL d w S M t ||| (digV ch.toNat % p) else entL d w S M t := by
        intro t ht
        rw [hM']
        split_ifs with h1 h2
        · rw [entL_put hS ht h1 hv, ite_eq_left h2]
        · rw [entL_put hS ht h1 hv, ite_eq_right h2]
        · omega
        · rfl
      have hM'0 : ∀ t < d * d, idx + 1 ≤ t → entL d w S M' t = 0 := by
        intro t ht h
        rw [hent t ht, ite_eq_right (by omega)]
        exact hM t ht (by omega)
      rw [ih (idx + 1) M' hM'0 t ht]
      by_cases h1 : idx + 1 ≤ t
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
        have e2 : t - idx = (t - (idx + 1)) + 1 := by omega
        rw [e2, List.getD_cons_succ]
      · rw [ite_eq_right h1, hent t ht]
        by_cases h2 : t = idx
        · subst h2
          rw [ite_eq_left rfl, ite_eq_left le_rfl, hM t ht le_rfl, Nat.zero_or, Nat.sub_self,
            List.getD_cons_zero]
        · rw [ite_eq_right h2, ite_eq_right (by omega)]

theorem payRunP_eqL {p d w S : Nat} (cs : List Char) (hp0 : 0 < p) (hp : p ≤ 2 ^ w)
    (hS : w * d ≤ S) :
    CFSG.Sporadic.He.Native.rowsOf p d (String.ofList cs) =
      unpackL d w S (payRunP p d w S cs 0 0 0) := by
  rw [pay_ph0]
  have hdec : decodeEntries (String.ofList cs) = esL ((cs.dropWhile (· != '\n')).drop 1) := by
    unfold decodeEntries
    rw [String.toList_ofList]
    rfl
  have hrun := pay_run1 hp0 hp hS ((cs.dropWhile (· != '\n')).drop 1) 0 0
    (fun t _ _ => by simp [entL])
  unfold CFSG.Sporadic.He.Native.rowsOf
  rw [hdec, unpackL_ofFn]
  refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun j => ?_))
  have hd : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have ht : d * i.val + j.val < d * d := by
    have := i.isLt
    have := j.isLt
    nlinarith
  have h := hrun (d * i.val + j.val) ht
  unfold entL at h
  have e1 : (d * i.val + j.val) / d = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt j.isLt, Nat.zero_add]
  have e2 : (d * i.val + j.val) % d = j.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]
  rw [e1, e2, ite_eq_left (Nat.zero_le _), Nat.sub_zero] at h
  rw [h, List.getElem?_toArray, List.getD_eq_getElem?_getD, Nat.mul_comm i.val d]

end CFSG.KS.SporSch.LyM

end
