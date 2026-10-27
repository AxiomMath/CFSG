module

public import CFSG.GF2Type.Smith1979W3.Cert690.Check
public import CFSG.GF2Type.Smith1979W3.Cert690.Dict
public import CFSG.GF2Type.Smith1979W3.Cert690.Q0

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

@[expose] def packVec (v : V₀) : ℕ := ∑ i : Fin 6, (v i).val * 2 ^ (i : ℕ)

theorem packVec_lt : ∀ v : V₀, packVec v < 64 := by decide +kernel

theorem vec_packVec : ∀ v : V₀, Code.vec (packVec v) = v := by decide +kernel

theorem vec_zero : Code.vec 0 = 0 := by
  funext i
  simp [Code.vec, Code.bitZ]

theorem packVec_testBit : ∀ (v : V₀) (i : Fin 6), (packVec v).testBit i.val = (v i == 1) := by
  decide +kernel

theorem packVec_testBit' (v : V₀) (i : ℕ) (hi : i < 6) :
    (packVec v).testBit i = (v ⟨i, hi⟩ == 1) :=
  packVec_testBit v ⟨i, hi⟩

theorem packVec_vec {m : ℕ} (hm : m < 64) : packVec (Code.vec m) = m :=
  vec_injective_of_lt (packVec_lt _) hm (vec_packVec (Code.vec m))

theorem packVec_zero : packVec (0 : V₀) = 0 := by
  have h : (0 : V₀) = Code.vec 0 := (vec_zero).symm
  rw [h, packVec_vec (by norm_num)]

theorem packVec_injective : Function.Injective packVec := by
  intro u v h
  have h' := congrArg Code.vec h
  rwa [vec_packVec u, vec_packVec v] at h'

theorem zmod2_val_eq_ite (z : ZMod 2) : z.val = if z == 1 then 1 else 0 := by
  rcases CFSG.RankThree.Literature.FSmith.zmod2_cases z with h | h
  · rw [h]; simp
  · rw [h, ZMod.val_one]; simp

theorem zmod2_val_add (a b : ZMod 2) : (a + b).val = a.val ^^^ b.val := by
  rcases CFSG.RankThree.Literature.FSmith.zmod2_cases a with h | h <;> rw [h] <;>
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases b with h' | h' <;> rw [h'] <;> decide

theorem zmod2_eq_one_add (a b : ZMod 2) :
    (a + b == 1) = ((a == 1) ^^ (b == 1)) := by
  rcases CFSG.RankThree.Literature.FSmith.zmod2_cases a with h | h <;> rw [h] <;>
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases b with h' | h' <;> rw [h'] <;> decide

theorem zmod2_eq_one_mul (a b : ZMod 2) :
    (a * b == 1) = ((a == 1) && (b == 1)) := by
  rcases CFSG.RankThree.Literature.FSmith.zmod2_cases a with h | h <;> rw [h] <;>
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases b with h' | h' <;> rw [h'] <;> decide

theorem testBit_zero_add_two_mul (a p : ℕ) (ha : a < 2) :
    (a + 2 * p).testBit 0 = (a == 1) := by
  have h := Nat.testBit_two_pow_mul_add p (b := a) (i := 1) (by omega) 0
  rw [show a + 2 * p = 2 ^ 1 * p + a by ring, h]
  norm_num
  interval_cases a <;> decide

@[expose] noncomputable def enc (x : Q0) : ℕ := x.a.val + 2 * packVec x.v

@[expose] def dec (n : ℕ) : Q0 := ⟨Code.bitZ n 0, Code.vec (n / 2)⟩

theorem enc_eq (x : Q0) : enc x = x.a.val + 2 * packVec x.v := rfl

theorem enc_mod_two (x : Q0) : enc x % 2 = x.a.val := by
  have h : x.a.val < 2 := ZMod.val_lt x.a
  simp only [enc_eq]
  omega

theorem enc_div_two (x : Q0) : enc x / 2 = packVec x.v := by
  have h : x.a.val < 2 := ZMod.val_lt x.a
  simp only [enc_eq]
  omega

theorem enc_lt (x : Q0) : enc x < 128 := by
  have h1 : x.a.val < 2 := ZMod.val_lt x.a
  have h2 := packVec_lt x.v
  simp only [enc_eq]
  omega

theorem dec_enc (x : Q0) : dec (enc x) = x := by
  apply Q0.ext
  · show Code.bitZ (enc x) 0 = x.a
    have h1 : (Code.bitZ (enc x) 0).val = x.a.val := by
      unfold Code.bitZ
      rw [enc_eq]
      rcases CFSG.RankThree.Literature.FSmith.zmod2_cases x.a with h | h
      · rw [h, ZMod.val_zero]
        rw [testBit_zero_add_two_mul 0 (packVec x.v) (by norm_num)]
        simp
      · rw [h, ZMod.val_one]
        rw [testBit_zero_add_two_mul 1 (packVec x.v) (by norm_num)]
        decide
    exact ZMod.val_injective 2 h1
  · show Code.vec (enc x / 2) = x.v
    rw [enc_div_two, vec_packVec]

theorem enc_dec {n : ℕ} (h : n < 128) : enc (dec n) = n := by
  have h1 : (Code.bitZ n 0).val = if n.testBit 0 then 1 else 0 := by
    unfold Code.bitZ
    split
    · rw [ZMod.val_one]
    · rw [ZMod.val_zero]
  have h2 : packVec (Code.vec (n / 2)) = n / 2 := packVec_vec (by omega)
  have h3 : (if n.testBit 0 then 1 else 0) = n % 2 := by
    rw [Nat.testBit_zero]
    by_cases hc : n % 2 = 1
    · simp [hc]
    · have hlt := Nat.mod_lt n (by norm_num : 0 < 2)
      have hc0 : n % 2 = 0 := by omega
      simp [hc, hc0]
  show (Code.bitZ n 0).val + 2 * packVec (Code.vec (n / 2)) = n
  rw [h1, h2, h3]
  have hd := Nat.div_add_mod n 2
  omega

theorem enc_injective : Function.Injective enc := by
  intro x y h
  rw [← dec_enc x, ← dec_enc y, h]

theorem enc_one : enc 1 = 0 := by
  simp [enc_eq, packVec_zero]

theorem enc_z0 : enc z0 = z0N := by
  simp only [enc_eq, z0, z0N, packVec_zero, ZMod.val_one]

theorem enc_a0 : enc a0 = a0N := by
  have h : packVec (Code.vec 1) = 1 := packVec_vec (by norm_num)
  simp [enc_eq, a0, a0N, h]

theorem packVec_add (u v : V₀) : packVec (u + v) = packVec u ^^^ packVec v := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_xor]
  by_cases hk : k < 6
  · rw [packVec_testBit' (u + v) k hk, packVec_testBit' u k hk, packVec_testBit' v k hk]
    show ((u + v) ⟨k, hk⟩ == 1) = ((u ⟨k, hk⟩ == 1) ^^ (v ⟨k, hk⟩ == 1))
    have hpi : (u + v) ⟨k, hk⟩ = u ⟨k, hk⟩ + v ⟨k, hk⟩ := rfl
    rw [hpi, zmod2_eq_one_add]
  · have hk6 : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : packVec (u + v) < 2 ^ k := by
      have := packVec_lt (u + v); omega
    rw [Nat.testBit_eq_false_of_lt h1, Nat.testBit_eq_false_of_lt (by have := packVec_lt u; omega),
      Nat.testBit_eq_false_of_lt (by have := packVec_lt v; omega)]
    simp

theorem b0n_packVec (u v : V₀) : b0n (packVec u) (packVec v) = (beta0 u v == 1) := by
  rw [show beta0 u v = u 1 * v 0 + u 3 * v 2 + u 5 * v 4 from rfl]
  rw [b0n, packVec_testBit' u 1 (by norm_num), packVec_testBit' v 0 (by norm_num),
    packVec_testBit' u 3 (by norm_num), packVec_testBit' v 2 (by norm_num),
    packVec_testBit' u 5 (by norm_num), packVec_testBit' v 4 (by norm_num)]
  rw [zmod2_eq_one_add, zmod2_eq_one_add, zmod2_eq_one_mul, zmod2_eq_one_mul, zmod2_eq_one_mul]
  rfl

theorem qmulN_enc (x y : Q0) : qmulN (enc x) (enc y) = enc (x * y) := by
  simp only [qmulN, enc_mod_two, enc_div_two]
  rw [enc_eq, mul_a, mul_v]
  have hb0 : (if b0n (packVec x.v) (packVec y.v) then 1 else 0) =
      (beta0 x.v y.v).val := by
    rw [b0n_packVec, zmod2_val_eq_ite]
  have hxor : x.a.val ^^^ y.a.val ^^^ (beta0 x.v y.v).val =
      (x.a + y.a + beta0 x.v y.v).val := by
    rw [zmod2_val_add (x.a + y.a) (beta0 x.v y.v), zmod2_val_add x.a y.a]
  rw [hb0, hxor, packVec_add]

theorem qinvN_enc (x : Q0) : qinvN (enc x) = enc x⁻¹ := by
  simp only [qinvN, enc_mod_two, enc_div_two]
  rw [enc_eq, inv_a, inv_v]
  have hb0 : (if b0n (packVec x.v) (packVec x.v) then 1 else 0) =
      (beta0 x.v x.v).val := by
    rw [b0n_packVec, zmod2_val_eq_ite]
  have hxor : x.a.val ^^^ (beta0 x.v x.v).val = (x.a + beta0 x.v x.v).val := by
    rw [zmod2_val_add x.a (beta0 x.v x.v)]
  rw [hb0, hxor]

@[expose] noncomputable def tabOf (φ : Q0 ≃* Q0) : Array ℕ :=
  Array.ofFn (n := 128) fun i => enc (φ (dec i))

theorem tabOf_size (φ : Q0 ≃* Q0) : (tabOf φ).size = 128 := by
  simp [tabOf]

theorem tabOf_getElem! (φ : Q0 ≃* Q0) (x : Q0) : (tabOf φ)[enc x]! = enc (φ x) := by
  rw [getElem!_pos _ _ (by rw [tabOf_size]; exact enc_lt x)]
  simp only [tabOf, Array.getElem_ofFn, Array.size_ofFn]
  rw [dec_enc]

theorem tabOf_injective : Function.Injective tabOf := by
  intro φ ψ h
  refine MulEquiv.ext fun x => enc_injective ?_
  calc enc (φ x) = (tabOf φ)[enc x]! := (tabOf_getElem! φ x).symm
    _ = (tabOf ψ)[enc x]! := by rw [h]
    _ = enc (ψ x) := tabOf_getElem! ψ x

theorem qmulN_ofFn {x y : ℕ} (hx : x < 128) (hy : y < 128) :
    (Array.ofFn (n := 16384) fun i : Fin 16384 =>
      qmulN (i.val / 128) (i.val % 128))[x * 128 + y]'(by
      simp; omega) = qmulN x y := by
  rw [Array.getElem_ofFn]
  have hdiv : (x * 128 + y) / 128 = x := by
    rw [Nat.mul_comm x 128, Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt hy, Nat.add_zero]
  have hmod : (x * 128 + y) % 128 = y := by
    rw [Nat.mul_comm x 128, Nat.mul_add_mod, Nat.mod_eq_of_lt hy]
  rw [hdiv, hmod]

theorem qmulFlat_getElem! {x y : ℕ} (hx : x < 128) (hy : y < 128) :
    (qmulFlat ())[x * 128 + y]! = qmulN x y := by
  have hidx : x * 128 + y < (qmulFlat ()).size := by
    simp [qmulFlat]
    omega
  rw [Array.getElem!_eq_getD, ← Array.getElem_eq_getD (fallback := default) (h := hidx)]
  exact qmulN_ofFn hx hy

theorem isHomTab_components {t : Array ℕ} (h : isHomTab t = true) :
    t.size = 128 ∧ (∀ i < 128, t[i]! < 128) ∧
      (∀ x < 128, ∀ y < 128, t[qmulN x y]! = qmulN (t[x]!) (t[y]!)) ∧
      (hashSetOfArray t).size = 128 := by
  rw [isHomTab, isHomTabWith] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hsize, hlt⟩, hhom⟩, hhash⟩ := h
  have hentry : ∀ i < 128, t[i]! < 128 := by
    intro i hi
    have h1 : ∀ j < t.size, t[j]! < 128 := by
      intro j hj
      have h2 := Array.all_eq_true.mp hlt j hj
      rw [getElem!_pos t j hj]
      simpa using h2
    exact h1 i (by omega)
  refine ⟨hsize, hentry, ?_, hhash⟩
  intro x hx y hy
  have h1 : ∀ i, i ∈ Array.range 128 →
      ((Array.range 128).all fun y => t[qmulFlat[i * 128 + y]!]! ==
        qmulFlat[t[i]! * 128 + t[y]!]!) = true := Array.all_eq_true'.mp hhom
  have h2 : ∀ j, j ∈ Array.range 128 →
      (t[qmulFlat[x * 128 + j]!]! == qmulFlat[t[x]! * 128 + t[j]!]!) = true :=
    Array.all_eq_true'.mp (h1 x (by simpa using hx))
  have h3 := h2 y (by simpa using hy)
  rw [beq_iff_eq] at h3
  rw [qmulFlat_getElem! hx hy] at h3
  rw [qmulFlat_getElem! (hentry x hx) (hentry y hy)] at h3
  exact h3

private theorem mem_foldl_insert_iff : ∀ (l : List ℕ) (s : Std.HashSet ℕ) (x : ℕ),
    x ∈ l.foldl (fun s x => s.insert x) s ↔ x ∈ l ∨ x ∈ s
  | [], s, x => by simp
  | a :: l, s, x => by
    rw [List.foldl_cons, mem_foldl_insert_iff l (s.insert a) x, Std.HashSet.mem_insert,
      beq_iff_eq, List.mem_cons]
    tauto

theorem tab_injective_of_hashSet {t : Array ℕ} (hsize : t.size = 128)
    (h : (hashSetOfArray t).size = 128) :
    ∀ i < 128, ∀ j < 128, t[i]! = t[j]! → i = j := by
  have hS_nodup : (hashSetOfArray t).toList.Nodup := by
    have hpair := Std.HashSet.distinct_toList (m := hashSetOfArray t)
    rw [List.nodup_iff_pairwise_ne]
    exact List.Pairwise.imp (fun {a b} hab => by simpa [beq_iff_eq] using hab) hpair
  have hsub1 : (hashSetOfArray t).toList.toFinset ⊆ t.toList.toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    have hxS : x ∈ hashSetOfArray t := Std.HashSet.mem_toList.mp hx
    have hx' : x ∈ t.toList.foldl (fun s x => s.insert x) (∅ : Std.HashSet ℕ) := by
      rw [hashSetOfArray, ← Array.foldl_toList] at hxS
      exact hxS
    rcases (mem_foldl_insert_iff t.toList ∅ x).mp hx' with h' | h'
    · exact h'
    · exact absurd h' (by simp)
  have hsub2 : t.toList.toFinset ⊆ (hashSetOfArray t).toList.toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    have h1 : x ∈ t.toList.foldl (fun s x => s.insert x) (∅ : Std.HashSet ℕ) :=
      (mem_foldl_insert_iff t.toList ∅ x).mpr (Or.inl hx)
    have h2 : x ∈ hashSetOfArray t := by
      rw [hashSetOfArray, ← Array.foldl_toList]
      exact h1
    exact Std.HashSet.mem_toList.mpr h2
  have hfin : (hashSetOfArray t).toList.toFinset = t.toList.toFinset :=
    Finset.Subset.antisymm hsub1 hsub2
  have hcard : t.toList.toFinset.card = 128 := by
    rw [← hfin, List.toFinset_card_of_nodup hS_nodup, Std.HashSet.length_toList, h]
  have htnodup : t.toList.Nodup := by
    rw [List.nodup_iff_length_dedup_eq, ← List.card_toFinset, hcard, Array.length_toList, hsize]
  intro i hi j hj hij
  have hi' : i < t.toList.length := by rw [Array.length_toList, hsize]; exact hi
  have hj' : j < t.toList.length := by rw [Array.length_toList, hsize]; exact hj
  have hlist : t.toList[i] = t.toList[j] := by
    rw [← getElem!_eq_getElem_of_lt hi', ← getElem!_eq_getElem_of_lt hj',
      Array.getElem!_toList, Array.getElem!_toList, hij]
  exact htnodup.getElem_inj_iff.mp hlist

theorem ofTabFun_one {t : Array ℕ} (h : isHomTab t = true) : dec t[enc 1]! = 1 := by
  have hc := isHomTab_components h
  have h0 := hc.2.2.1 0 (by norm_num) 0 (by norm_num)
  have hq0 : qmulN 0 0 = 0 := by decide +kernel
  rw [hq0] at h0
  have hA : enc (dec (t[0]!)) = t[0]! := enc_dec (hc.2.1 0 (by norm_num))
  have hy : dec t[0]! = dec t[0]! * dec t[0]! := by
    conv_lhs => rw [h0]
    rw [← hA, qmulN_enc, dec_enc, dec_enc]
  have h1 : (dec t[0]!)⁻¹ * (dec t[0]!) = (dec t[0]!)⁻¹ * (dec t[0]! * dec t[0]!) := by
    rw [← hy]
  have h2 : (dec t[0]!)⁻¹ * (dec t[0]! * dec t[0]!) = dec t[0]! := by
    rw [← mul_assoc, inv_mul_cancel, one_mul]
  rw [inv_mul_cancel, h2] at h1
  have h3 : dec t[0]! = 1 := h1.symm
  rw [enc_one]
  exact h3

theorem ofTabFun_mul {t : Array ℕ} (h : isHomTab t = true) (x y : Q0) :
    dec t[enc (x * y)]! = dec t[enc x]! * dec t[enc y]! := by
  have hc := isHomTab_components h
  rw [show enc (x * y) = qmulN (enc x) (enc y) from (qmulN_enc x y).symm]
  rw [hc.2.2.1 (enc x) (enc_lt x) (enc y) (enc_lt y)]
  rw [← enc_dec (hc.2.1 (enc x) (enc_lt x)), ← enc_dec (hc.2.1 (enc y) (enc_lt y))]
  rw [qmulN_enc, dec_enc, dec_enc, dec_enc]

theorem ofTabFun_injective {t : Array ℕ} (h : isHomTab t = true) :
    ∀ x y : Q0, dec t[enc x]! = dec t[enc y]! → x = y := by
  have hc := isHomTab_components h
  intro x y hxy
  have h1 : t[enc x]! = t[enc y]! := by
    have h2 := congrArg enc hxy
    rwa [enc_dec (hc.2.1 (enc x) (enc_lt x)), enc_dec (hc.2.1 (enc y) (enc_lt y))] at h2
  have h2 : enc x = enc y := tab_injective_of_hashSet hc.1 hc.2.2.2 (enc x) (enc_lt x)
    (enc y) (enc_lt y) h1
  exact enc_injective h2

@[expose] noncomputable def ofTabFun (t : Array ℕ) (h : isHomTab t = true) : Q0 →* Q0 where
  toFun x := dec t[enc x]!
  map_one' := ofTabFun_one h
  map_mul' x y := ofTabFun_mul h x y

theorem ofTabFun_apply (t : Array ℕ) (h : isHomTab t = true) (x : Q0) :
    ofTabFun t h x = dec t[enc x]! := rfl

@[expose] noncomputable def ofTab (t : Array ℕ) (h : isHomTab t = true) : Q0 ≃* Q0 :=
  MulEquiv.ofBijective (ofTabFun t h)
    ⟨ofTabFun_injective h, Finite.injective_iff_surjective.mp (ofTabFun_injective h)⟩

theorem ofTab_apply (t : Array ℕ) (h : isHomTab t = true) (x : Q0) :
    ofTab t h x = dec t[enc x]! := rfl

theorem tabOf_ofTab (t : Array ℕ) (h : isHomTab t = true) : tabOf (ofTab t h) = t := by
  have hc := isHomTab_components h
  apply Array.ext
  · rw [tabOf_size, hc.1]
  · intro i hi hi'
    have hi128 : i < 128 := by simpa [tabOf_size] using hi
    rw [Array.getElem_eq_getD (fallback := default) (h := hi),
      Array.getElem_eq_getD (fallback := default) (h := hi'),
      ← Array.getElem!_eq_getD (xs := tabOf (ofTab t h)) (i := i),
      ← Array.getElem!_eq_getD (xs := t) (i := i)]
    have h1 : (tabOf (ofTab t h))[i]! = enc (ofTab t h (dec i)) := by
      have h := tabOf_getElem! (ofTab t h) (dec i)
      rwa [enc_dec hi128] at h
    rw [h1, ofTab_apply, enc_dec hi128, enc_dec (hc.2.1 i hi128)]

theorem exists_tabOf_eq (t : Array ℕ) (h : isHomTab t = true) : ∃ φ, tabOf φ = t :=
  ⟨ofTab t h, tabOf_ofTab t h⟩

theorem array_eq_of_getElem!_eq {s t : Array ℕ} (hs : s.size = 128) (ht : t.size = 128)
    (h : ∀ i < 128, s[i]! = t[i]!) : s = t := by
  apply Array.ext_getElem?
  intro i
  by_cases hi : i < 128
  · rw [Array.getElem?_eq_some_getElem! s i (by rw [hs]; exact hi),
      Array.getElem?_eq_some_getElem! t i (by rw [ht]; exact hi), h i hi]
  · have h1 : s[i]? = none := by rw [getElem?_eq_none_iff, hs]; omega
    have h2 : t[i]? = none := by rw [getElem?_eq_none_iff, ht]; omega
    rw [h1, h2]

theorem compTab_getElem! (s t : Array ℕ) {i : ℕ} (hi : i < 128) :
    (compTab s t)[i]! = s[t[i]!]! := by
  have hidx : i < (compTab s t).size := by simp [compTab]; omega
  rw [Array.getElem!_eq_getD, ← Array.getElem_eq_getD (fallback := default) (h := hidx)]
  simp only [compTab, Array.getElem_ofFn, Array.size_ofFn]

private theorem foldl_if_true (t : Array ℕ) : ∀ (l : List ℕ) (r : Array ℕ),
    (∀ x ∈ l, t[x]! < 128) →
    l.foldl (fun (r : Array ℕ) x => if t[x]! < 128 then r.set! (t[x]!) x else r) r
      = l.foldl (fun (r : Array ℕ) x => r.set! (t[x]!) x) r
  | [], r, _ => rfl
  | a :: l, r, h => by
    rw [List.foldl_cons, List.foldl_cons, if_pos (h a (by simp))]
    exact foldl_if_true t l (r.set! (t[a]!) a) (fun x hx => h x (by simp [hx]))

theorem ofFn_getElem! {n : ℕ} {f : Fin n → ℕ} {i : ℕ} (hi : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  have hidx : i < (Array.ofFn f).size := by simpa using hi
  rw [Array.getElem!_eq_getD, ← Array.getElem_eq_getD (fallback := default) (h := hidx)]
  simp only [Array.getElem_ofFn, Array.size_ofFn]

theorem invTab_size (t : Array ℕ) : (invTab t).size = 128 := by
  rw [invTab]
  have h : ∀ (l : List ℕ) (r : Array ℕ),
      (l.foldl (fun (r : Array ℕ) x => if t[x]! < 128 then r.set! (t[x]!) x else r) r).size
        = r.size := by
    intro l
    induction l with
    | nil => intro r; rfl
    | cons a l ih =>
      intro r
      rw [List.foldl_cons, ih]
      split
      · rw [Array.size_set!]
      · rfl
  rw [h]
  simp

theorem invTab_getElem! {t : Array ℕ} (hsize : t.size = 128)
    (hlt : ∀ i < 128, t[i]! < 128)
    (hinj : ∀ i < 128, ∀ j < 128, t[i]! = t[j]! → i = j)
    {x : ℕ} (hx : x < 128) : (invTab t)[t[x]!]! = x := by
  have haux : ∀ (k : ℕ), k ≤ 128 → ∀ x < k,
      ((List.range k).foldl (fun (r : Array ℕ) x => r.set! (t[x]!) x)
        (Array.replicate 128 0))[t[x]!]! = x := by
    intro k
    induction k with
    | zero => intro _ x hx; omega
    | succ k ih =>
      intro hk x hx
      have hk128 : k < 128 := by omega
      have hstep : (List.range (k + 1)).foldl (fun (r : Array ℕ) x => r.set! (t[x]!) x)
            (Array.replicate 128 0)
          = ((List.range k).foldl (fun (r : Array ℕ) x => r.set! (t[x]!) x)
            (Array.replicate 128 0)).set! (t[k]!) k := by
        rw [List.range_succ, List.foldl_append]
        simp
      rw [hstep]
      have hrsize : ((List.range k).foldl (fun (r : Array ℕ) x => r.set! (t[x]!) x)
          (Array.replicate 128 0)).size = 128 := by
        have h : ∀ (l : List ℕ) (r : Array ℕ),
            (l.foldl (fun (r : Array ℕ) x => r.set! (t[x]!) x) r).size = r.size := by
          intro l
          induction l with
          | nil => intro r; rfl
          | cons a l ih =>
            intro r
            rw [List.foldl_cons, ih, Array.size_set!]
        rw [h]
        simp
      by_cases hxk : x = k
      · rw [hxk]
        rw [Array.getElem!_set!_self _ _ _ (by rw [hrsize]; exact hlt k hk128)]
      · have hx' : x < k := by omega
        rw [Array.getElem!_set!_ne _ _ _ _ (by
          intro h
          exact absurd (hinj k hk128 x (by omega) h) (by omega))]
        exact ih (by omega) x hx'
  rw [invTab, foldl_if_true t (List.range 128) (Array.replicate 128 0) (fun x hx => by
    rw [List.mem_range] at hx
    exact hlt x hx)]
  exact haux 128 (by norm_num) x hx

theorem innTab_getElem! (e : ℕ) {i : ℕ} (hi : i < 128) :
    (innTab e)[i]! = qmulN (qmulN (qinvN e) i) e := by
  have hidx : i < (innTab e).size := by simp [innTab]; omega
  rw [Array.getElem!_eq_getD, ← Array.getElem_eq_getD (fallback := default) (h := hidx)]
  simp only [innTab, Array.getElem_ofFn, Array.size_ofFn]

theorem tabOf_mul (φ ψ : Q0 ≃* Q0) : tabOf (φ * ψ) = compTab (tabOf φ) (tabOf ψ) := by
  apply array_eq_of_getElem!_eq (tabOf_size _) (by simp [compTab])
  intro i hi
  have hii : enc (dec i) = i := enc_dec hi
  rw [← hii]
  rw [tabOf_getElem! (φ * ψ) (dec i),
    compTab_getElem! _ _ (by rw [enc_dec hi]; exact hi), tabOf_getElem! ψ (dec i),
    tabOf_getElem! φ (ψ (dec i))]
  rfl

theorem tabOf_inv (φ : Q0 ≃* Q0) : tabOf φ⁻¹ = invTab (tabOf φ) := by
  apply array_eq_of_getElem!_eq (tabOf_size (φ⁻¹)) (invTab_size (tabOf φ))
  intro i hi
  have hii : enc (dec i) = i := enc_dec hi
  rw [← hii]
  rw [tabOf_getElem! φ⁻¹ (dec i)]
  have hinj : ∀ a < 128, ∀ b < 128, (tabOf φ)[a]! = (tabOf φ)[b]! → a = b := by
    intro a ha b hb hab
    have h1 : (tabOf φ)[enc (dec a)]! = (tabOf φ)[enc (dec b)]! := by
      rwa [enc_dec ha, enc_dec hb]
    rw [tabOf_getElem! φ (dec a), tabOf_getElem! φ (dec b)] at h1
    have h2 : φ (dec a) = φ (dec b) := enc_injective h1
    have h3 : dec a = dec b := φ.injective h2
    rw [← enc_dec ha, ← enc_dec hb, h3]
  have hb : (tabOf φ)[enc (φ⁻¹ (dec i))]! = enc (dec i) := by
    rw [tabOf_getElem! φ (φ⁻¹ (dec i)), show φ (φ⁻¹ (dec i)) = dec i from by simp, enc_dec hi]
  have hx : enc (φ⁻¹ (dec i)) < 128 := enc_lt _
  have hlt : ∀ j < 128, (tabOf φ)[j]! < 128 := by
    intro j hj
    rw [← enc_dec hj, tabOf_getElem! φ (dec j)]
    exact enc_lt _
  have hmain := invTab_getElem! (tabOf_size φ) hlt hinj hx
  rw [hb] at hmain
  exact hmain.symm

theorem tabOf_inn (e : Q0) : tabOf (inn e) = innTab (enc e) := by
  apply array_eq_of_getElem!_eq (tabOf_size _) (by simp [innTab])
  intro i hi
  have hii : enc (dec i) = i := enc_dec hi
  rw [← hii]
  rw [tabOf_getElem! (inn e) (dec i), innTab_getElem! (enc e) (by rw [enc_dec hi]; exact hi),
    qinvN_enc]
  rw [qmulN_enc (e⁻¹) (dec i), qmulN_enc (e⁻¹ * dec i) e]
  congr 1
  rw [inn, MulAut.conj_apply, inv_inv]

theorem innTabs_getElem! {e : ℕ} (he : e < 128) : (innTabs ())[e]! = innTab e := by
  have hidx : e < (innTabs ()).size := by simp [innTabs]; omega
  rw [Array.getElem!_eq_getD, ← Array.getElem_eq_getD (fallback := default) (h := hidx)]
  simp only [innTabs, Array.getElem_ofFn, Array.size_ofFn]

theorem tabOf_one : tabOf (1 : Q0 ≃* Q0) = Array.ofFn (n := 128) fun i => i.val := by
  apply array_eq_of_getElem!_eq (tabOf_size _) (by simp)
  intro i hi
  have hii : enc (dec i) = i := enc_dec hi
  rw [← hii]
  rw [tabOf_getElem! (1 : Q0 ≃* Q0) (dec i), ofFn_getElem! (by rw [enc_dec hi]; exact hi)]
  simp

@[expose] def fStep (g f : ℕ) (F : Array Bool) (v : ℕ) : Array Bool :=
  if v = 0 then F
  else
    let j := lowIdx v
    let e := 1 <<< j
    let w := v ^^^ e
    F.set! v (F[w]! ^^ f.testBit j ^^ b0n (Code.act g w) (Code.act g e) ^^ b0n w e)

theorem fTable_eq_foldl (g f : ℕ) :
    fTable g f = (List.range 64).foldl (fStep g f) (Array.replicate 64 false) := rfl

theorem lowIdx_lt_six (v : ℕ) : lowIdx v < 6 := by
  simp only [lowIdx]
  split_ifs <;> omega

theorem lowIdx_spec {v : ℕ} (hv : v ≠ 0) (hv64 : v < 64) : v.testBit (lowIdx v) = true := by
  by_cases h0 : v.testBit 0 = true
  · simpa [lowIdx, h0] using h0
  by_cases h1 : v.testBit 1 = true
  · simpa [lowIdx, h0, h1] using h1
  by_cases h2 : v.testBit 2 = true
  · simpa [lowIdx, h0, h1, h2] using h2
  by_cases h3 : v.testBit 3 = true
  · simpa [lowIdx, h0, h1, h2, h3] using h3
  by_cases h4 : v.testBit 4 = true
  · simpa [lowIdx, h0, h1, h2, h3, h4] using h4
  by_cases h5 : v.testBit 5 = true
  · simpa [lowIdx, h0, h1, h2, h3, h4, h5] using h5
  · exfalso
    apply hv
    apply Nat.zero_of_testBit_eq_false
    intro k
    by_cases hk : k < 6
    · interval_cases k
      · simpa using h0
      · simpa using h1
      · simpa using h2
      · simpa using h3
      · simpa using h4
      · simpa using h5
    · refine Nat.testBit_eq_false_of_lt ?_
      have h64 : v < 2 ^ 6 := by simpa using hv64
      exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem lowIdx_xor_lt {v : ℕ} (hv : v ≠ 0) (hv64 : v < 64) :
    v ^^^ (1 <<< lowIdx v) < v := by
  have hbit := lowIdx_spec hv hv64
  rw [Nat.one_shiftLeft]
  refine Nat.lt_of_testBit (lowIdx v) ?_ hbit ?_
  · rw [Nat.testBit_xor, Nat.testBit_two_pow_self, hbit]
    simp
  · intro j hj
    rw [Nat.testBit_xor, Nat.testBit_two_pow_of_ne (by omega)]
    simp

theorem lowIdx_two_pow {j : ℕ} (hj : j < 6) : lowIdx (2 ^ j) = j := by
  interval_cases j <;> decide +kernel

theorem act_zero (g : ℕ) : Code.act g 0 = 0 := by
  simp [Code.act, Code.sel, Code.col]

theorem fStep_size (g f : ℕ) (F : Array Bool) (v : ℕ) : (fStep g f F v).size = F.size := by
  unfold fStep
  split
  · rfl
  · dsimp only
    exact Array.size_set! F v _

theorem fStep_of_eq (g f : ℕ) (F : Array Bool) : fStep g f F 0 = F := by
  unfold fStep
  rw [if_pos rfl]

theorem fStep_of_ne (g f : ℕ) (F : Array Bool) {v : ℕ} (hv : v ≠ 0) :
    fStep g f F v = F.set! v (F[v ^^^ (1 <<< lowIdx v)]! ^^ f.testBit (lowIdx v) ^^
      b0n (Code.act g (v ^^^ (1 <<< lowIdx v))) (Code.act g (1 <<< lowIdx v)) ^^
      b0n (v ^^^ (1 <<< lowIdx v)) (1 <<< lowIdx v)) := by
  unfold fStep
  rw [if_neg hv]

theorem fTable_foldl_size (g f : ℕ) : ∀ (l : List ℕ) (F : Array Bool),
    (l.foldl (fStep g f) F).size = F.size
  | [], F => rfl
  | a :: l, F => by
    rw [List.foldl_cons, fTable_foldl_size g f l, fStep_size]

theorem foldl_fStep_getElem (g f : ℕ) : ∀ (k : ℕ), k ≤ 64 → ∀ v < k,
    ((List.range k).foldl (fStep g f) (Array.replicate 64 false))[v]! =
      if v = 0 then false
      else
        ((List.range k).foldl (fStep g f) (Array.replicate 64 false))[v ^^^ (1 <<< lowIdx v)]! ^^
          f.testBit (lowIdx v) ^^
          b0n (Code.act g (v ^^^ (1 <<< lowIdx v))) (Code.act g (1 <<< lowIdx v)) ^^
          b0n (v ^^^ (1 <<< lowIdx v)) (1 <<< lowIdx v) := by
  intro k
  induction k with
  | zero => intro _ v hv; omega
  | succ k ih =>
    intro hk v hv
    have hk64 : k < 64 := by omega
    have hstep : (List.range (k + 1)).foldl (fStep g f) (Array.replicate 64 false)
        = fStep g f ((List.range k).foldl (fStep g f) (Array.replicate 64 false)) k := by
      rw [List.range_succ, List.foldl_append]
      rfl
    rw [hstep]
    by_cases hv0 : v = 0
    · rw [hv0, if_pos rfl]
      have h0 : ((List.range k).foldl (fStep g f) (Array.replicate 64 false))[0]! = false := by
        rcases Nat.eq_or_lt_of_le (Nat.zero_le k) with hk0 | hkpos
        · subst hk0
          simp
        · rw [ih (by omega) 0 hkpos]
          simp
      rcases eq_or_ne k 0 with hk0 | hk0
      · subst hk0
        rw [fStep_of_eq]
        simpa using h0
      · rw [fStep_of_ne g f _ hk0, Array.getElem!_set!_ne _ _ _ _ (by omega : k ≠ 0)]
        exact h0
    · rw [if_neg hv0]
      rcases Nat.lt_or_ge v k with hvk | hvk
      · have hstepv :
            (fStep g f ((List.range k).foldl (fStep g f) (Array.replicate 64 false)) k)[v]!
            = ((List.range k).foldl (fStep g f) (Array.replicate 64 false))[v]! := by
          unfold fStep
          split
          · omega
          · exact Array.getElem!_set!_ne _ _ _ _ (by omega)
        rw [hstepv, ih (by omega) v hvk]
        rw [if_neg hv0]
        have hw : v ^^^ (1 <<< lowIdx v) < k := by
          have := lowIdx_xor_lt hv0 (by omega)
          omega
        have hstepw :
            (fStep g f ((List.range k).foldl (fStep g f) (Array.replicate 64 false)) k)[
              v ^^^ (1 <<< lowIdx v)]!
            = ((List.range k).foldl (fStep g f) (Array.replicate 64 false))[
              v ^^^ (1 <<< lowIdx v)]! := by
          rw [fStep_of_ne g f _ (by omega)]
          exact Array.getElem!_set!_ne _ _ _ _ (by omega)
        rw [hstepw]
      · have hvkeq : v = k := by omega
        rw [hvkeq]
        have hstepv :
            (fStep g f ((List.range k).foldl (fStep g f) (Array.replicate 64 false)) k)[k]!
            = (((List.range k).foldl (fStep g f) (Array.replicate 64 false))[
                k ^^^ (1 <<< lowIdx k)]! ^^
              f.testBit (lowIdx k) ^^
              b0n (Code.act g (k ^^^ (1 <<< lowIdx k))) (Code.act g (1 <<< lowIdx k)) ^^
              b0n (k ^^^ (1 <<< lowIdx k)) (1 <<< lowIdx k)) := by
          rw [fStep_of_ne g f _ (by omega : k ≠ 0)]
          exact Array.getElem!_set!_self _ _ _ (by rw [fTable_foldl_size]; simpa using hk64)
        rw [hstepv]
        have hw : k ^^^ (1 <<< lowIdx k) < k := lowIdx_xor_lt (by omega) (by omega)
        have hstepw :
            (fStep g f ((List.range k).foldl (fStep g f) (Array.replicate 64 false)) k)[
              k ^^^ (1 <<< lowIdx k)]!
            = ((List.range k).foldl (fStep g f) (Array.replicate 64 false))[
              k ^^^ (1 <<< lowIdx k)]! := by
          rw [fStep_of_ne g f _ (by omega)]
          exact Array.getElem!_set!_ne _ _ _ _ (by omega)
        rw [hstepw]

theorem fTable_getElem!_zero (g f : ℕ) : (fTable g f)[0]! = false := by
  rw [fTable_eq_foldl]
  have h := foldl_fStep_getElem g f 64 (le_refl 64) 0 (by norm_num)
  simpa using h

theorem fTable_getElem!_succ {g f v : ℕ} (hv : v < 64) (hv0 : v ≠ 0) :
    (fTable g f)[v]! = ((fTable g f)[v ^^^ (1 <<< lowIdx v)]! ^^ f.testBit (lowIdx v) ^^
      b0n (Code.act g (v ^^^ (1 <<< lowIdx v))) (Code.act g (1 <<< lowIdx v)) ^^
      b0n (v ^^^ (1 <<< lowIdx v)) (1 <<< lowIdx v)) := by
  rw [fTable_eq_foldl]
  have h := foldl_fStep_getElem g f 64 (le_refl 64) v hv
  rwa [if_neg hv0] at h

theorem fTable_two_pow {g f : ℕ} {j : ℕ} (hj : j < 6) :
    (fTable g f)[2 ^ j]! = f.testBit j := by
  have hv64 : 2 ^ j < 64 := by
    calc 2 ^ j < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) hj
      _ = 64 := by norm_num
  have hv0 : 2 ^ j ≠ 0 := by positivity
  rw [fTable_getElem!_succ hv64 hv0, lowIdx_two_pow hj, Nat.one_shiftLeft, Nat.xor_self,
    act_zero, fTable_getElem!_zero]
  simp [b0n]

theorem liftTab_size (g f : ℕ) : (liftTab g f).size = 128 := by
  simp [liftTab]

theorem liftTab_getElem! {g f i : ℕ} (hi : i < 128) :
    (liftTab g f)[i]! = ((i % 2) ^^^ (if (fTable g f)[i / 2]! then 1 else 0)) +
      2 * Code.act g (i / 2) := by
  have hidx : i < (liftTab g f).size := by rw [liftTab_size]; exact hi
  rw [Array.getElem!_eq_getD, ← Array.getElem_eq_getD (fallback := default) (h := hidx)]
  simp only [liftTab, Array.getElem_ofFn, Array.size_ofFn]

theorem vec_xor (a b : ℕ) : Code.vec (a ^^^ b) = Code.vec a + Code.vec b := by
  funext i
  simp only [Code.vec, Pi.add_apply, Code.bitZ_xor]

theorem exists_liftTab_eq {u : V₀ ≃ₗ[ZMod 2] V₀} {g : ℕ}
    (hg : Code.HasCode (u : V₀ →ₗ[ZMod 2] V₀) g)
    {θ : Q0 ≃* Q0} (hθ : ∀ x, (θ x).v = u x.v) : ∃ f < 64, tabOf θ = liftTab g f := by
  have hcenter : ∀ c : Q0, c ∈ Subgroup.center Q0 → θ c = c := fun c hc =>
    CFSG.GroupTheory.mulAut_apply_eq_of_mem_center (by rw [center_eq_Q0Z, card_Q0Z]) θ hc
  have hform : ∀ x : Q0, θ x = ⟨x.a + (θ ⟨0, x.v⟩).a, u x.v⟩ := by
    intro x
    have hx : x = (⟨0, x.v⟩ : Q0) * ⟨x.a, 0⟩ := by
      have h : ((⟨0, x.v⟩ : Q0) * ⟨x.a, 0⟩) = ⟨x.a, x.v⟩ := by
        apply Q0.ext <;> simp [mul_a, mul_v, beta0]
      rw [h]
    conv_lhs => rw [hx]
    rw [map_mul, hcenter (⟨x.a, 0⟩) (by simp [center_eq_Q0Z, mem_Q0Z_iff])]
    apply Q0.ext
    · simp only [mul_a, mul_v, hθ, beta0, Pi.zero_apply, zero_mul, mul_zero, add_zero]
      ring
    · simp only [mul_v, hθ, add_zero]
  have hF0 : (θ ⟨0, (0 : V₀)⟩).a = 0 := by
    have h : θ (⟨0, (0 : V₀)⟩ : Q0) = 1 := map_one θ
    rw [h]
    rfl
  have hFadd : ∀ w e : V₀, (θ ⟨0, w + e⟩).a =
      (θ ⟨0, w⟩).a + (θ ⟨0, e⟩).a + beta0 (u w) (u e) + beta0 w e := by
    intro w e
    have h1 : (⟨0, w + e⟩ : Q0) = (⟨beta0 w e, 0⟩ : Q0) * (⟨0, w⟩ * ⟨0, e⟩) := by
      apply Q0.ext
      · simp only [mul_a, mul_v, beta0, Pi.zero_apply, zero_mul, mul_zero, add_zero, zero_add]
        rw [CharTwo.add_self_eq_zero]
      · simp only [mul_v, add_zero, zero_add]
    have h2 : θ (⟨beta0 w e, 0⟩ : Q0) = ⟨beta0 w e, 0⟩ :=
      hcenter _ (by simp [center_eq_Q0Z, mem_Q0Z_iff])
    rw [h1, map_mul, map_mul, h2]
    simp only [mul_a, mul_v, hθ, beta0, Pi.zero_apply, zero_mul, mul_zero, add_zero]
    ring
  have hact : ∀ n < 64, Code.act g n = packVec (u (Code.vec n)) := by
    intro n hn
    rw [apply_vec_of_hasCode hg n, packVec_vec (Code.act_lt g n)]
  set f : ℕ := packVec (fun i : Fin 6 => (θ ⟨0, Code.vec (2 ^ (i : ℕ))⟩).a) with hf
  have hf_bit : ∀ j < 6, f.testBit j = ((θ ⟨0, Code.vec (2 ^ j)⟩).a == 1) := by
    intro j hj
    have h := packVec_testBit' (fun i : Fin 6 => (θ ⟨0, Code.vec (2 ^ (i : ℕ))⟩).a) j hj
    simpa [f] using h
  rw [hf] at hf_bit
  refine ⟨f, packVec_lt _, ?_⟩
  have hGf : ∀ v, v < 64 → (fTable g f)[v]! = ((θ ⟨0, Code.vec v⟩).a == 1) := by
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ih =>
      intro hv
      by_cases hv0 : v = 0
      · rw [hv0, fTable_getElem!_zero]
        simp [vec_zero, hF0]
      · have hw : v ^^^ (1 <<< lowIdx v) < v := lowIdx_xor_lt hv0 hv
        have hw64 : v ^^^ (1 <<< lowIdx v) < 64 := by omega
        have he64 : 1 <<< lowIdx v < 64 := by
          rw [Nat.one_shiftLeft]
          exact Nat.pow_lt_pow_right (by norm_num) (lowIdx_lt_six v)
        have hsplit : Code.vec v =
            Code.vec (v ^^^ (1 <<< lowIdx v)) + Code.vec (1 <<< lowIdx v) := by
          have hve : v = (v ^^^ (1 <<< lowIdx v)) ^^^ (1 <<< lowIdx v) := by
            rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
          conv_lhs => rw [hve]
          rw [vec_xor]
        have hFv := hFadd (Code.vec (v ^^^ (1 <<< lowIdx v))) (Code.vec (1 <<< lowIdx v))
        rw [← hsplit] at hFv
        have hbit : f.testBit (lowIdx v) = ((θ ⟨0, Code.vec (1 <<< lowIdx v)⟩).a == 1) := by
          rw [Nat.one_shiftLeft]
          exact hf_bit (lowIdx v) (lowIdx_lt_six v)
        have hb1 : b0n (Code.act g (v ^^^ (1 <<< lowIdx v))) (Code.act g (1 <<< lowIdx v)) =
            (beta0 (u (Code.vec (v ^^^ (1 <<< lowIdx v))))
              (u (Code.vec (1 <<< lowIdx v))) == 1) := by
          rw [hact _ hw64, hact _ he64, b0n_packVec]
        have hb2 : b0n (v ^^^ (1 <<< lowIdx v)) (1 <<< lowIdx v) =
            (beta0 (Code.vec (v ^^^ (1 <<< lowIdx v))) (Code.vec (1 <<< lowIdx v)) == 1) := by
          have hh := b0n_packVec (Code.vec (v ^^^ (1 <<< lowIdx v))) (Code.vec (1 <<< lowIdx v))
          rwa [packVec_vec hw64, packVec_vec he64] at hh
        rw [fTable_getElem!_succ hv hv0, ih _ hw hw64, hFv, hbit, hb1, hb2,
          zmod2_eq_one_add, zmod2_eq_one_add, zmod2_eq_one_add]
  apply array_eq_of_getElem!_eq (tabOf_size _) (by rw [liftTab_size])
  intro i hi
  have hii : enc (dec i) = i := enc_dec hi
  rw [← hii]
  rw [tabOf_getElem! θ (dec i), liftTab_getElem! (by rw [enc_dec hi]; exact hi),
    enc_eq, hform]
  have h1 : (dec i).a.val = enc (dec i) % 2 := (enc_mod_two _).symm
  have h2 : enc (dec i) / 2 = packVec (dec i).v := enc_div_two _
  rw [h2]
  have h3 : ((dec i).a + (θ ⟨0, (dec i).v⟩).a).val = (dec i).a.val ^^^ ((θ ⟨0, (dec i).v⟩).a).val :=
    zmod2_val_add _ _
  have h4 : ((θ ⟨0, (dec i).v⟩).a).val = if ((θ ⟨0, (dec i).v⟩).a == 1) then 1 else 0 :=
    zmod2_val_eq_ite _
  have h5 : (fTable g f)[packVec (dec i).v]! = ((θ ⟨0, (dec i).v⟩).a == 1) := by
    rw [hGf (packVec (dec i).v) (packVec_lt _)]
    show ((θ ⟨0, Code.vec (packVec (dec i).v)⟩).a == 1) = _
    rw [vec_packVec]
  rw [h3, h4, h5, ← h1, hact (packVec (dec i).v) (packVec_lt _), vec_packVec]

theorem liftTab_injective {g f f' : ℕ} (hf : f < 64) (hf' : f' < 64)
    (h : liftTab g f = liftTab g f') : f = f' := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 6
  · have hj128 : 2 ^ (j + 1) < 128 := by
      calc 2 ^ (j + 1) < 2 ^ 7 := Nat.pow_lt_pow_right (by norm_num) (by omega)
        _ = 128 := by norm_num
    have h1 : (liftTab g f)[2 ^ (j + 1)]! = (liftTab g f')[2 ^ (j + 1)]! :=
      congrArg (fun t : Array ℕ => t[2 ^ (j + 1)]!) h
    rw [liftTab_getElem! hj128, liftTab_getElem! hj128,
      show (2 : ℕ) ^ (j + 1) % 2 = 0 from by rw [pow_succ]; simp,
      show (2 : ℕ) ^ (j + 1) / 2 = 2 ^ j from by rw [pow_succ]; simp,
      fTable_two_pow hj, fTable_two_pow hj] at h1
    have h2 : (if f.testBit j then 1 else 0) = (if f'.testBit j then 1 else 0) := by
      simpa using Nat.add_right_cancel h1
    cases hfj : f.testBit j <;> cases hfj' : f'.testBit j <;> simp_all
  · rw [Nat.testBit_eq_false_of_lt (by
        have : 2 ^ 6 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega),
      Nat.testBit_eq_false_of_lt (by
        have : 2 ^ 6 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega)]

theorem v_ofTab_liftTab {u : V₀ ≃ₗ[ZMod 2] V₀} {g f : ℕ}
    (hg : Code.HasCode (u : V₀ →ₗ[ZMod 2] V₀) g)
    (h : isHomTab (liftTab g f) = true) (x : Q0) :
    (ofTab (liftTab g f) h x).v = u x.v := by
  rw [ofTab_apply]
  show Code.vec (((liftTab g f)[enc x]!) / 2) = u x.v
  rw [liftTab_getElem! (enc_lt x), enc_mod_two, enc_div_two]
  have hlt : (x.a.val ^^^ (if (fTable g f)[packVec x.v]! then 1 else 0)) < 2 := by
    have h := Nat.xor_lt_two_pow (x := x.a.val)
      (y := if (fTable g f)[packVec x.v]! then 1 else 0) (n := 1)
      (by simpa using ZMod.val_lt x.a) (by split <;> omega)
    simpa using h
  have hdiv : ((x.a.val ^^^ (if (fTable g f)[packVec x.v]! then 1 else 0)) +
      2 * Code.act g (packVec x.v)) / 2 = Code.act g (packVec x.v) := by omega
  rw [hdiv]
  rw [← apply_vec_of_hasCode hg, vec_packVec]

theorem ofTab_liftTab_apply_a0 {g f : ℕ} (h : isHomTab (liftTab g f) = true) :
    ((liftTab g f)[a0N]! = a0N) ↔ ofTab (liftTab g f) h a0 = a0 := by
  have hc := isHomTab_components h
  have hlt : a0N < 128 := by decide +kernel
  constructor
  · intro hh
    rw [ofTab_apply, enc_a0, hh, ← enc_a0]
    exact dec_enc a0
  · intro hh
    rw [ofTab_apply, enc_a0] at hh
    have h3 := congrArg enc hh
    rwa [enc_dec (hc.2.1 a0N hlt), enc_a0] at h3

theorem mem_fixed_iff (φ : Q0 ≃* Q0) (x : Q0) :
    φ x = x ↔ (tabOf φ)[enc x]! = enc x := by
  constructor
  · intro h
    rw [tabOf_getElem!, h]
  · intro h
    rw [tabOf_getElem!] at h
    exact enc_injective h

theorem ncard_fixed (φ : Q0 ≃* Q0) :
    Set.ncard {x : Q0 | φ x = x} =
      ((List.range 128).filter fun x => (tabOf φ)[x]! == x).length := by
  set L : List ℕ := (List.range 128).filter fun x => (tabOf φ)[x]! == x with hL
  set F : Finset ℕ := (Finset.range 128).filter fun n => (tabOf φ)[n]! == n with hF
  have hset : {x : Q0 | φ x = x}.toFinset = F.image dec := by
    ext x
    rw [Set.mem_toFinset, Finset.mem_image]
    constructor
    · intro hx
      refine ⟨enc x, ?_, dec_enc x⟩
      rw [hF, Finset.mem_filter, Finset.mem_range, beq_iff_eq]
      exact ⟨enc_lt x, (mem_fixed_iff φ x).mp hx⟩
    · rintro ⟨n, hn, rfl⟩
      rw [hF, Finset.mem_filter, Finset.mem_range, beq_iff_eq] at hn
      exact (mem_fixed_iff φ (dec n)).mpr (by rw [enc_dec hn.1]; exact hn.2)
  have hinj : Set.InjOn dec (F : Set ℕ) := by
    intro a ha b hb hab
    rw [hF, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
    rw [← enc_dec ha.1, ← enc_dec hb.1, hab]
  have hcard : (F.image dec).card = F.card := Finset.card_image_of_injOn hinj
  have hLnd : L.Nodup := (hL ▸ List.nodup_range.filter _)
  have hFL : F.card = L.length := by
    rw [hF, hL, ← List.toFinset_card_of_nodup hLnd, List.toFinset_filter, List.toFinset_range]
  calc Set.ncard {x : Q0 | φ x = x} = {x : Q0 | φ x = x}.toFinset.card :=
        Set.ncard_eq_toFinset_card' _
    _ = (F.image dec).card := by rw [hset]
    _ = F.card := hcard
    _ = L.length := hFL

theorem findInn_spec {t : Array ℕ} {e : ℕ} (h : findInn (innTabs ()) t = some e) :
    e < 128 ∧ innTab e = t := by
  have hsize : (innTabs ()).size = 128 := by simp [innTabs]
  have hmem := List.mem_of_find?_eq_some h
  rw [List.mem_range, hsize] at hmem
  have hsome := List.find?_some h
  refine ⟨hmem, ?_⟩
  rw [← innTabs_getElem! hmem]
  exact beq_iff_eq.mp hsome

theorem mem_innRoots_iff {t : Array ℕ} {e : ℕ} :
    e ∈ innRoots (innTabs ()) t ↔ e < 128 ∧ innTab e = t := by
  have hsize : (innTabs ()).size = 128 := by simp [innTabs]
  rw [innRoots, List.mem_filter, List.mem_range, hsize]
  constructor
  · rintro ⟨hlt, hsome⟩
    refine ⟨hlt, ?_⟩
    rw [← innTabs_getElem! hlt]
    exact beq_iff_eq.mp hsome
  · rintro ⟨hlt, he⟩
    refine ⟨hlt, ?_⟩
    rw [innTabs_getElem! hlt, he]
    simp

end CFSG.GF2Type.Smith1979W3.Cert690

end

