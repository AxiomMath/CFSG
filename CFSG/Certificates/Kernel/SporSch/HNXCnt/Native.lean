module

public import CFSG.Certificates.Kernel.SporSch.HNXCnt.Base
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.Th.TableSpec
public import Certificates.Data.Kernel.SporSch.HNXBind
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KS.SporSch.HNXP

open CFSG.KC.Enum CFSG.KC.LL CFSG.KS.SporSch CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.F5.Native CFSG.Sporadic.Th.Native

theorem walk_allBlk {g : Nat → Bool} : ∀ {c : Nat}, allBlk 0 g c = true → ∀ j < c, g j = true := by
  intro c h j hj
  have := CFSG.KS.allBlk_spec h j hj
  simpa using this

theorem walkOK_spec {f : Nat → Nat → Bool} :
    ∀ (t : OrbitNats) (o : Nat), t.valid = true → walkOK f t o = true →
      ∀ i < t.size, f (o + i) (t.values[i]!) = true := by
  intro t
  induction t with
  | leaf w c bits =>
    intro o _ h i hi
    have h' : allBlk (nat_lit 0) (fun j => f (Nat.add o j) (fldW bits (Nat.mul w j) w)) c = true := h
    have := walk_allBlk h' i hi
    simp only [OrbitNats.size] at hi
    have e : (OrbitNats.leaf w c bits).values[i]! = (bits >>> (w * i)) % 2 ^ w := by
      simp [OrbitNats.values, hi]
    rw [e, Nat.shiftRight_eq_div_pow]
    rw [fldW_eq] at this
    exact this
  | branch ls a b iha ihb =>
    intro o hv h i hi
    simp only [OrbitNats.valid, Bool.and_eq_true, beq_iff_eq] at hv
    obtain ⟨⟨hva, hvb⟩, hs⟩ := hv
    have h' : Bool.rec (motive := fun _ => Bool) false
        (strictB (Nat.add o ls) (fun o' => walkOK f b o')) (walkOK f a o) = true := h
    obtain ⟨ha, hb⟩ := (CFSG.KS.bAnd_iff _ _).1 h'
    rw [strictB_eq] at hb
    simp only [OrbitNats.size] at hi
    simp only [OrbitNats.values]
    have hla := OrbitNats.values_length a hva
    rcases Nat.lt_or_ge i a.size with hia | hia
    · rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_left (by omega),
        ← List.getElem!_eq_getElem?_getD]
      exact iha o hva ha i hia
    · rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by omega),
        ← List.getElem!_eq_getElem?_getD, hla]
      have := ihb (Nat.add o ls) hvb hb (i - a.size) (by omega)
      rw [← hs] at this
      have e : Nat.add o a.size + (i - a.size) = o + i := by
        change o + a.size + (i - a.size) = o + i
        omega
      rwa [e] at this

theorem shape_spec {n : Nat} {t : OrbitNats} (h : shapeOK n t = true) :
    t.valid = true ∧ t.size = n ∧ t.values.length = n := by
  unfold shapeOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, h.2, (OrbitNats.values_length t h.1).trans h.2⟩

theorem walk_get {f : Nat → Nat → Bool} {n : Nat} {t : OrbitNats} (hs : shapeOK n t = true)
    (h : walkOK f t (nat_lit 0) = true) : ∀ i < n, f i (t.values[i]!) = true := by
  obtain ⟨hv, hsz, -⟩ := shape_spec hs
  intro i hi
  have := walkOK_spec t 0 hv h i (by omega)
  rwa [Nat.zero_add] at this


theorem toOrbit_keys (P : PackedOrbitData) :
    P.toOrbit.keys = (P.vectors.values.map (orbitVector P.dimension)).toArray := rfl

theorem toOrbit_keys_size (P : PackedOrbitData) :
    P.toOrbit.keys.size = P.vectors.values.length := by
  simp [toOrbit_keys]

theorem toOrbit_keys_get (P : PackedOrbitData) {i : Nat} (hi : i < P.vectors.values.length) :
    P.toOrbit.keys[i]! = orbitVector P.dimension (P.vectors.values[i]!) := by
  rw [toOrbit_keys]
  simp [List.getElem!_eq_getElem?_getD, hi]

theorem toOrbit_alpha_size (P : PackedOrbitData) : P.toOrbit.alpha.size = P.alpha.values.length := by
  simp [PackedOrbitData.toOrbit]

theorem toOrbit_beta_size (P : PackedOrbitData) : P.toOrbit.beta.size = P.beta.values.length := by
  simp [PackedOrbitData.toOrbit]

theorem ap_values (t : OrbitNats) (ht : t.valid = true) (i : Nat) (hv : t.values[i]! < 2 ^ 32) :
    ap (t.values.map UInt32.ofNat).toArray i = t.values[i]! := by
  rw [OrbitNats.table_ap t ht, OrbitNats.get_eq t ht, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt hv

theorem toOrbit_ap_alpha (P : PackedOrbitData) (ht : P.alpha.valid = true) (i : Nat)
    (hv : P.alpha.values[i]! < 2 ^ 32) : ap P.toOrbit.alpha i = P.alpha.values[i]! :=
  ap_values _ ht i hv

theorem toOrbit_ap_beta (P : PackedOrbitData) (ht : P.beta.valid = true) (i : Nat)
    (hv : P.beta.values[i]! < 2 ^ 32) : ap P.toOrbit.beta i = P.beta.values[i]! :=
  ap_values _ ht i hv

theorem toOrbit_ap_par (P : PackedOrbitData) (ht : P.parents.valid = true) (i : Nat)
    (hv : P.parents.values[i]! < 2 ^ 32) : ap P.toOrbit.par i = P.parents.values[i]! :=
  ap_values _ ht i hv

theorem toOrbit_ap_lab (P : PackedOrbitData) (ht : P.labels.valid = true) (i : Nat)
    (hv : P.labels.values[i]! < 2 ^ 32) : ap P.toOrbit.lab i = P.labels.values[i]! :=
  ap_values _ ht i hv

theorem orbitVector_size (d x : Nat) : (orbitVector d x).size = d := by
  simp [orbitVector, ByteArray.size]

theorem orbitVector_get (d x : Nat) {j : Nat} (hj : j < d) :
    ((orbitVector d x).get! j).toNat = x / 2 ^ (3 * j) % 8 := by
  have e : (orbitVector d x).get! j = UInt8.ofNat ((x >>> (3 * j)) % 8) := by
    simp [orbitVector, ByteArray.get!, hj]
  rw [e, UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt (by omega)

theorem canonB_orbitVector {d x : Nat} (h : ∀ j < d, x / 2 ^ (3 * j) % 8 < 5) :
    canonB d (orbitVector d x) = true := by
  unfold canonB
  rw [Bool.and_eq_true, beq_iff_eq, orbitVector_size, CFSG.Sporadic.Th.allIn_eq_true]
  refine ⟨rfl, fun j _ hj => ?_⟩
  rw [decide_eq_true_eq, orbitVector_get d x hj]
  exact h j hj

theorem eq_of_fields {d x y : Nat} (hx : x < 2 ^ (3 * d)) (hy : y < 2 ^ (3 * d))
    (h : ∀ j < d, x / 2 ^ (3 * j) % 8 = y / 2 ^ (3 * j) % 8) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 3 * d
  · have hj : b / 3 < d := by omega
    have e := h (b / 3) hj
    have key : ∀ z : Nat, z.testBit b = (z / 2 ^ (3 * (b / 3)) % 8).testBit (b % 3) := by
      intro z
      rw [show (8 : Nat) = 2 ^ 3 by norm_num, Nat.testBit_mod_two_pow,
        decide_eq_true (Nat.mod_lt b (by norm_num)), Bool.true_and,
        ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
      congr 1
      omega
    rw [key x, key y, e]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem orbitVector_inj {d x y : Nat} (hx : x < 2 ^ (3 * d)) (hy : y < 2 ^ (3 * d))
    (h : orbitVector d x = orbitVector d y) : x = y := by
  refine eq_of_fields hx hy fun j hj => ?_
  rw [← orbitVector_get d x hj, ← orbitVector_get d y hj, h]

theorem xv_lt (T : Nat → Nat) (i : Nat) : xv T i < 2 ^ (3 * 133) := by
  unfold xv
  rw [fldW_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

instance lawfulBEqByteArray : LawfulBEq ByteArray where
  eq_of_beq {a b} h := by
    have h' : (a.data == b.data) = true := h
    exact ByteArray.ext (by simpa using h')
  rfl {a} := by
    change (a.data == a.data) = true
    exact beq_self_eq_true _

theorem fold_index_notMem (l : List (ByteArray × Nat)) (m : Std.HashMap ByteArray Nat)
    {k : ByteArray} (hk : k ∉ l.map Prod.fst) (fb : Nat) :
    (l.foldl (fun m (vi : ByteArray × Nat) => m.insert vi.1 vi.2) m).getD k fb = m.getD k fb := by
  induction l generalizing m with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hk
    rw [List.foldl_cons, ih _ hk.2, Std.HashMap.getD_insert]
    have : (a.1 == k) = false := by
      rw [beq_eq_false_iff_ne]
      exact fun e => hk.1 e.symm
    rw [this]
    rfl

theorem fold_index_mem (l : List (ByteArray × Nat)) (hl : (l.map Prod.fst).Nodup)
    (m : Std.HashMap ByteArray Nat) {k : ByteArray} {v : Nat} (hkv : (k, v) ∈ l) (fb : Nat) :
    (l.foldl (fun m (vi : ByteArray × Nat) => m.insert vi.1 vi.2) m).getD k fb = v := by
  induction l generalizing m with
  | nil => simp at hkv
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons] at hl
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hkv with e | hm
    · subst e
      rw [fold_index_notMem l _ hl.1, Std.HashMap.getD_insert_self]
    · exact ih hl.2 _ hm

theorem index_eq (l : List ByteArray) (hd : l.Nodup) {i : Nat} (hi : i < l.length) (fb c : Nat) :
    (l.toArray.toList.zipIdx.foldl
      (fun (m : Std.HashMap ByteArray Nat) (vi : ByteArray × Nat) => m.insert vi.1 vi.2)
      (Std.HashMap.emptyWithCapacity c)).getD l[i] fb = i := by
  rw [List.toList_toArray]
  refine fold_index_mem _ ?_ _ ?_ fb
  · rw [List.zipIdx_map_fst]
    exact hd
  · rw [List.mem_iff_getElem]
    exact ⟨i, by simp [hi], by simp [List.getElem_zipIdx]⟩

theorem toOrbit_index (P : PackedOrbitData)
    (hd : (P.vectors.values.map (orbitVector P.dimension)).Nodup) {i : Nat}
    (hi : i < P.vectors.values.length) (fb : Nat) :
    P.toOrbit.index.getD P.toOrbit.keys[i]! fb = i := by
  have hi' : i < (P.vectors.values.map (orbitVector P.dimension)).length := by simpa using hi
  have e : P.toOrbit.keys[i]! = (P.vectors.values.map (orbitVector P.dimension))[i] := by
    rw [toOrbit_keys_get P hi]
    simp [List.getElem?_eq_getElem hi]
  rw [e]
  exact index_eq _ hd hi' fb _

end CFSG.KS.SporSch.HNXP

end
