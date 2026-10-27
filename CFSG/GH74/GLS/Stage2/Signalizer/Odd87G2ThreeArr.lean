module

public import Certificates.Data.G2ThreeMaxCheck

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.G2ThreeCert

open Certificates.G2ThreeMax

abbrev Mat3 : Type := Matrix (Fin 14) (Fin 14) (ZMod 3)

@[expose] def M (a : Array ℕ) : Mat3 := Matrix.of fun r c => ((a[14 * r.val + c.val]! : ℕ) : ZMod 3)

theorem ofFn_get (f : Fin 196 → ℕ) {p : ℕ} (hp : p < 196) : (Array.ofFn f)[p]! = f ⟨p, hp⟩ := by
  rw [getElem!_pos _ p (by simpa using hp)]
  exact Array.getElem_ofFn _

theorem idx_lt (r c : Fin 14) : 14 * r.val + c.val < 196 := by
  have := r.2; have := c.2; omega

theorem list_sum_range (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ l ∈ Finset.range n, f l := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem M_idArr : M idArr = 1 := by
  ext r c
  simp only [M, idArr, Matrix.of_apply, Matrix.one_apply]
  rw [ofFn_get _ (idx_lt r c)]
  have h1 : (14 * r.val + c.val) / 14 = r.val := by have := c.2; omega
  have h2 : (14 * r.val + c.val) % 14 = c.val := by have := c.2; omega
  simp only [h1, h2, Fin.val_inj]
  split_ifs <;> simp_all

theorem M_mmul (a b : Array ℕ) : M (mmul a b) = M a * M b := by
  ext r c
  simp only [M, mmul, Matrix.of_apply, Matrix.mul_apply]
  rw [ofFn_get _ (idx_lt r c)]
  have h1 : (14 * r.val + c.val) / 14 = r.val := by have := c.2; omega
  have h2 : (14 * r.val + c.val) % 14 = c.val := by have := c.2; omega
  simp only [h1, h2]
  rw [ZMod.natCast_mod, Nat.cast_sum, Finset.sum_range]
  simp [Nat.cast_mul]

theorem sum_filterMap_nz (L : List ℕ) (a f : ℕ → ℕ) :
    ((L.filterMap fun l => if a l = 0 then none else some (l, a l)).map
      fun t => t.2 * f t.1).sum = (L.map fun l => a l * f l).sum := by
  induction L with
  | nil => simp
  | cons l L ih =>
    by_cases h : a l = 0
    · simp [h, ih]
    · simp [h, ih]

theorem rowNZ_sum (A : Array ℕ) (r : ℕ) (f : ℕ → ℕ) :
    ((rowNZ A r).map fun t => t.2 * f t.1).sum = ∑ l ∈ Finset.range 14, A[14 * r + l]! * f l := by
  unfold rowNZ
  rw [sum_filterMap_nz (List.range 14) (fun l => A[14 * r + l]!) f, list_sum_range]

theorem colNZ_sum (A : Array ℕ) (c : ℕ) (f : ℕ → ℕ) :
    ((colNZ A c).map fun t => t.2 * f t.1).sum = ∑ l ∈ Finset.range 14, A[14 * l + c]! * f l := by
  unfold colNZ
  rw [sum_filterMap_nz (List.range 14) (fun l => A[14 * l + c]!) f, list_sum_range]

theorem rowsOf_get (A : Array ℕ) {r : ℕ} (hr : r < 14) : (rowsOf A)[r]! = rowNZ A r := by
  unfold rowsOf
  rw [getElem!_pos _ r (by simpa using hr)]
  simp

theorem colsOf_get (A : Array ℕ) {r : ℕ} (hr : r < 14) : (colsOf A)[r]! = colNZ A r := by
  unfold colsOf
  rw [getElem!_pos _ r (by simpa using hr)]
  simp

theorem sparse2 (A B : Array ℕ) (r c : ℕ) (g : ℕ → ℕ → ℕ) :
    ((rowNZ A r).map fun t => ((colNZ B c).map fun u => t.2 * g t.1 u.1 * u.2).sum).sum =
      ∑ l ∈ Finset.range 14, A[14 * r + l]! * ∑ m ∈ Finset.range 14, g l m * B[14 * m + c]! := by
  have e : ∀ t : ℕ × ℕ, ((colNZ B c).map fun u => t.2 * g t.1 u.1 * u.2).sum =
      t.2 * ∑ m ∈ Finset.range 14, g t.1 m * B[14 * m + c]! := by
    intro t
    have h := colNZ_sum B c (fun m => g t.1 m)
    calc ((colNZ B c).map fun u => t.2 * g t.1 u.1 * u.2).sum
        = t.2 * ((colNZ B c).map fun u => u.2 * g t.1 u.1).sum := by
          rw [← List.sum_map_mul_left]
          congr 1
          refine List.map_congr_left fun u _ => ?_
          ring
      _ = t.2 * ∑ l ∈ Finset.range 14, B[14 * l + c]! * g t.1 l := congrArg (fun x => t.2 * x) h
      _ = t.2 * ∑ m ∈ Finset.range 14, g t.1 m * B[14 * m + c]! :=
          congrArg (fun x => t.2 * x) (Finset.sum_congr rfl fun m _ => mul_comm _ _)
  simp only [e]
  exact rowNZ_sum A r (fun l => ∑ m ∈ Finset.range 14, g l m * B[14 * m + c]!)

theorem M_conjSparse (A B P : Array ℕ) :
    M (conjSparse (rowsOf A) (colsOf B) P) = M A * M P * M B := by
  ext r c
  simp only [M, conjSparse, Matrix.of_apply, Matrix.mul_apply]
  rw [ofFn_get _ (idx_lt r c)]
  have h1 : (14 * r.val + c.val) / 14 = r.val := by have := c.2; omega
  have h2 : (14 * r.val + c.val) % 14 = c.val := by have := c.2; omega
  simp only [h1, h2]
  rw [rowsOf_get A r.2, colsOf_get B c.2, ZMod.natCast_mod,
    sparse2 A B r.val c.val (fun l m => P[14 * l + m]!)]
  push_cast
  rw [Finset.sum_range]
  simp only [Finset.sum_range, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem size_ofFn' (f : Fin 196 → ℕ) : (Array.ofFn f).size = 196 := by simp

theorem size_mmul (a b : Array ℕ) : (mmul a b).size = 196 := size_ofFn' _
theorem size_conjSparse (rows cols : Array (List (ℕ × ℕ))) (P : Array ℕ) :
    (conjSparse rows cols P).size = 196 := size_ofFn' _
theorem lt_mmul (a b : Array ℕ) {p : ℕ} (hp : p < 196) : (mmul a b)[p]! < 3 := by
  unfold mmul; rw [ofFn_get _ hp]; exact Nat.mod_lt _ (by norm_num)
theorem lt_conjSparse (rows cols : Array (List (ℕ × ℕ))) (P : Array ℕ) {p : ℕ} (hp : p < 196) :
    (conjSparse rows cols P)[p]! < 3 := by
  unfold conjSparse; rw [ofFn_get _ hp]; exact Nat.mod_lt _ (by norm_num)

theorem decodeAux_encodeL (l : List ℕ) (h : ∀ d ∈ l, d < 3) : decodeAux l.length (encodeL l) = l := by
  induction l with
  | nil => simp [decodeAux]
  | cons d l ih =>
    have hd : d < 3 := h d (by simp)
    have hl : ∀ x ∈ l, x < 3 := fun x hx => h x (by simp [hx])
    simp only [List.length_cons, decodeAux, encodeL]
    have e1 : (d + 3 * encodeL l) % 3 = d := by omega
    have e2 : (d + 3 * encodeL l) / 3 = encodeL l := by omega
    rw [e1, e2, ih hl]

theorem decode_encode (a : Array ℕ) (hs : a.size = 196) (hd : ∀ p < 196, a[p]! < 3) :
    decode (encode a) = a := by
  have hl : a.toList.length = 196 := by simpa using hs
  have hdig : ∀ d ∈ a.toList, d < 3 := by
    intro d hd'
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hd'
    have hi' : i < 196 := by simpa [hs] using hi
    have := hd i hi'
    rw [getElem!_pos a i (by omega)] at this
    simpa using this
  unfold decode encode
  have := decodeAux_encodeL a.toList hdig
  rw [hl] at this
  rw [this]

theorem M_inj (a b : Array ℕ) (ha : a.size = 196) (hb : b.size = 196)
    (hda : ∀ p < 196, a[p]! < 3) (hdb : ∀ p < 196, b[p]! < 3) (h : M a = M b) : a = b := by
  apply Array.ext (by rw [ha, hb])
  intro p hpa hpb
  have hp : p < 196 := by simpa [ha] using hpa
  have hr : p / 14 < 14 := by omega
  have hc : p % 14 < 14 := by omega
  have h1 := congrFun (congrFun h ⟨p / 14, hr⟩) ⟨p % 14, hc⟩
  simp only [M, Matrix.of_apply] at h1
  have h2 : 14 * (p / 14) + p % 14 = p := by omega
  simp only [h2] at h1
  have h3 : a[p]! = b[p]! := by
    have := (ZMod.natCast_eq_natCast_iff' _ _ 3).1 h1
    rw [Nat.mod_eq_of_lt (hda p hp), Nat.mod_eq_of_lt (hdb p hp)] at this
    exact this
  rwa [getElem!_pos a p hpa, getElem!_pos b p hpb] at h3

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.G2ThreeCert
