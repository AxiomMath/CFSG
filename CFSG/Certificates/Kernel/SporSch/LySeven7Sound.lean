module

public import Certificates.Data.Kernel.SporSch.LySeven7
public import CFSG.Certificates.Kernel.SporSch.LySevenSound
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.SporSch.LyLoop
import CFSG.Certificates.Kernel.SporSch.LySevBfs

namespace CFSG.KS.SporSch.LySev

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.Ly.Native CFSG.Sporadic.He.Native
open CFSG.KS.SporSch.LyLoop CFSG.KS.SporSch.LyM CFSG.KS.SporSch.LySvB

theorem dec49_get {x t : Nat} (ht : t < 49) : (dec49 x)[t]! = d3 x t := by
  unfold dec49
  rw [ofFn_getP (fun t => d3 x t) ht]

theorem mul7K_place (X Y : Nat) : mul7K X Y = CFSG.KS.SporSch.LyK.placeF
    (fun t => (∑ l ∈ Finset.range 7, d3 X (7 * (t / 7) + l) * d3 Y (7 * l + t % 7)) % 5)
    (fun t => 3 * t) 49 := by
  unfold mul7K CFSG.KS.SporSch.LyK.placeF
  rw [foldN_eqP]
  congr 1
  funext t acc
  rw [foldN_eqP, foldr_sum (fun l => Nat.mul (d3 X (Nat.add (Nat.mul 7 (Nat.div t 7)) l))
    (d3 Y (Nat.add (Nat.mul 7 l) (Nat.mod t 7)))) 7 0, Nat.zero_add]
  rfl

theorem d3_mul7K (X Y : Nat) {t : Nat} (ht : t < 49) :
    d3 (mul7K X Y) t = (∑ l ∈ Finset.range 7, d3 X (7 * (t / 7) + l) * d3 Y (7 * l + t % 7)) % 5 := by
  rw [d3_eq, mul7K_place]
  exact place_fld (w := 3) (by norm_num) (fun r _ => Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num))
    (by norm_num)) ht

theorem congr7K_place (P S : Nat) : congr7K P S = CFSG.KS.SporSch.LyK.placeF
    (fun t => (∑ l ∈ Finset.range 7, d3 (mul7K P S) (7 * (t / 7) + l) * d3 P (7 * (t % 7) + l)) % 5)
    (fun t => 3 * t) 49 := by
  unfold congr7K CFSG.KS.SporSch.LyK.placeF
  rw [strictN_eqP, foldN_eqP]
  congr 1
  funext t acc
  rw [foldN_eqP, foldr_sum (fun l => Nat.mul (d3 (mul7K P S) (Nat.add (Nat.mul 7 (Nat.div t 7)) l))
    (d3 P (Nat.add (Nat.mul 7 (Nat.mod t 7)) l))) 7 0, Nat.zero_add]
  rfl

theorem d3_congr7K (P S : Nat) {t : Nat} (ht : t < 49) :
    d3 (congr7K P S) t =
      (∑ l ∈ Finset.range 7, d3 (mul7K P S) (7 * (t / 7) + l) * d3 P (7 * (t % 7) + l)) % 5 := by
  rw [d3_eq, congr7K_place]
  exact place_fld (w := 3) (by norm_num) (fun r _ => Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num))
    (by norm_num)) ht

theorem d3_id7K {t : Nat} (ht : t < 49) : d3 id7K t = if t / 7 = t % 7 then 1 else 0 := by
  have hp : id7K = CFSG.KS.SporSch.LyK.placeF (fun _ => 1) (fun i => 24 * i) 7 := by
    unfold id7K CFSG.KS.SporSch.LyK.placeF
    rw [foldN_eqP]
    rfl
  have hspec := CFSG.KS.SporSch.LyK.placeF_spec (d := 7) (w := 3) (S := 21) (N := 7) le_rfl
    (pl := fun i => 8 * i) (val := fun _ => 1) (sh := fun i => 24 * i)
    (fun p hp => by omega) (fun p _ q _ h => by omega) (fun p _ => by norm_num)
    (fun p hp => by omega) 7 le_rfl
  have e : ∀ M, entL 7 3 21 M t = M / 2 ^ (3 * t) % 8 := fun M => by
    unfold entL
    rw [show 21 * (t / 7) + 3 * (t % 7) = 3 * t by omega]
    norm_num
  rw [d3_eq, hp, ← e]
  by_cases h : t / 7 = t % 7
  · rw [ite_eq_left h]
    have e2 := hspec.1 (t / 7) (by omega)
    rw [show 8 * (t / 7) = t by omega] at e2
    exact e2
  · rw [ite_eq_right h]
    exact hspec.2 t ht fun p hp e3 => h (by omega)

theorem bsize_set (A : ByteArray) (i : Nat) (v : UInt8) : (A.set! i v).size = A.size := by
  cases A with
  | mk a => exact size_setR a i v

theorem bget_set {A : ByteArray} {i : Nat} (hi : i < A.size) (v : UInt8) (m : Nat) :
    (A.set! i v).get! m = if m = i then v else A.get! m := by
  cases A with
  | mk a =>
    change (a.set! i v)[m]! = if m = i then v else a[m]!
    by_cases hm : m < a.size
    · rw [get_setR a i v hm]
    · have hm' : ¬ m < (a.set! i v).size := by rw [size_setR]; exact hm
      rw [getElem!_neg _ m hm', getElem!_neg a m hm,
        ite_eq_right (fun h => hm (by rw [h]; exact hi))]

theorem bne_toNat (b : UInt8) : (b != 0) = (b.toNat != 0) := by
  have e : (b == 0) = (b.toNat == 0) := by
    by_cases h : b = 0
    · subst h
      rfl
    · have h' : b.toNat ≠ 0 := fun e => h (UInt8.toNat_inj.1 (e.trans (rfl : (0 : Nat) = (0 : UInt8).toNat)))
      rw [beq_false_of_ne h, beq_false_of_ne h']
  simp only [bne, e]

theorem u8_scale {x y : UInt8} (hx : x.toNat < 5) (hy : y.toNat < 5) :
    (x * y % 5).toNat = x.toNat * y.toNat % 5 := by
  have hp : x.toNat * y.toNat < 256 := by nlinarith
  rw [UInt8.toNat_mod, UInt8.toNat_mul, Nat.mod_eq_of_lt hp]
  rfl

theorem u8_elim {x f y : UInt8} (hx : x.toNat < 5) (hf : f.toNat < 5) (hy : y.toNat < 5) :
    ((x + (5 - f) * y) % 5).toNat = (x.toNat + (5 - f.toNat) * y.toNat) % 5 := by
  have h5 : (5 : UInt8).toNat = 5 := rfl
  have hle : f ≤ 5 := by
    rw [UInt8.le_iff_toNat_le, h5]
    omega
  have hp : (5 - f.toNat) * y.toNat ≤ 25 := by
    have : 5 - f.toNat ≤ 5 := by omega
    nlinarith
  rw [UInt8.toNat_mod, UInt8.toNat_add, UInt8.toNat_mul, UInt8.toNat_sub_of_le _ _ hle, h5,
    Nat.mod_eq_of_lt (by omega : (5 - f.toNat) * y.toNat < 2 ^ 8),
    Nat.mod_eq_of_lt (by omega : x.toNat + (5 - f.toNat) * y.toNat < 2 ^ 8)]

theorem rowLoop {A : ByteArray} {b e : Nat} (F : Nat → UInt8 → UInt8 → UInt8)
    (f : ByteArray → Nat → ByteArray)
    (hf : ∀ B j, f B j = B.set! (b + j) (F j (B.get! (b + j)) (B.get! (e + j))))
    (hb : b + 14 ≤ A.size) (he : ∀ j < 14, ∀ j' < j, e + j ≠ b + j') :
    ∀ n ≤ 14, ((List.range n).foldl f A).size = A.size ∧ ∀ m, ((List.range n).foldl f A).get! m =
      if b ≤ m ∧ m < b + n then F (m - b) (A.get! m) (A.get! (e + (m - b))) else A.get! m := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hf]
    generalize (List.range n).foldl f A = B at h1 h2 ⊢
    refine ⟨by rw [bsize_set, h1], fun m => ?_⟩
    have g1 : B.get! (b + n) = A.get! (b + n) := by rw [h2, ite_eq_right (by omega)]
    have g2 : B.get! (e + n) = A.get! (e + n) := by
      rw [h2, ite_eq_right (fun h => he n (by omega) (e + n - b) (by omega) (by omega))]
    rw [bget_set (by rw [h1]; omega), g1, g2]
    by_cases hm : m = b + n
    · subst hm
      rw [ite_eq_left rfl, ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
    · rw [ite_eq_right hm, h2 m]
      have e' : (b ≤ m ∧ m < b + n) ↔ (b ≤ m ∧ m < b + (n + 1)) := by omega
      simp only [e']

theorem swapLoop {A : ByteArray} {p q : Nat} (f : ByteArray → Nat → ByteArray)
    (hf : ∀ B j, f B j = (B.set! (p + j) (B.get! (q + j))).set! (q + j) (B.get! (p + j)))
    (hp : p + 14 ≤ A.size) (hq : q + 14 ≤ A.size) (hpq : p + 14 ≤ q ∨ q + 14 ≤ p) :
    ∀ n ≤ 14, ((List.range n).foldl f A).size = A.size ∧ ∀ m, ((List.range n).foldl f A).get! m =
      if q ≤ m ∧ m < q + n then A.get! (p + (m - q))
      else if p ≤ m ∧ m < p + n then A.get! (q + (m - p)) else A.get! m := by
  intro n
  induction n with
  | zero =>
    intro _
    simp only [List.range_zero, List.foldl_nil]
    refine ⟨trivial, fun m => ?_⟩
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  | succ n ih =>
    intro hn
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hf]
    generalize (List.range n).foldl f A = B at h1 h2 ⊢
    refine ⟨by rw [bsize_set, bsize_set, h1], fun m => ?_⟩
    have g1 : B.get! (p + n) = A.get! (p + n) := by
      rw [h2, ite_eq_right (by omega), ite_eq_right (by omega)]
    have g2 : B.get! (q + n) = A.get! (q + n) := by
      rw [h2, ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [bget_set (by rw [bsize_set, h1]; omega), bget_set (by rw [h1]; omega), g1, g2, h2 m]
    by_cases hm1 : m = q + n
    · subst hm1
      rw [ite_eq_left rfl, ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
    · rw [ite_eq_right hm1]
      by_cases hm2 : m = p + n
      · subst hm2
        rw [ite_eq_left rfl, ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩,
          Nat.add_sub_cancel_left]
      · rw [ite_eq_right hm2]
        have e1 : (q ≤ m ∧ m < q + n) ↔ (q ≤ m ∧ m < q + (n + 1)) := by omega
        have e2 : (p ≤ m ∧ m < p + n) ↔ (p ≤ m ∧ m < p + (n + 1)) := by omega
        simp only [e1, e2]

def pivB (c : Nat) (A : ByteArray) (piv r : Nat) : Nat :=
  if (piv == 7 && A.get! (14 * r + c) != 0) = true then r else piv

def pivBF (c : Nat) (A : ByteArray) : Nat := (List.range' c (7 - c)).foldl (pivB c A) 7

def swapB (A : ByteArray) (piv c : Nat) : ByteArray :=
  (List.range 14).foldl (fun B j => (B.set! (14 * piv + j) (B.get! (14 * c + j))).set!
    (14 * c + j) (B.get! (14 * piv + j))) A

def scaleB (c : Nat) (A : ByteArray) : ByteArray :=
  (List.range 14).foldl (fun B j => B.set! (14 * c + j)
    (B.get! (14 * c + j) * UInt8.ofNat (inv5 (A.get! (14 * c + c)).toNat) % 5)) A

def elimB (c : Nat) (A : ByteArray) (r : Nat) : ByteArray :=
  if (r != c) = true then
    if (A.get! (14 * r + c) != 0) = true then
      (List.range 14).foldl (fun B j => B.set! (14 * r + j)
        ((B.get! (14 * r + j) + (5 - A.get! (14 * r + c)) * B.get! (14 * c + j)) % 5)) A
    else A
  else A

def stepB (A : ByteArray) (c : Nat) : ByteArray :=
  if pivBF c A < 7 then
    if (pivBF c A != c) = true then (List.range 7).foldl (elimB c) (scaleB c (swapB A (pivBF c A) c))
    else (List.range 7).foldl (elimB c) (scaleB c A)
  else A

def initB (X : Array Nat) : ByteArray :=
  ⟨Array.ofFn (n := 98) fun t => UInt8.ofNat (if t.val % 14 < 7 then
    X[7 * (t.val / 14) + t.val % 14]! % 5 else if t.val % 14 - 7 = t.val / 14 then 1 else 0)⟩

def inv7F (X : Array Nat) : Array Nat :=
  Array.ofFn (n := 49) fun t =>
    (((List.range 7).foldl stepB (initB X)).get! (14 * (t.val / 7) + 7 + t.val % 7)).toNat

theorem inv7_eq_F (X : Array Nat) : inv7 X = inv7F X := by
  unfold inv7
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', ite_pure_yieldL,
    List.forIn_pure_yield_eq_foldl, pure_bind]
  have h1 : ∀ a b : Nat, [a:b].size = b - a := fun a b => by simp [Std.Legacy.Range.size]
  simp only [h1, Nat.sub_zero, ← List.range_eq_range']
  rfl

def absB (A : ByteArray) : Array (Array Nat) :=
  Array.ofFn (n := 7) fun i => Array.ofFn (n := 14) fun j => (A.get! (14 * i.val + j.val)).toNat

def BB (A : ByteArray) : Prop := A.size = 98 ∧ ∀ m < 98, (A.get! m).toNat < 5

theorem absB_ent (A : ByteArray) {i j : Nat} (hi : i < 7) (hj : j < 14) :
    ((absB A)[i]!)[j]! = (A.get! (14 * i + j)).toNat := by
  unfold absB
  rw [ofFn_get! _ hi, ofFn_get! _ hj]

theorem absB_size (A : ByteArray) : (absB A).size = 7 := by simp [absB]

theorem absB_row (A : ByteArray) {i : Nat} (hi : i < 7) : ((absB A)[i]!).size = 14 := by
  unfold absB
  rw [ofFn_get! _ hi]
  simp

theorem absB_ext {A : ByteArray} {M : Array (Array Nat)} (hM : M.size = 7)
    (hr : ∀ i < 7, (M[i]!).size = 14)
    (he : ∀ i < 7, ∀ j < 14, (M[i]!)[j]! = (A.get! (14 * i + j)).toNat) : absB A = M := by
  apply Array.ext
  · rw [absB_size, hM]
  · intro i h1 h2
    have hi : i < 7 := by rwa [absB_size] at h1
    have hiM : i < M.size := by rw [hM]; exact hi
    have hrow := hr i hi
    rw [getElem!_pos M i hiM] at hrow
    apply Array.ext
    · have := absB_row A hi
      rw [getElem!_pos _ i h1] at this
      rw [this, hrow]
    · intro j k1 k2
      have hj : j < 14 := by rwa [hrow] at k2
      have e1 := absB_ent A hi hj
      have e2 := he i hi j hj
      rw [getElem!_pos _ i h1, getElem!_pos _ j k1] at e1
      rw [getElem!_pos M i hiM, getElem!_pos _ j k2] at e2
      rw [e1, e2]

theorem fold_sim {α : Type} (f : ByteArray → α → ByteArray)
    (g : Array (Array Nat) → α → Array (Array Nat)) (l : List α)
    (h : ∀ A, ∀ x ∈ l, BB A → BB (f A x) ∧ absB (f A x) = g (absB A) x) :
    ∀ A, BB A → BB (l.foldl f A) ∧ absB (l.foldl f A) = l.foldl g (absB A) := by
  induction l with
  | nil => intro A hA; exact ⟨hA, rfl⟩
  | cons x l ih =>
    intro A hA
    obtain ⟨h1, h2⟩ := h A x (by simp) hA
    rw [List.foldl_cons, List.foldl_cons, ← h2]
    exact ih (fun A y hy hA => h A y (List.mem_cons_of_mem x hy) hA) _ h1

theorem pivB_eq {c : Nat} {A : ByteArray} (hc : c < 7) (hA : BB A) :
    pivBF c A = pivF 5 7 c (absB A) := by
  unfold pivBF pivF
  refine List.foldl_ext _ _ _ fun piv r hr => ?_
  rw [List.mem_range'_1] at hr
  unfold pivB pivS
  rw [absB_ent A (by omega) (by omega), Nat.mod_eq_of_lt (hA.2 _ (by omega)), bne_toNat]

theorem swap_sim {c P : Nat} {A : ByteArray} (hc : c < 7) (hP : P < 7) (hA : BB A) :
    BB (if (P != c) = true then swapB A P c else A) ∧
      absB (if (P != c) = true then swapB A P c else A) = swapR (absB A) P c := by
  have key : ∀ m < 98, (if (P != c) = true then swapB A P c else A).get! m =
      A.get! (14 * (if m / 14 = c then P else if m / 14 = P then c else m / 14) + m % 14) ∧
      (if (P != c) = true then swapB A P c else A).size = 98 := by
    intro m hm
    by_cases hPc : P = c
    · subst hPc
      simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
      refine ⟨?_, hA.1⟩
      congr 1
      split_ifs <;> omega
    · have hb : (P != c) = true := by simpa using hPc
      rw [ite_eq_left hb]
      obtain ⟨s1, s2⟩ := swapLoop (A := A) (p := 14 * P) (q := 14 * c) _ (fun _ _ => rfl)
        (by rw [hA.1]; omega) (by rw [hA.1]; omega) (by omega) 14 le_rfl
      refine ⟨?_, by rw [swapB, s1, hA.1]⟩
      unfold swapB
      rw [s2 m]
      have hm14 : m = 14 * (m / 14) + m % 14 := (Nat.div_add_mod m 14).symm
      split_ifs <;> first | omega | exact congrArg (ByteArray.get! A) (by omega)
  have hB : BB (if (P != c) = true then swapB A P c else A) := by
    refine ⟨(key 0 (by norm_num)).2, fun m hm => ?_⟩
    rw [(key m hm).1]
    exact hA.2 _ (by split_ifs <;> omega)
  refine ⟨hB, absB_ext (by unfold swapR; rw [size_setR, size_setR, absB_size]) (fun i hi => ?_)
    (fun i hi j hj => ?_)⟩
  · rw [swap_get (absB_size A) hi]
    split_ifs <;> exact absB_row A (by omega)
  · rw [swap_get (absB_size A) hi, (key _ (by omega)).1]
    have e1 : (14 * i + j) / 14 = i := by omega
    have e2 : (14 * i + j) % 14 = j := by omega
    rw [e1, e2]
    split_ifs <;> rw [absB_ent A (by omega) hj]

theorem scale_sim {c : Nat} {A : ByteArray} (hc : c < 7) (hA : BB A) :
    BB (scaleB c A) ∧ absB (scaleB c A) = scaleR 5 c (absB A) := by
  set iv := UInt8.ofNat (inv5 (A.get! (14 * c + c)).toNat) with hiv
  have hivN : iv.toNat = (A.get! (14 * c + c)).toNat ^ (5 - 2) % 5 := by
    rw [hiv, UInt8.toNat_ofNat', inv5]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))
  have hiv5 : iv.toNat < 5 := by rw [hivN]; exact Nat.mod_lt _ (by norm_num)
  obtain ⟨s1, s2⟩ := rowLoop (A := A) (b := 14 * c) (e := 14 * c) (fun _ x _ => x * iv % 5) _
    (fun _ _ => rfl) (by rw [hA.1]; omega) (fun j _ j' hj' => by omega) 14 le_rfl
  have hval : ∀ m < 98, (scaleB c A).get! m =
      if 14 * c ≤ m ∧ m < 14 * c + 14 then A.get! m * iv % 5 else A.get! m := fun m _ => s2 m
  have hB : BB (scaleB c A) := by
    refine ⟨by unfold scaleB; rw [s1, hA.1], fun m hm => ?_⟩
    rw [hval m hm]
    split_ifs
    · rw [u8_scale (hA.2 m hm) hiv5]
      exact Nat.mod_lt _ (by norm_num)
    · exact hA.2 m hm
  refine ⟨hB, absB_ext (by unfold scaleR; rw [size_setR, absB_size]) (fun i hi => ?_)
    (fun i hi j hj => ?_)⟩
  · rw [scale_get (absB_size A) hi]
    split_ifs with h
    · rw [Array.size_map, absB_row A hc]
    · exact absB_row A hi
  · rw [scale_get (absB_size A) hi, hval _ (by omega)]
    by_cases h : i = c
    · subst h
      rw [ite_eq_left rfl, ite_eq_left ⟨by omega, by omega⟩, get_mapR _ _ (by rw [absB_row A hi]; exact hj),
        absB_ent A hi hj, absB_ent A hi (by omega), u8_scale (hA.2 _ (by omega)) hiv5, hivN]
    · rw [ite_eq_right h, ite_eq_right (by omega), absB_ent A hi hj]

theorem elim_sim {c r : Nat} {A : ByteArray} (hc : c < 7) (hr : r < 7) (hA : BB A) :
    BB (elimB c A r) ∧ absB (elimB c A r) = elimS 5 7 c (absB A) r := by
  unfold elimB elimS
  rw [absB_ent A hr (by omega), bne_toNat]
  by_cases h1 : (r != c) = true
  · rw [ite_eq_left h1, ite_eq_left h1]
    by_cases h2 : ((A.get! (14 * r + c)).toNat != 0) = true
    · rw [ite_eq_left h2, ite_eq_left h2]
      have hrc : r ≠ c := by simpa using h1
      set f := A.get! (14 * r + c) with hfd
      have hf5 : f.toNat < 5 := hA.2 _ (by omega)
      obtain ⟨s1, s2⟩ := rowLoop (A := A) (b := 14 * r) (e := 14 * c)
        (fun _ x y => (x + (5 - f) * y) % 5) _ (fun _ _ => rfl) (by rw [hA.1]; omega)
        (fun j hj j' hj' => by omega) 14 le_rfl
      generalize hE : (List.range 14).foldl _ A = E at s1 s2
      have hB : BB E := by
        refine ⟨by rw [s1, hA.1], fun m hm => ?_⟩
        rw [s2 m]
        split_ifs
        · rw [u8_elim (hA.2 m hm) hf5 (hA.2 _ (by omega))]
          exact Nat.mod_lt _ (by norm_num)
        · exact hA.2 m hm
      refine ⟨hB, absB_ext (by rw [size_setR, absB_size]) (fun i hi => ?_) (fun i hi j hj => ?_)⟩
      · rw [get_setR _ _ _ (by rw [absB_size]; exact hi)]
        split_ifs
        · simp [newRow]
        · exact absB_row A hi
      · rw [get_setR _ _ _ (by rw [absB_size]; exact hi), s2]
        by_cases hir : i = r
        · subst hir
          rw [ite_eq_left rfl, ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
          unfold newRow
          rw [ofFn_get! _ (by omega), absB_ent A hi hj, absB_ent A hi (by omega), absB_ent A hc hj,
            u8_elim (hA.2 _ (by omega)) hf5 (hA.2 _ (by omega))]
        · rw [ite_eq_right hir, ite_eq_right (by omega), absB_ent A hi hj]
    · rw [ite_eq_right h2, ite_eq_right h2]
      exact ⟨hA, rfl⟩
  · rw [ite_eq_right h1, ite_eq_right h1]
    exact ⟨hA, rfl⟩

theorem step_sim {c : Nat} {A : ByteArray} (hc : c < 7) (hA : BB A) :
    BB (stepB A c) ∧ absB (stepB A c) = stepS 5 7 (absB A) c := by
  unfold stepB stepS
  rw [pivB_eq hc hA]
  by_cases hlt : pivF 5 7 c (absB A) < 7
  · rw [ite_eq_left hlt, ite_eq_left hlt]
    have hif : ∀ (q : Bool) (W : ByteArray), (if q = true then (List.range 7).foldl (elimB c)
        (scaleB c W) else (List.range 7).foldl (elimB c) (scaleB c A)) =
        (List.range 7).foldl (elimB c) (scaleB c (if q = true then W else A)) := by
      intro q W
      split <;> rfl
    rw [hif]
    obtain ⟨w1, w2⟩ := swap_sim hc hlt hA
    obtain ⟨c1, c2⟩ := scale_sim hc w1
    rw [w2] at c2
    obtain ⟨e1, e2⟩ := fold_sim (elimB c) (elimS 5 7 c) (List.range 7)
      (fun A r hr hA => elim_sim hc (List.mem_range.1 hr) hA) _ c1
    rw [c2] at e2
    exact ⟨e1, e2⟩
  · rw [ite_eq_right hlt, ite_eq_right hlt]
    exact ⟨hA, rfl⟩

def rows7 (X : Array Nat) : Array (Array Nat) :=
  Array.ofFn (n := 7) fun i => Array.ofFn (n := 7) fun j => X[7 * i.val + j.val]!

theorem initB_get (X : Array Nat) {m : Nat} (hm : m < 98) : (initB X).get! m =
    UInt8.ofNat (if m % 14 < 7 then X[7 * (m / 14) + m % 14]! % 5
      else if m % 14 - 7 = m / 14 then 1 else 0) := by
  unfold initB
  change (Array.ofFn _)[m]! = _
  rw [ofFn_get! _ hm]

theorem init_sim (X : Array Nat) : BB (initB X) ∧ absB (initB X) = initG 5 7 (rows7 X) := by
  have hv : ∀ m < 98, ((initB X).get! m).toNat = if m % 14 < 7 then X[7 * (m / 14) + m % 14]! % 5
      else if m % 14 - 7 = m / 14 then 1 else 0 := by
    intro m hm
    rw [initB_get X hm, UInt8.toNat_ofNat']
    refine Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le ?_ (by norm_num : 5 ≤ 2 ^ 8))
    split_ifs
    · exact Nat.mod_lt _ (by norm_num)
    · norm_num
    · norm_num
  refine ⟨⟨by simp [initB, ByteArray.size], fun m hm => ?_⟩, absB_ext (by simp [initG])
    (fun i hi => ?_) (fun i hi j hj => ?_)⟩
  · rw [hv m hm]
    split_ifs
    · exact Nat.mod_lt _ (by norm_num)
    · norm_num
    · norm_num
  · unfold initG
    rw [ofFn_get! _ hi]
    simp
  · unfold initG
    rw [ofFn_get! _ hi, ofFn_get! _ hj, hv _ (by omega)]
    have e1 : (14 * i + j) / 14 = i := by omega
    have e2 : (14 * i + j) % 14 = j := by omega
    rw [e1, e2]
    by_cases hj7 : j < 7
    · rw [ite_eq_left hj7, ite_eq_left hj7]
      unfold rows7
      rw [ofFn_get! _ hi, ofFn_get! _ hj7]
    · rw [ite_eq_right hj7, ite_eq_right hj7]

end CFSG.KS.SporSch.LySev

public section

namespace CFSG.KS.SporSch.LySev

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.Ly.Native CFSG.Sporadic.He.Native
open CFSG.KS.SporSch.LyLoop CFSG.KS.SporSch.LyM CFSG.KS.SporSch.LySvB

theorem mul7_eq (X Y : Nat) : mul7 (dec49 X) (dec49 Y) = dec49 (mul7K X Y) := by
  unfold mul7
  conv_rhs => unfold dec49
  refine congrArg Array.ofFn (funext fun t => ?_)
  dsimp only
  rw [d3_mul7K X Y t.isLt, fold_sum]
  refine congrArg (· % 5) (Finset.sum_congr rfl fun l hl => ?_)
  have hl' := Finset.mem_range.1 hl
  have ht := t.isLt
  rw [dec49_get (by omega), dec49_get (by omega)]

theorem congr7_eq (P S : Nat) : congr7 (dec49 P) (dec49 S) = dec49 (congr7K P S) := by
  unfold congr7
  rw [mul7_eq]
  conv_rhs => unfold dec49
  refine congrArg Array.ofFn (funext fun t => ?_)
  dsimp only
  rw [d3_congr7K P S t.isLt, fold_sum]
  refine congrArg (· % 5) (Finset.sum_congr rfl fun l hl => ?_)
  have hl' := Finset.mem_range.1 hl
  have ht := t.isLt
  rw [dec49_get (by omega), dec49_get (by omega)]

theorem inv7_eq {X Y : Nat} (_hX : red49 X = true) (hY : red49 Y = true) (h : mul7K X Y = id7K) :
    inv7 (dec49 X) = dec49 Y := by
  have hy : ∀ i < 7, ∀ j < 7, d3 Y (7 * i + j) < 5 := by
    intro i hi j hj
    have h1 : allN 49 (fun t => Nat.blt (d3 Y t) 5) = true := ((bAnd_iff _ _).1 hY).1
    exact Nat.le_of_ble_eq_true (allN_spec h1 (7 * i + j) (by omega))
  have hXY : ∀ i < 7, ∀ j < 7, ∑ k ∈ Finset.range 7,
      ((((rows7 (dec49 X))[i]!)[k]! : Nat) : ZMod 5) * ((d3 Y (7 * k + j) : Nat) : ZMod 5) =
        if i = j then 1 else 0 := by
    intro i hi j hj
    have e : d3 (mul7K X Y) (7 * i + j) = d3 id7K (7 * i + j) := by rw [h]
    rw [d3_mul7K X Y (t := 7 * i + j) (by omega), d3_id7K (t := 7 * i + j) (by omega)] at e
    have q1 : (7 * i + j) / 7 = i := by omega
    have q2 : (7 * i + j) % 7 = j := by omega
    rw [q1, q2] at e
    have e' := congrArg (fun n : Nat => (n : ZMod 5)) e
    simp only [ZMod.natCast_mod, Nat.cast_sum, Nat.cast_mul, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero] at e'
    rw [← e']
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    unfold rows7
    rw [ofFn_get! _ hi, ofFn_get! _ hk', dec49_get (by omega)]
  have hspec := invM_spec (p := 5) (d := 7) (by norm_num) (y := fun i j => d3 Y (7 * i + j)) hy hXY
  rw [invM_eq_invF] at hspec
  unfold invF at hspec
  obtain ⟨b0, a0⟩ := init_sim (dec49 X)
  obtain ⟨bF, aF⟩ := fold_sim stepB (stepS 5 7) (List.range 7)
    (fun A c hc hA => step_sim (List.mem_range.1 hc) hA) _ b0
  rw [a0] at aF
  rw [← aF] at hspec
  rw [inv7_eq_F]
  unfold inv7F
  conv_rhs => unfold dec49
  refine congrArg Array.ofFn (funext fun t => ?_)
  have ht := t.isLt
  generalize (List.range 7).foldl stepB (initB (dec49 X)) = A at bF hspec ⊢
  have e : (((absB A).map
      fun row => row.extract 7 14)[t.val / 7]!)[t.val % 7]! =
      ((Array.ofFn (n := 7) fun i => Array.ofFn (n := 7) fun j =>
        d3 Y (7 * i.val + j.val))[t.val / 7]!)[t.val % 7]! := by rw [← hspec]
  rw [ofFn_get! _ (by omega), ofFn_get! _ (by omega), get_mapR _ _ (by rw [absB_size]; omega)] at e
  have hrow := absB_row A (i := t.val / 7) (by omega)
  have e2 : ∀ R : Array Nat, R.size = 14 → (R.extract 7 14)[t.val % 7]! = R[7 + t.val % 7]! := by
    intro R hR
    have hlt : t.val % 7 < (R.extract 7 14).size := by
      rw [Array.size_extract, hR]
      omega
    rw [getElem!_pos (R.extract 7 14) (t.val % 7) hlt, Array.getElem_extract,
      getElem!_pos R (7 + t.val % 7) (by rw [hR]; omega)]
  rw [e2 _ hrow, absB_ent A (by omega) (by omega)] at e
  rw [show 14 * (t.val / 7) + 7 + t.val % 7 = 14 * (t.val / 7) + (7 + t.val % 7) by omega, e]
  dsimp only
  exact congrArg (d3 Y) (by omega)

end CFSG.KS.SporSch.LySev

end
