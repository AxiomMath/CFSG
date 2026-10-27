module

public import Certificates.Data.Kernel.SmithEKF
public import CFSG.Certificates.Kernel.SmithEK.TvSound

public section

namespace CFSG.SmithE.K

open CFSG.F4.Native CFSG.SmithE

theorem packD_cons (d : Nat) (ds : List Nat) : packD (d :: ds) = d + 4 * packD ds := rfl

theorem packD_div (l : List Nat) (hl : ∀ d ∈ l, d < 4) (u : Nat) (hu : u < l.length) :
    packD l / 4 ^ u % 4 = l[u] := by
  induction l generalizing u with
  | nil => simp at hu
  | cons d ds ih =>
    have hd : d < 4 := hl d (by simp)
    rw [packD_cons]
    cases u with
    | zero =>
      simp only [pow_zero, Nat.div_one, List.getElem_cons_zero]
      omega
    | succ u =>
      simp only [List.getElem_cons_succ]
      have e : (d + 4 * packD ds) / 4 = packD ds := by omega
      rw [pow_succ', ← Nat.div_div_eq_div_mul, e]
      exact ih (fun d h => hl d (by simp [h])) u (by simpa using hu)

theorem dig_eq (Q u : Nat) : dig Q u = Q / 4 ^ u % 4 := by
  unfold dig
  rw [Nat.shiftRight_eq_div_pow, pow_mul]
  rfl

theorem dig_packD (l : List Nat) (hl : ∀ d ∈ l, d < 4) (u : Nat) (hu : u < l.length) :
    dig (packD l) u = l[u] := by
  rw [dig_eq, packD_div l hl u hu]

theorem f4mul_lt (x y : Nat) : f4mul x y < 4 := by
  unfold f4mul
  exact Nat.lt_of_lt_of_le (Nat.add_lt_add_of_lt_of_le (Nat.mod_lt _ (by norm_num))
    (Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))))) (by norm_num)

theorem qd_lt (p u : Nat) : qd p u < 4 := by
  unfold qd
  split_ifs
  · exact f4mul_lt _ _
  · omega

theorem dig_qOf (p : Nat) {u : Nat} (hu : u < 37) : dig (qOf p) u = qd p u := by
  unfold qOf
  rw [dig_packD _ (by simp only [List.mem_map]; rintro d ⟨v, -, rfl⟩; exact qd_lt p v) u (by simpa)]
  simp

theorem dig_qS (p c : Nat) {u : Nat} (hu : u < 37) : dig (qS p c) u = f4mul (qd p u) c := by
  unfold qS
  rw [dig_packD _ (by simp only [List.mem_map]; rintro d ⟨v, -, rfl⟩; exact f4mul_lt _ _) u
    (by simpa)]
  simp

theorem qd_code (p : Nat) {a b : Nat} (ha : a < 6) (hb : b < 6) :
    qd p (6 * a + b) = f4mul (coord p a) (f4mul (coord p b) (coord p b)) := by
  unfold qd
  rw [if_pos (by omega), show (6 * a + b) / 6 = a by omega, show (6 * a + b) % 6 = b by omega]

theorem qd_one (p : Nat) : qd p 36 = 1 := rfl

theorem laneQ_congr {Q Q' : Nat} {l : List Nat} (h : ∀ u ∈ l, dig Q u = dig Q' u) :
    laneQ Q l = laneQ Q' l := by
  unfold laneQ
  exact List.foldl_ext _ _ _ fun acc u hu => by rw [h u hu]

theorem foldl_xor_lt (f : Nat → Nat) (hf : ∀ u, f u < 4) (l : List Nat) {a : Nat} (ha : a < 4) :
    l.foldl (fun acc u => acc ^^^ f u) a < 4 := by
  induction l generalizing a with
  | nil => exact ha
  | cons u l ih =>
    rw [List.foldl_cons]
    exact ih (Nat.xor_lt_two_pow (n := 2) ha (hf u))

theorem f4mul_xor : ∀ a < 4, ∀ d < 4, ∀ c < 4, f4mul (a ^^^ d) c = f4mul a c ^^^ f4mul d c := by
  decide

theorem f4mul_zero_left (c : Nat) : f4mul 0 c = 0 := by
  simp [f4mul]

theorem foldl_f4mul (f : Nat → Nat) (hf : ∀ u, f u < 4) (c : Nat) (hc : c < 4) (l : List Nat)
    {a : Nat} (ha : a < 4) :
    l.foldl (fun acc u => acc ^^^ f4mul (f u) c) (f4mul a c) =
      f4mul (l.foldl (fun acc u => acc ^^^ f u) a) c := by
  induction l generalizing a with
  | nil => rfl
  | cons u l ih =>
    rw [List.foldl_cons, List.foldl_cons, ← f4mul_xor a ha (f u) (hf u) c hc]
    exact ih (Nat.xor_lt_two_pow (n := 2) ha (hf u))

@[expose] def laneD (p : Nat) (l : List Nat) : Nat := l.foldl (fun acc u => acc ^^^ qd p u) 0

theorem laneQ_qOf (p : Nat) {l : List Nat} (hl : ∀ u ∈ l, u < 37) : laneQ (qOf p) l = laneD p l := by
  unfold laneQ laneD
  exact List.foldl_ext _ _ _ fun acc u hu => by rw [dig_qOf p (hl u hu)]

theorem laneQ_qS (p c : Nat) (hc : c < 4) {l : List Nat} (hl : ∀ u ∈ l, u < 37) :
    laneQ (qS p c) l = f4mul (laneD p l) c := by
  unfold laneQ laneD
  rw [List.foldl_ext _ (fun acc u => acc ^^^ f4mul (qd p u) c) _
    fun acc u hu => by rw [dig_qS p c (hl u hu)]]
  have h := foldl_f4mul (qd p) (qd_lt p) c hc l (a := 0) (by omega)
  rw [f4mul_zero_left] at h
  exact h

theorem laneD_lt (p : Nat) (l : List Nat) : laneD p l < 4 :=
  foldl_xor_lt _ (qd_lt p) l (by omega)

theorem tri_lt : ∀ s < 20, (tri[s]!).1 < 6 ∧ (tri[s]!).2.1 < 6 ∧ (tri[s]!).2.2 < 6 := by
  decide

theorem termsQ_lt {s t : Nat} (hs : s < 20) (ht : t < 20) : ∀ u ∈ termsQ s t, u < 37 := by
  obtain ⟨h0, h1, h2⟩ := tri_lt s hs
  obtain ⟨g0, g1, g2⟩ := tri_lt t ht
  unfold termsQ
  generalize tri[s]! = A at h0 h1 h2 ⊢
  generalize tri[t]! = B at g0 g1 g2 ⊢
  obtain ⟨i0, i1, i2⟩ := A
  obtain ⟨j0, j1, j2⟩ := B
  dsimp only at *
  split_ifs <;> simp <;> omega

theorem laneD_termsQ (p : Nat) {s t : Nat} (hs : s < 20) (ht : t < 20) :
    laneD p (termsQ s t) = minorK p s t := by
  obtain ⟨h0, h1, h2⟩ := tri_lt s hs
  obtain ⟨g0, g1, g2⟩ := tri_lt t ht
  unfold laneD termsQ minorK minorG
  generalize tri[s]! = A at h0 h1 h2 ⊢
  generalize tri[t]! = B at g0 g1 g2 ⊢
  obtain ⟨i0, i1, i2⟩ := A
  obtain ⟨j0, j1, j2⟩ := B
  dsimp only at *
  split_ifs <;> simp (disch := omega) [qd_code, qd_one]

theorem pack_foldr (f : Nat → Nat) (n init : Nat) :
    ((List.range n).map f).foldr (fun v acc => v + 4 * acc) init =
      (List.range n).foldl (fun acc k => acc + f k * 4 ^ k) 0 + init * 4 ^ n := by
  induction n generalizing init with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.foldr_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, List.foldl_cons,
      List.foldl_nil]
    rw [ih, pow_succ]
    ring

theorem zipIdx_map_range {α β : Type} (g : Nat → α) (F : α × Nat → β) (n : Nat) :
    ((List.range n).map g).zipIdx.map F = (List.range n).map fun m => F (g m, m) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_zipIdx]

theorem f4sq_one : f4sq 1 = 1 := rfl

theorem f4sq_two : f4sq 2 = 3 := rfl

theorem f4mul_one (x : Nat) (hx : x < 4) : f4mul x 1 = x := by
  interval_cases x <;> rfl

theorem tvQ_cTabQ (p : Nat) : tvQ cTabQ p = tvK p := by
  unfold tvQ hQ cTabQ tvK
  rw [zipIdx_map_range]
  apply List.map_congr_left
  intro m hm
  have hm' : m < 20 := List.mem_range.1 hm
  have hc : ∀ QA QB, colQ QA QB ((List.range 10).map fun k =>
      [termsQ k (m / 2), termsQ k (19 - m / 2)]) = ((List.range 10).map fun k =>
        laneQ QA (termsQ k (m / 2)) ^^^ laneQ QB (termsQ k (19 - m / 2))).foldr
          (fun v acc => v + 4 * acc) 0 := by
    intro QA QB
    unfold colQ
    rw [List.foldr_map, List.foldr_map]
    rfl
  have ha : m / 2 < 20 := by omega
  have hb : 19 - m / 2 < 20 := by omega
  dsimp only
  unfold colK
  rw [hc, hc, pack_foldr, pack_foldr]
  simp only [Nat.zero_mul, Nat.add_zero]
  split_ifs with h
  · have h1 : 1 + m % 2 = 1 := by omega
    apply List.foldl_ext
    intro acc k hk
    have hk' : k < 20 := by have := List.mem_range.1 hk; omega
    rw [laneQ_qOf p (termsQ_lt hk' ha), laneQ_qOf p (termsQ_lt hk' hb), ← laneD_termsQ p hk' ha,
      ← laneD_termsQ p hk' hb, h1, f4sq_one, f4mul_one _ (laneD_lt _ _),
      f4mul_one _ (laneD_lt _ _)]
  · have h2 : 1 + m % 2 = 2 := by omega
    apply List.foldl_ext
    intro acc k hk
    have hk' : k < 20 := by have := List.mem_range.1 hk; omega
    rw [laneQ_qS p 2 (by omega) (termsQ_lt hk' ha), laneQ_qS p 3 (by omega) (termsQ_lt hk' hb),
      ← laneD_termsQ p hk' ha, ← laneD_termsQ p hk' hb, h2, f4sq_two]

end CFSG.SmithE.K
