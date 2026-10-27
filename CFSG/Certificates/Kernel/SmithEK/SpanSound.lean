module

public import Certificates.Data.Kernel.SmithEKS
public import CFSG.Certificates.Kernel.SmithEK.FastSound

public section

namespace CFSG.SmithE.K

open CFSG.F4.Native CFSG.SmithE

theorem m01_testBit : ∀ i < 74, m01.testBit i = (i % 2 == 0) := by
  decide +kernel

theorem dig_bits (X u : Nat) :
    dig X u = (X.testBit (2 * u)).toNat + 2 * (X.testBit (2 * u + 1)).toNat := by
  unfold dig
  have h0 : (X >>> (2 * u)).testBit 0 = X.testBit (2 * u) := by
    rw [Nat.testBit_shiftRight, Nat.add_zero]
  have h1 : (X >>> (2 * u)).testBit 1 = X.testBit (2 * u + 1) := by
    rw [Nat.testBit_shiftRight]
  rw [← h0, ← h1]
  generalize X >>> (2 * u) = Y
  rw [Nat.testBit_zero, ← Nat.testBit_div_two, Nat.testBit_zero]
  have : Y % 4 = Y % 2 + 2 * (Y / 2 % 2) := by omega
  rw [this]
  rcases Nat.mod_two_eq_zero_or_one Y with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one (Y / 2) with h' | h' <;> simp [h, h']

theorem f4mul_two_bits (a b : Bool) :
    f4mul (a.toNat + 2 * b.toNat) 2 = b.toNat + 2 * (a ^^ b).toNat := by
  cases a <;> cases b <;> rfl

theorem f4mul_three_bits (a b : Bool) :
    f4mul (a.toNat + 2 * b.toNat) 3 = (a ^^ b).toNat + 2 * a.toNat := by
  cases a <;> cases b <;> rfl

theorem dig_wM (Q : Nat) {u : Nat} (hu : u < 37) : dig (wM Q) u = f4mul (dig Q u) 2 := by
  have e0 := m01_testBit (2 * u) (by omega)
  have e1 := m01_testBit (2 * u + 1) (by omega)
  have e2 : 2 * u ≥ 1 → m01.testBit (2 * u - 1) = false := fun h => by
    rw [m01_testBit _ (by omega)]
    simp only [beq_eq_false_iff_ne]
    omega
  rw [dig_bits, dig_bits, f4mul_two_bits]
  simp only [Nat.mul_mod_right, beq_self_eq_true, Nat.mul_add_mod, Nat.reduceMod,
    Nat.reduceBEq] at e0 e1
  have hm : m01 % 2 = 1 := by decide +kernel
  unfold wM
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, e0, e1]
  rcases Nat.eq_zero_or_pos u with rfl | hu0
  · simp [Nat.add_comm, hm]
  · rw [e2 (by omega)]
    simp [Nat.add_comm, show 2 * u + 1 - 1 = 2 * u by omega, show 2 * u ≥ 1 by omega, e0, e1]

theorem dig_wM2 (Q : Nat) {u : Nat} (hu : u < 37) : dig (wM2 Q) u = f4mul (dig Q u) 3 := by
  have e0 := m01_testBit (2 * u) (by omega)
  have e1 := m01_testBit (2 * u + 1) (by omega)
  have e2 : 2 * u ≥ 1 → m01.testBit (2 * u - 1) = false := fun h => by
    rw [m01_testBit _ (by omega)]
    simp only [beq_eq_false_iff_ne]
    omega
  rw [dig_bits, dig_bits, f4mul_three_bits]
  simp only [Nat.mul_mod_right, beq_self_eq_true, Nat.mul_add_mod, Nat.reduceMod,
    Nat.reduceBEq] at e0 e1
  have hm : m01 % 2 = 1 := by decide +kernel
  unfold wM2
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, e0, e1]
  rcases Nat.eq_zero_or_pos u with rfl | hu0
  · simp [Nat.add_comm, hm]
  · rw [e2 (by omega)]
    simp [Nat.add_comm, show 2 * u + 1 - 1 = 2 * u by omega, show 2 * u ≥ 1 by omega, e0, e1]
    try omega

theorem colQ_congr {A B A' B' : Nat} (col : List (List (List Nat)))
    (h0 : ∀ ab ∈ col, ∀ u ∈ ab.getD 0 [], u < 37) (h1 : ∀ ab ∈ col, ∀ u ∈ ab.getD 1 [], u < 37)
    (hA : ∀ u < 37, dig A u = dig A' u) (hB : ∀ u < 37, dig B u = dig B' u) :
    colQ A B col = colQ A' B' col := by
  induction col with
  | nil => rfl
  | cons ab col ih =>
    unfold colQ at *
    rw [List.foldr_cons, List.foldr_cons,
      ih (fun ab' h u hu => h0 ab' (by simp [h]) u hu) (fun ab' h u hu => h1 ab' (by simp [h]) u hu),
      laneQ_congr (fun u hu => hA u (h0 ab (by simp) u hu)),
      laneQ_congr (fun u hu => hB u (h1 ab (by simp) u hu))]

theorem tvW_cTabQ (p : Nat) : tvW cTabQ p = tvK p := by
  rw [← tvQ_cTabQ]
  unfold tvW tvQ hQ cTabQ
  rw [zipIdx_map_range, zipIdx_map_range]
  apply List.map_congr_left
  intro m hm
  have hm' : m < 20 := List.mem_range.1 hm
  have hT : ∀ i, ∀ ab ∈ (List.range 10).map (fun k => [termsQ k (m / 2), termsQ k (19 - m / 2)]),
      ∀ u ∈ ab.getD i [], u < 37 := by
    intro i ab hab u hu
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hab
    have hk' : k < 20 := by have := List.mem_range.1 hk; omega
    match i, hu with
    | 0, hu => exact termsQ_lt hk' (by omega) u hu
    | 1, hu => exact termsQ_lt hk' (by omega) u hu
    | _ + 2, hu => simp at hu
  dsimp only
  split_ifs
  · rfl
  · exact colQ_congr _ (hT 0) (hT 1)
      (fun u hu => by rw [dig_wM _ hu, dig_qS _ _ hu, dig_qOf _ hu])
      (fun u hu => by rw [dig_wM2 _ hu, dig_qS _ _ hu, dig_qOf _ hu])

theorem applyCols_toArray (l : List Nat) (c : Nat) : applyCols l.toArray c = applyL l c := by
  suffices h : ∀ (l : List Nat) (c a : Nat), (List.range l.length).foldl
      (fun acc m => if c.testBit m then acc ^^^ l.toArray[m]! else acc) a = a ^^^ applyL l c by
    unfold applyCols
    simpa using h l c 0
  intro l
  induction l with
  | nil => intro c a; simp [applyL]
  | cons x l ih =>
    intro c a
    rw [List.length_cons, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    rw [List.foldl_ext _ (fun acc m => if (c / 2).testBit m then acc ^^^ l.toArray[m]! else acc) _
      (fun acc m _ => by simp [Nat.testBit_div_two])]
    rw [ih]
    have e : applyL (x :: l) c = (if c.testBit 0 then x else 0) ^^^ applyL l (c / 2) := rfl
    rw [e]
    split_ifs <;> simp [Nat.xor_assoc]

theorem applyL_zero (S : List Nat) : applyL S 0 = 0 := by
  induction S with
  | nil => rfl
  | cons x S ih =>
    have e : applyL (x :: S) 0 = (if (0 : Nat).testBit 0 then x else 0) ^^^ applyL S (0 / 2) := rfl
    rw [e, Nat.zero_div, ih]
    simp

theorem ite_xor_bool (p q : Bool) (x : Nat) :
    (if (p ^^ q) = true then x else 0) = (if p = true then x else 0) ^^^ (if q = true then x else 0) := by
  cases p <;> cases q <;> simp

theorem applyL_xor : ∀ (S : List Nat) (a b : Nat), applyL S (a ^^^ b) = applyL S a ^^^ applyL S b
  | [], a, b => by simp [applyL]
  | x :: S, a, b => by
    have e : ∀ c, applyL (x :: S) c = (if c.testBit 0 then x else 0) ^^^ applyL S (c / 2) :=
      fun c => rfl
    rw [e, e, e, Nat.testBit_xor, Nat.xor_div_two, applyL_xor S, ite_xor_bool]
    ac_rfl

theorem applyL_comp (S : List Nat) : ∀ (B : List Nat) (c : Nat),
    applyL S (applyL B c) = applyL (B.map (applyL S)) c
  | [], _ => applyL_zero S
  | x :: B, c => by
    have e : ∀ (l : List Nat) (y c : Nat),
        applyL (y :: l) c = (if c.testBit 0 then y else 0) ^^^ applyL l (c / 2) := fun _ _ _ => rfl
    rw [e, List.map_cons, e, applyL_xor, applyL_comp S B]
    split_ifs <;> simp [applyL_zero]

theorem applyL_of_zero : ∀ (Z : List Nat) (c : Nat), (∀ z ∈ Z, z = 0) → applyL Z c = 0
  | [], _, _ => rfl
  | z :: Z, c, h => by
    have e : applyL (z :: Z) c = (if c.testBit 0 then z else 0) ^^^ applyL Z (c / 2) := rfl
    rw [e, applyL_of_zero Z _ (fun y hy => h y (by simp [hy])), h z (by simp)]
    simp

@[expose] def spanOKA (T : Array Nat) : Bool :=
  let D := spanData T; let g := gensOf T
  D.basis.size == 6 && D.coef.size == 20 &&
    (List.range 20).all fun m => decide (D.coef[m]! < 64) &&
      applyCols D.basis D.coef[m]! == g[m]! && applyCols D.syn g[m]! == 0

theorem coefR_scale (v : Nat) : ∀ (E : List (Nat × Nat)) (s a : Nat),
    (List.range E.length).foldl (fun acc i => if v.testBit (E[i]!).1 then acc + s * 2 ^ i else acc)
      a = a + s * coefR E v := by
  intro E
  induction E with
  | nil => intro s a; simp [coefR]
  | cons be E ih =>
    intro s a
    rw [List.length_cons, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    rw [List.foldl_ext _ (fun acc i => if v.testBit (E[i]!).1 then acc + (2 * s) * 2 ^ i else acc) _
      (fun acc i _ => by simp [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc])]
    rw [ih]
    have e : coefR (be :: E) v = (if v.testBit be.1 then 1 else 0) + 2 * coefR E v := rfl
    have h0 : (be :: E)[0]! = be := rfl
    rw [e, h0]
    split_ifs <;> ring

theorem coefR_eq (E : List (Nat × Nat)) (v : Nat) : coefR E v = coefOf E v := by
  have h := coefR_scale v E 1 0
  simp only [Nat.one_mul, Nat.zero_add] at h
  exact h.symm

theorem gensOf_toList {L : List Nat} (hL : L.length = 20) : (gensOf L.toArray).toList = gensL L := by
  apply List.ext_getElem
  · simp [gensOf, gensL, hL]
  · intro i h1 h2
    have hi : i < 20 := by simpa [gensL, hL] using h2
    simp only [gensOf, Array.getElem_toList, Array.getElem_ofFn, gensL, List.getElem_map,
      List.getElem_zipIdx, Nat.zero_add]
    rw [getElem!_pos L.toArray i (by simpa [hL] using hi)]
    simp

theorem spanOKA_of {L : List Nat} (hL : L.length = 20) (h : spanOKL L = true) :
    spanOKA L.toArray = true := by
  have hg := gensOf_toList hL
  have hsz : (gensOf L.toArray).size = 20 := by simp [gensOf]
  have hE : echelon L.toArray = (gensL L).foldl insertVec [] := by
    unfold echelon
    rw [hg]
  unfold spanOKL at h
  unfold spanOKA spanData
  rw [hE]
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hlen, hBz⟩, hall⟩ := h
  generalize hG : gensL L = G at hall hBz hlen hg ⊢
  generalize hEq : G.foldl insertVec [] = E at hall hBz hlen ⊢
  generalize gensOf L.toArray = g at hg hsz ⊢
  simp only [coefR_eq] at hall
  have hS : (Array.ofFn (n := 20) fun m => reduceBy E (2 ^ m.val)) =
      ((List.range 20).map fun m => reduceBy E (2 ^ m)).toArray := by
    apply Array.ext
    · simp
    · intro i h1 h2
      simp
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq, hS,
    applyCols_toArray]
  refine ⟨⟨by simp [hlen], by simp [hsz]⟩, ?_⟩
  intro m hm
  have hm' : m < 20 := List.mem_range.1 hm
  have hgm : g[m]! = G[m]'(by rw [← hg]; simpa [hsz] using hm') := by
    rw [getElem!_pos g m (by omega)]
    simp only [← hg, Array.getElem_toList]
  have hv : G[m]'(by rw [← hg]; simpa [hsz] using hm') ∈ G := List.getElem_mem _
  obtain ⟨c1, c2⟩ := hall _ hv
  have c3 : applyL ((List.range 20).map fun m => reduceBy E (2 ^ m))
      (G[m]'(by rw [← hg]; simpa [hsz] using hm')) = 0 := by
    rw [← c2, applyL_comp]
    apply applyL_of_zero
    intro z hz
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hz
    exact hBz b hb
  have hc : (g.map fun v => (List.range E.length).foldl
      (fun acc i => if v.testBit (E[i]!).1 then acc + 2 ^ i else acc) 0)[m]! =
      coefOf E (G[m]'(by rw [← hg]; simpa [hsz] using hm')) := by
    rw [getElem!_pos _ m (by simp; omega), Array.getElem_map, ← hgm, getElem!_pos g m (by omega)]
    rfl
  rw [hc, hgm]
  exact ⟨⟨c1, c2⟩, c3⟩

theorem chkSpan_of (h : ∀ k < 693, spanOKA (tvCols k) = true) : chkSpan = true := by
  unfold chkSpan
  rw [List.all_eq_true]
  intro k hk
  have hk' : k < 693 := List.mem_range.1 hk
  have e1 : spanArr[k]! = spanData (tvCols k) := by
    rw [getElem!_pos spanArr k (by simp [spanArr, tvArr, hk'])]
    simp [spanArr, tvArr]
  have e2 : tvArr[k]! = tvCols k := by
    rw [getElem!_pos tvArr k (by simp [tvArr, hk'])]
    simp [tvArr]
  rw [e1, e2]
  exact h k hk'

end CFSG.SmithE.K
