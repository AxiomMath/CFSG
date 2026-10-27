module

public import CFSG.GF2Type.SmithTypeE.LMod.UaRank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.LMod

open CFSG.SmithL6
open CFSG.SmithE (applyCols)
open scoped Pointwise

attribute [local irreducible] stabGens elemGens planeImg meetCard dRoot tvIdxTab tvTab tvImg tvList

theorem applyCols_aux_succ (f : ℕ → ℕ → ℕ) (s n : ℕ) :
    (List.range (n + 1)).foldl f s = f ((List.range n).foldl f s) n := by
  rw [List.range_succ, List.foldl_append]
  rfl

theorem applyCols_aux_cancel (x y w : ℕ) : (x ^^^ w) ^^^ (y ^^^ w) = x ^^^ y := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases x.testBit i <;> cases y.testBit i <;> cases w.testBit i <;> rfl

theorem applyCols_aux_zero (cols : Array ℕ) (n : ℕ) :
    (List.range n).foldl (fun acc m => if (0 : ℕ).testBit m then acc ^^^ cols[m]! else acc) 0 = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [applyCols_aux_succ, ih]
    simp

theorem applyCols_aux_xor (cols : Array ℕ) (a b n : ℕ) :
    (List.range n).foldl (fun acc m => if (a ^^^ b).testBit m then acc ^^^ cols[m]! else acc) 0 =
      (List.range n).foldl (fun acc m => if a.testBit m then acc ^^^ cols[m]! else acc) 0 ^^^
        (List.range n).foldl (fun acc m => if b.testBit m then acc ^^^ cols[m]! else acc) 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [applyCols_aux_succ, applyCols_aux_succ, applyCols_aux_succ, ih]
    try dsimp only
    rw [Nat.testBit_xor]
    generalize (List.range n).foldl (fun acc m => if a.testBit m then acc ^^^ cols[m]! else acc) 0 = x
    generalize (List.range n).foldl (fun acc m => if b.testBit m then acc ^^^ cols[m]! else acc) 0 = y
    generalize cols[n]! = w
    cases ha : a.testBit n <;> cases hb : b.testBit n <;> simp [ha, hb] <;>
      (first
        | ac_rfl
        | exact (applyCols_aux_cancel x y w).symm
        | (apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_xor]; cases x.testBit i <;> cases y.testBit i <;> cases w.testBit i <;> rfl))

theorem applyCols_aux_pow (cols : Array ℕ) (m n : ℕ) :
    (List.range n).foldl (fun acc k => if (2 ^ m).testBit k then acc ^^^ cols[k]! else acc) 0 =
      if m < n then cols[m]! else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [applyCols_aux_succ, ih]
    try dsimp only
    by_cases hmn : m = n
    · subst hmn
      simp [Nat.testBit_two_pow]
    · simp [Nat.testBit_two_pow, hmn]
      split_ifs <;> first | rfl | omega

theorem applyCols_aux_lt (cols : Array ℕ) (a : ℕ) (h : ∀ j < 9, cols[j]! < 512) :
    ∀ n, n ≤ 9 →
      (List.range n).foldl (fun acc m => if a.testBit m then acc ^^^ cols[m]! else acc) 0 < 512 := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [applyCols_aux_succ]
    have hS := ih (by omega)
    have hc := h n (by omega)
    try dsimp only
    split_ifs
    · have h9 : (512 : ℕ) = 2 ^ 9 := by norm_num
      rw [h9] at hS hc ⊢
      exact Nat.xor_lt_two_pow hS hc
    · exact hS

theorem applyCols_lt {cols : Array ℕ} (hs : cols.size = 9) (h : ∀ j < 9, cols[j]! < 512) (a : ℕ) :
    applyCols cols a < 512 := by
  unfold applyCols
  rw [hs]
  exact applyCols_aux_lt cols a h 9 le_rfl

theorem applyCols_xor {cols : Array ℕ} (a b : ℕ) :
    applyCols cols (a ^^^ b) = applyCols cols a ^^^ applyCols cols b := by
  unfold applyCols
  exact applyCols_aux_xor cols a b cols.size

theorem applyCols_pow {cols : Array ℕ} {m : ℕ} (hm : m < cols.size) :
    applyCols cols (2 ^ m) = cols[m]! := by
  unfold applyCols
  rw [applyCols_aux_pow cols m cols.size, if_pos hm]

theorem applyCols_zero (cols : Array ℕ) : applyCols cols 0 = 0 := by
  unfold applyCols
  exact applyCols_aux_zero cols cols.size

theorem applyCols_congr {cols cols' : Array ℕ} (hs : cols.size = 9) (hs' : cols'.size = 9)
    (h : ∀ m < 9, applyCols cols (2 ^ m) = applyCols cols' (2 ^ m)) (a : ℕ) :
    applyCols cols a = applyCols cols' a := by
  have hc : ∀ m < 9, cols[m]! = cols'[m]! := by
    intro m hm
    have h1 : applyCols cols (2 ^ m) = cols[m]! := applyCols_pow (by rw [hs]; exact hm)
    have h2 : applyCols cols' (2 ^ m) = cols'[m]! := applyCols_pow (by rw [hs']; exact hm)
    exact h1.symm.trans ((h m hm).trans h2)
  have key : ∀ n, n ≤ 9 →
      (List.range n).foldl (fun acc m => if a.testBit m then acc ^^^ cols[m]! else acc) 0 =
        (List.range n).foldl (fun acc m => if a.testBit m then acc ^^^ cols'[m]! else acc) 0 := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [applyCols_aux_succ, applyCols_aux_succ, ih (by omega)]
      try dsimp only
      rw [hc n (by omega)]
  unfold applyCols
  rw [hs, hs']
  exact key 9 le_rfl

section Act


@[expose] noncomputable def colsOf (π : Equiv.Perm (Fin 1953)) : Array ℕ :=
  Array.ofFn (n := 9) fun j => uco[pos0 (π (gen0 j.val)).val]!

theorem colsOf_size (π : Equiv.Perm (Fin 1953)) : (colsOf π).size = 9 := by
  simp [colsOf]

theorem pos0_lt_49_of_mem {y : Fin 1953} (hy : y ∈ wPlane 0) : pos0 y.val < 49 := by
  have hmem : y.val ∈ planePtsArr[0]! := hd3_mem_planePtsArr_zero.2 ⟨y.isLt, mem_wPlane.1 hy⟩
  unfold pos0
  rw [← planePtsArr0_size]
  exact Array.findIdx_lt_size_of_exists ⟨y.val, hmem, by simp⟩

theorem colsOf_get (π : Equiv.Perm (Fin 1953)) {j : ℕ} (hj : j < 9) :
    (colsOf π)[j]! = uco[pos0 (π (gen0 j)).val]! := by
  have hj' : j < (colsOf π).size := by
    rw [colsOf_size]
    exact hj
  rw [getElem!_pos (colsOf π) j hj']
  simp [colsOf]

theorem conj_psi0_gen {π : Equiv.Perm (Fin 1953)} (hπ : IsTvAut π) (hW : ⇑π '' wPlane 0 = wPlane 0)
    (a : ℕ) : π * psi0 a * π⁻¹ = psi0 (applyCols (colsOf π) a) := by
  have hcol : ∀ j < 9, π * tvP (gen0 j) * π⁻¹ = psi0 ((colsOf π)[j]!) := by
    intro j hj
    have hw : π (gen0 j) ∈ wPlane 0 := by
      rw [← hW]
      exact Set.mem_image_of_mem _ (gen0_mem j hj)
    rw [hπ (gen0 j), tvP_eq_psi0_pos0 hw, colsOf_get π hj]
  have e0 : psi0 a = bitProd (fun j => tvP (gen0 j)) a 9 := rfl
  have e1 : π * psi0 a * π⁻¹ = bitProd (fun j => psi0 ((colsOf π)[j]!)) a 9 := by
    rw [e0, conj_bitProd]
    exact bitProd_congr a 9 (fun j hj => hcol j hj)
  have e2 : bitProd (fun j => psi0 ((colsOf π)[j]!)) a 9 = psi0 (applyCols (colsOf π) a) := by
    refine (bitProd_hom psi0_zero psi0_xor (fun j => (colsOf π)[j]!) a 9).trans ?_
    rw [CFSG.SmithE.applyCols, colsOf_size]
  exact e1.trans e2

theorem colsOf_point {π : Equiv.Perm (Fin 1953)} (hπ : IsTvAut π) (hW : ⇑π '' wPlane 0 = wPlane 0)
    {j : ℕ} (hj : j < 9) : ∃ k < 49, uco[k]! = (colsOf π)[j]! := by
  have hw : π (gen0 j) ∈ wPlane 0 := by
    rw [← hW]
    exact Set.mem_image_of_mem _ (gen0_mem j hj)
  exact ⟨pos0 (π (gen0 j)).val, pos0_lt_49_of_mem hw, (colsOf_get π hj).symm⟩

theorem colsOf_lt {π : Equiv.Perm (Fin 1953)} (hπ : IsTvAut π) (hW : ⇑π '' wPlane 0 = wPlane 0)
    {j : ℕ} (hj : j < 9) : (colsOf π)[j]! < 512 := by
  obtain ⟨k, hk, he⟩ := colsOf_point hπ hW hj
  rw [← he]
  exact (uaFacts.uco_parts k hk).2

theorem two_pow_lt_512 {m : ℕ} (hm : m < 9) : 2 ^ m < 512 := by
  interval_cases m <;> norm_num

theorem act_one (a : ℕ) (ha : a < 512) : applyCols (colsOf 1) a = a := by
  have hW1 : ⇑(1 : Equiv.Perm (Fin 1953)) '' wPlane 0 = wPlane 0 := by simp
  have h1 := conj_psi0_gen IsTvAut.one hW1 a
  simp only [one_mul, inv_one, mul_one] at h1
  exact (psi0_inj ha (applyCols_lt (colsOf_size 1)
    (fun j hj => colsOf_lt IsTvAut.one hW1 hj) a) h1).symm

theorem act_mul {π ρ : Equiv.Perm (Fin 1953)} (hπ : IsTvAut π) (hπW : ⇑π '' wPlane 0 = wPlane 0)
    (hρ : IsTvAut ρ) (hρW : ⇑ρ '' wPlane 0 = wPlane 0) (a : ℕ) :
    applyCols (colsOf (π * ρ)) a = applyCols (colsOf π) (applyCols (colsOf ρ) a) := by
  have hmul : IsTvAut (π * ρ) := IsTvAut.mul hπ hρ
  have hmulW : ⇑(π * ρ) '' wPlane 0 = wPlane 0 := by
    rw [Equiv.Perm.coe_mul, Set.image_comp, hρW, hπW]
  have h1 := conj_psi0_gen hmul hmulW a
  have h2 := conj_psi0_gen hρ hρW a
  have h3 := conj_psi0_gen hπ hπW (applyCols (colsOf ρ) a)
  have key : (π * ρ) * psi0 a * (π * ρ)⁻¹ = π * (ρ * psi0 a * ρ⁻¹) * π⁻¹ := by group
  rw [h1, h2, h3] at key
  exact psi0_inj (applyCols_lt (colsOf_size (π * ρ))
    (fun j hj => colsOf_lt hmul hmulW hj) a)
    (applyCols_lt (colsOf_size π) (fun j hj => colsOf_lt hπ hπW hj) _) key

theorem act_pt {π : Equiv.Perm (Fin 1953)} (hπ : IsTvAut π) (hW : ⇑π '' wPlane 0 = wPlane 0)
    {k : ℕ} (hk : k < 49) :
    applyCols (colsOf π) uco[k]! = uco[pos0 (π (pt0 k)).val]! := by
  have hpW : π (pt0 k) ∈ wPlane 0 := by
    rw [← hW]
    exact Set.mem_image_of_mem _ (pt0_mem hk)
  have h1 := conj_psi0_gen hπ hW (uco[k]!)
  rw [← tvP_pt0 hk, hπ (pt0 k), tvP_eq_psi0_pos0 hpW] at h1
  exact (psi0_inj (uaFacts.uco_parts _ (pos0_lt_49_of_mem hpW)).2
    (applyCols_lt (colsOf_size π) (fun j hj => colsOf_lt hπ hW hj) (uco[k]!)) h1).symm

theorem colsOf_eq_one_iff {π : Equiv.Perm (Fin 1953)} (hπ : IsTvAut π)
    (hW : ⇑π '' wPlane 0 = wPlane 0) :
    (∀ m < 9, applyCols (colsOf π) (2 ^ m) = 2 ^ m) ↔ ∀ p ∈ wPlane 0, π p = p := by
  constructor
  · intro h p hp
    obtain ⟨k, hk, rfl⟩ := exists_pt0 hp
    have hfix : ∀ a < 512, applyCols (colsOf π) a = a := by
      intro a ha
      have hc := applyCols_congr (colsOf_size π) (colsOf_size 1)
        (fun m hm => by rw [h m hm, act_one (2 ^ m) (two_pow_lt_512 hm)]) a
      rw [hc, act_one a ha]
    have hpW : π (pt0 k) ∈ wPlane 0 := by
      rw [← hW]
      exact Set.mem_image_of_mem _ (pt0_mem hk)
    have h1 := act_pt hπ hW hk
    rw [hfix _ (uaFacts.uco_parts k hk).2] at h1
    apply tvP_injective
    rw [tvP_eq_psi0_pos0 hpW, ← h1, tvP_pt0 hk]
  · intro hfix m hm
    have hm' : m < (colsOf π).size := by rw [colsOf_size]; exact hm
    have hm1 : m < (colsOf 1).size := by rw [colsOf_size]; exact hm
    have h1 : uco[pos0 (gen0 m).val]! = 2 ^ m := by
      have h := act_one (2 ^ m) (two_pow_lt_512 hm)
      rw [applyCols_pow hm1, colsOf_get 1 hm] at h
      simpa using h
    rw [applyCols_pow hm', colsOf_get π hm, hfix _ (gen0_mem m hm), h1]

theorem apply_eq_of_colsOf_eq {π ρ : Equiv.Perm (Fin 1953)} (hπ : IsTvAut π)
    (hπW : ⇑π '' wPlane 0 = wPlane 0) (hρ : IsTvAut ρ) (hρW : ⇑ρ '' wPlane 0 = wPlane 0)
    (h : ∀ m < 9, applyCols (colsOf π) (2 ^ m) = applyCols (colsOf ρ) (2 ^ m)) :
    ∀ p ∈ wPlane 0, π p = ρ p := by
  intro p hp
  obtain ⟨k, hk, rfl⟩ := exists_pt0 hp
  have hπpW : π (pt0 k) ∈ wPlane 0 := by
    rw [← hπW]
    exact Set.mem_image_of_mem _ (pt0_mem hk)
  have hρpW : ρ (pt0 k) ∈ wPlane 0 := by
    rw [← hρW]
    exact Set.mem_image_of_mem _ (pt0_mem hk)
  have hc := applyCols_congr (colsOf_size π) (colsOf_size ρ) h (uco[k]!)
  have h1 := act_pt hπ hπW hk
  have h2 := act_pt hρ hρW hk
  rw [hc, h2] at h1
  apply tvP_injective
  rw [tvP_eq_psi0_pos0 hπpW, tvP_eq_psi0_pos0 hρpW, h1]

end Act

end CFSG.GF2Type.SmithTypeE.LMod
