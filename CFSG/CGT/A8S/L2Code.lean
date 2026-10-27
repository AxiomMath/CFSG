module

public import CFSG.CGT.A8S.N0Model

public section

namespace CFSG.CGT.A8S.L2

open CFSG.CosetTable CFSG.CGT.A8S.N0

@[expose] def affOf (π : Equiv.Perm (Fin 8)) : ℕ × Cols3 :=
  ((π 0).val, ⟨(π 1).val ^^^ (π 0).val, (π 2).val ^^^ (π 0).val, (π 4).val ^^^ (π 0).val⟩)

@[expose] def avc (x : PG 5 relsN0A8) : ℕ := affCode (affOf (n0Perm x))

@[expose] def decA (c : ℕ) : ℕ × Cols3 := (c % 8, ⟨c / 8 % 8, c / 64 % 8, c / 512 % 8⟩)

@[expose] def affMul (p q : ℕ × Cols3) : ℕ × Cols3 := (p.1 ^^^ applyC3 p.2 q.1, compC3 p.2 q.2)

@[expose] def cmul (a b : ℕ) : ℕ := affCode (affMul (decA a) (decA b))

@[expose] def gl3 : List Cols3 := allCols3.filter isGL3

@[expose] def allCodes : List ℕ :=
  (List.range 8).flatMap fun v => gl3.map fun C => affCode (v, C)

@[expose] def validC (c : ℕ) : Bool := Nat.blt c 4096 && isGL3 (colsOfCode3 (c / 8))

theorem xor_xor_cancel (v c : ℕ) : (v ^^^ c) ^^^ v = c := by
  rw [Nat.xor_comm v c, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem xor_lt8 {a b : ℕ} (ha : a < 8) (hb : b < 8) : a ^^^ b < 8 :=
  Nat.xor_lt_two_pow (n := 3) ha hb

theorem affOf_eq {π : Equiv.Perm (Fin 8)} {p : ℕ × Cols3}
    (h : ∀ i : Fin 8, (π i).val = p.1 ^^^ applyC3 p.2 i.val) : affOf π = p := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h4 := h 4
  simp only [Fin.isValue, Fin.val_zero, applyC3_zero, Nat.xor_zero] at h0
  have e1 : applyC3 p.2 (1 : Fin 8).val = p.2.c0 := applyC3_basis p.2 0
  have e2 : applyC3 p.2 (2 : Fin 8).val = p.2.c1 := applyC3_basis p.2 1
  have e4 : applyC3 p.2 (4 : Fin 8).val = p.2.c2 := applyC3_basis p.2 2
  rw [e1] at h1
  rw [e2] at h2
  rw [e4] at h4
  refine Prod.ext h0 (Cols3.ext ?_ ?_ ?_) <;> simp only [affOf]
  · rw [h1, h0, xor_xor_cancel]
  · rw [h2, h0, xor_xor_cancel]
  · rw [h4, h0, xor_xor_cancel]

theorem affOf_n0Perm_mk (w : List (Fin 5 × Bool)) :
    affOf (n0Perm (PresentedGroup.mk _ (FreeGroup.mk w))) = affEval w :=
  affOf_eq fun i => N0.n0Perm_mk_apply w i

theorem n0Perm_apply_val (x : PG 5 relsN0A8) (i : Fin 8) :
    (n0Perm x i).val = (affOf (n0Perm x)).1 ^^^ applyC3 (affOf (n0Perm x)).2 i.val := by
  obtain ⟨k, rfl⟩ := n0_forall x
  rw [affOf_n0Perm_mk]
  exact N0.n0Perm_mk_apply _ i

theorem affOf_fst_lt (π : Equiv.Perm (Fin 8)) : (affOf π).1 < 8 := (π 0).isLt

theorem affOf_col_lt (π : Equiv.Perm (Fin 8)) (j : Fin 3) : (affOf π).2.col j < 8 := by
  fin_cases j <;> exact xor_lt8 (Fin.isLt _) (Fin.isLt _)

theorem decA_affCode {p : ℕ × Cols3} (h1 : p.1 < 8) (h2 : ∀ j, p.2.col j < 8) :
    decA (affCode p) = p := by
  obtain ⟨v, ⟨a, b, c⟩⟩ := p
  have ha := h2 0
  have hb := h2 1
  have hc := h2 2
  simp only [Cols3.col] at ha hb hc h1
  simp only [decA, affCode, Prod.mk.injEq, Cols3.mk.injEq]
  omega

theorem decA_avc (x : PG 5 relsN0A8) : decA (avc x) = affOf (n0Perm x) :=
  decA_affCode (affOf_fst_lt _) (affOf_col_lt _)

theorem avc_inj {x y : PG 5 relsN0A8} (h : avc x = avc y) :
    x = y := by
  have h' : affOf (n0Perm x) = affOf (n0Perm y) := by rw [← decA_avc, ← decA_avc, h]
  apply n0Perm_injective
  refine Equiv.ext fun i => Fin.ext ?_
  rw [n0Perm_apply_val, n0Perm_apply_val, h']

theorem avc_mk (w : List (Fin 5 × Bool)) :
    avc (PresentedGroup.mk _ (FreeGroup.mk w)) = affCode (affEval w) := by
  rw [avc, affOf_n0Perm_mk]

theorem avc_one : avc 1 = 2184 := by
  rw [avc, map_one]
  rfl

theorem avc_mul (x y : PG 5 relsN0A8) :
    avc (x * y) = cmul (avc x) (avc y) := by
  rw [cmul, decA_avc, decA_avc, avc]
  congr 1
  refine affOf_eq fun i => ?_
  rw [map_mul, Equiv.Perm.mul_apply, n0Perm_apply_val x, n0Perm_apply_val y, affMul,
    applyC3_xor, Nat.xor_assoc, ← applyC3_compC3]

theorem isGL3_affOf (x : PG 5 relsN0A8) :
    isGL3 (affOf (n0Perm x)).2 = true := by
  simp only [isGL3, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq]
  intro v hv h0
  have hv8 : v + 1 < 8 := by omega
  have e := n0Perm_apply_val x ⟨v + 1, hv8⟩
  have e0 := n0Perm_apply_val x 0
  simp only [Fin.val_zero, applyC3_zero, Nat.xor_zero] at e0
  rw [h0, Nat.xor_zero, ← e0] at e
  have h1 := (n0Perm x).injective (Fin.ext e)
  rw [Fin.ext_iff] at h1
  simp at h1

theorem avc_mem_allCodes (x : PG 5 relsN0A8) :
    avc x ∈ allCodes := by
  simp only [allCodes, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨(affOf (n0Perm x)).1, affOf_fst_lt _, (affOf (n0Perm x)).2,
    List.mem_filter.2 ⟨mem_allCols3 (affOf_col_lt _), isGL3_affOf x⟩, rfl⟩

theorem allCodes_bitsNodup : bitsNodup 0 allCodes = true := by decide +kernel

theorem allCodes_length : allCodes.length = 1344 := by decide +kernel

theorem exists_avc_eq {c : ℕ} (hc : c ∈ allCodes) :
    ∃ x, avc x = c := by
  classical
  have hnd : allCodes.Nodup := (nodup_of_bitsNodup allCodes_bitsNodup).1
  let f : PG 5 relsN0A8 → allCodes.toFinset := fun x =>
    ⟨avc x, List.mem_toFinset.2 (avc_mem_allCodes x)⟩
  have hf : Function.Injective f := fun x y h => avc_inj (congrArg Subtype.val h)
  have hcard : Nat.card allCodes.toFinset ≤ Nat.card (PG 5 relsN0A8) := by
    rw [card_pg_relsN0A8, Nat.card_eq_fintype_card, Fintype.card_coe,
      List.toFinset_card_of_nodup hnd, allCodes_length]
  have := finite_pg_relsN0A8
  obtain ⟨x, hx⟩ := (hf.bijective_of_nat_card_le hcard).2 ⟨c, List.mem_toFinset.2 hc⟩
  exact ⟨x, congrArg Subtype.val hx⟩

theorem mem_allCodes_of_validC {c : ℕ} (h : validC c = true) : c ∈ allCodes := by
  simp only [validC, Bool.and_eq_true, Nat.blt_eq] at h
  simp only [allCodes, List.mem_flatMap, List.mem_range, List.mem_map]
  refine ⟨c % 8, Nat.mod_lt _ (by norm_num), colsOfCode3 (c / 8),
    List.mem_filter.2 ⟨List.mem_map.2 ⟨c / 8, List.mem_range.2 (by omega), rfl⟩, h.2⟩, ?_⟩
  simp only [affCode, colsOfCode3]
  omega

theorem exists_avc_eq_of_validC {c : ℕ} (h : validC c = true) :
    ∃ x, avc x = c :=
  exists_avc_eq (mem_allCodes_of_validC h)

theorem mul_eq_mul_of_cmul {x y z w : PG 5 relsN0A8}
    (h : cmul (avc x) (avc y) = cmul (avc z) (avc w)) : x * y = z * w :=
  avc_inj (by rw [avc_mul, avc_mul, h])

end CFSG.CGT.A8S.L2
