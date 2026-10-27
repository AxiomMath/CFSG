module

public import CFSG.GF2Type.SmithTypeE.DMod.StabOrbit
public import Certificates.Certificate38800
public import CFSG.GF2Type.SmithTypeE.DMod.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.SmithD6 (wt tvCols applyCols tvImg ea7Bits ea7Diff ea7Pivot ea7I ea7InX ea7Restr)
open CFSG.GF2Type.SmithTypeE.DMod

theorem decode32_xor_eq_sub (a b : ℕ) : decode32 (a ^^^ b) = decode32 a - decode32 b := by
  rw [decode32_xor]
  funext m
  rw [Pi.add_apply, Pi.sub_apply]
  have key : ∀ x y : ZMod 2, x + y = x - y := by decide
  exact key _ _

theorem decode32_eq_one_of_testBit {c : ℕ} {m : Fin 32} (h : c.testBit m.val = true) :
    decode32 c m = 1 := by
  simp [decode32_apply, h]

theorem decode32_eq_zero_of_testBit {c : ℕ} {m : Fin 32} (h : c.testBit m.val = false) :
    decode32 c m = 0 := by
  simp [decode32_apply, h]

theorem vec_eq_sum_two_pow (v : V) : v = ∑ m : Fin 32, v m • decode32 (2 ^ m.val) := by
  funext k
  simp [Finset.sum_apply, decode32_two_pow, Pi.single_apply, mul_ite]

theorem colsLin_eq_self_iff (cols : Array ℕ)
    (hpiv : ∀ m₀ < 32, cols[m₀]! ^^^ 2 ^ m₀ = 0 ∨ ∃ j < 32,
      (cols[m₀]! ^^^ 2 ^ m₀).testBit j = true ∧
        ∀ m < 32, m ≠ m₀ → (cols[m]! ^^^ 2 ^ m).testBit j = false)
    (v : V) :
    colsLin cols v = v ↔ ∀ m : Fin 32, cols[m.val]! ^^^ 2 ^ m.val ≠ 0 → v m = 0 := by
  have hsub : colsLin cols v - v = ∑ m : Fin 32, v m • decode32 (cols[m.val]! ^^^ 2 ^ m.val) := by
    rw [colsLin_apply]
    have h2 : (∑ m : Fin 32, v m • decode32 cols[m.val]!) - v =
        ∑ m : Fin 32, v m • (decode32 cols[m.val]! - decode32 (2 ^ m.val)) := by
      simp only [smul_sub, Finset.sum_sub_distrib]
      rw [← vec_eq_sum_two_pow v]
    rw [h2]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [decode32_xor_eq_sub]
  rw [← sub_eq_zero, hsub]
  constructor
  · intro h m hm
    rcases hpiv m.val m.isLt with h0 | ⟨j, hj, hjt, hother⟩
    · exact absurd h0 hm
    · have hcoord := congrFun h (⟨j, hj⟩ : Fin 32)
      rw [Finset.sum_apply, Finset.sum_eq_single m, Pi.zero_apply] at hcoord
      · rw [Pi.smul_apply, smul_eq_mul, decode32_eq_one_of_testBit (m := ⟨j, hj⟩) hjt,
          mul_one] at hcoord
        exact hcoord
      · intro m' _ hm'
        have hne : m'.val ≠ m.val := fun e => hm' (Fin.ext e)
        rw [Pi.smul_apply, decode32_eq_zero_of_testBit (m := ⟨j, hj⟩)
          (hother m'.val m'.isLt hne), smul_zero]
      · intro hnot
        exact absurd (Finset.mem_univ m) hnot
  · intro h
    apply Finset.sum_eq_zero
    intro m _
    by_cases hd : cols[m.val]! ^^^ 2 ^ m.val = 0
    · rw [hd, decode32_zero, smul_zero]
    · rw [h m hd, zero_smul]

section Checks


theorem ea7ColsCheck_holds : CFSG.SmithD6.ea7ChkCols = true :=
  Certificates.certificate38800.1

theorem ea7BitsCheck_holds : CFSG.SmithD6.ea7ChkBits = true :=
  Certificates.certificate38800.2.1

theorem ea7WCheck_holds : CFSG.SmithD6.ea7ChkW = true :=
  Certificates.certificate38800.2.2.1

theorem ea7F4Check_holds : CFSG.SmithD6.ea7ChkF4 = true :=
  Certificates.certificate38800.2.2.2

end Checks

@[expose] def C16 : Submodule (ZMod 2) V where
  carrier := {v | ∀ m : Fin 32, m.val ∉ ea7Bits → v m = 0}
  add_mem' := fun {a b} ha hb m hm => by
    simp only [Pi.add_apply, ha m hm, hb m hm, add_zero]
  zero_mem' := fun m _ => rfl
  smul_mem' := fun c v hv m hm => by
    simp only [Pi.smul_apply, hv m hm, smul_zero]

theorem mem_C16 {v : V} : v ∈ C16 ↔ ∀ m : Fin 32, m.val ∉ ea7Bits → v m = 0 := Iff.rfl

theorem C16_le {N : Submodule (ZMod 2) V}
    (h : ∀ m : Fin 32, m.val ∈ ea7Bits → decode32 (2 ^ m.val) ∈ N) : C16 ≤ N := by
  intro v hv
  have hsum : v = ∑ m : Fin 32, v m • (Pi.single m (1 : ZMod 2) : V) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hsum]
  refine N.sum_mem fun m _ => ?_
  by_cases hm : m.val ∈ ea7Bits
  · rw [← decode32_two_pow]
    exact N.smul_mem _ (h m hm)
  · rw [hv m hm, zero_smul]
    exact N.zero_mem

theorem decode32_two_pow_mem_C16 {m : Fin 32} (hm : m.val ∈ ea7Bits) :
    decode32 (2 ^ m.val) ∈ C16 := by
  rw [decode32_two_pow]
  intro j hj
  rw [Pi.single_apply, if_neg]
  rintro rfl
  exact hj hm

theorem fin_val_zero : ((0 : Fin 365211) : ℕ) = 0 := rfl

section StdOpp


theorem stdOpp_val : stdOpp.val = 31899 := by
  have e1 := (lineFacts.entry stdOpp.val stdOpp.2).2.2.2.2.2.2.2
  have e2 := (lineFacts.entry 31899 (by norm_num)).2.2.2.2.2.2.2
  rw [linePair_stdOpp] at e1
  rw [stabOrd_unpack.2.1] at e2
  exact e1.symm.trans e2

end StdOpp

section Cols


theorem tvEquiv_eq_self_iff {k : ℕ} (hk : k < 365211) (hp : ea7Pivot k = true) (v : V) :
    tvEquiv k v = v ↔ ∀ m : Fin 32, ea7Diff k m.val ≠ 0 → v m = 0 := by
  rw [tvEquiv_apply hk]
  refine colsLin_eq_self_iff (tvCols k) ?_ v
  simp only [ea7Pivot, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true', ea7Diff] at hp
  intro m₀ hm₀
  rcases hp m₀ hm₀ with h | ⟨j, hj, ⟨h1, h2⟩⟩
  · exact Or.inl h
  · refine Or.inr ⟨j, hj, h1, fun m hm hne => ?_⟩
    have := h2 m hm
    simpa [hne] using this

end Cols

section Fixed


theorem mem_ea7Bits_iff {m : ℕ} (hm : m < 32) :
    m ∈ ea7Bits ↔ ea7Diff 0 m = 0 ∧ ea7Diff 31899 m = 0 := by
  have h := ea7BitsCheck_holds
  simp only [CFSG.SmithD6.ea7ChkBits, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have h1 := h m hm
  have h2 : List.elem m ea7Bits = (ea7Diff 0 m == 0 && ea7Diff 31899 m == 0) := h1
  rw [← List.elem_iff, h2]
  simp only [Bool.and_eq_true, beq_iff_eq]

theorem mem_C16_iff (v : V) :
    v ∈ C16 ↔ tvEquiv 0 v = v ∧ tvEquiv stdOpp.val v = v := by
  have hp := ea7ColsCheck_holds
  simp only [CFSG.SmithD6.ea7ChkCols, Bool.and_eq_true] at hp
  rw [stdOpp_val, tvEquiv_eq_self_iff (by norm_num) hp.1,
    tvEquiv_eq_self_iff (by norm_num) hp.2, mem_C16]
  constructor
  · intro hv
    exact ⟨fun m hm => hv m fun hmem => hm ((mem_ea7Bits_iff m.2).mp hmem).1,
      fun m hm => hv m fun hmem => hm ((mem_ea7Bits_iff m.2).mp hmem).2⟩
  · rintro ⟨h0, h1⟩ m hm
    by_cases hd0 : ea7Diff 0 m.val = 0
    · exact h1 m fun hd1 => hm ((mem_ea7Bits_iff m.2).mpr ⟨hd0, hd1⟩)
    · exact h0 m hd0

end Fixed

theorem exists_wt_eq_two_pow {m : ℕ} (hm : m ∈ ea7Bits) :
    ∃ i < 75735, wt i = 2 ^ m := by
  have h := ea7WCheck_holds
  simp only [CFSG.SmithD6.ea7ChkW, List.all_eq_true, List.any_eq_true, List.mem_range,
    beq_iff_eq] at h
  exact h m hm

section Comm


theorem commute_of_tvImg_eq {a b : Fin 365211} (h : tvImg a.val b.val = b.val) :
    Commute (tvP a) (tvP b) := by
  have h1 := mul_tvP_mul_inv (tvP_mem a) b
  rw [show tvP a b = b from Fin.ext (by rw [tvP_apply]; exact h)] at h1
  exact mul_inv_eq_iff_eq_mul.mp h1

theorem ea7InX_iff {p : Fin 365211} :
    ea7InX p.val = true ↔ Commute (tvP p) (tvP 0) ∧ Commute (tvP p) (tvP stdOpp) := by
  constructor
  · intro h
    simp only [CFSG.SmithD6.ea7InX, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    refine ⟨commute_of_tvImg_eq (a := p) (b := 0) (by rw [fin_val_zero]; exact h.1.2),
      commute_of_tvImg_eq (a := p) (b := stdOpp) (by rw [stdOpp_val]; exact h.2)⟩
  · rintro ⟨h0, h1⟩
    have e0 := tvImg_eq_of_commute (a := p) (b := 0) h0.eq
    have e1 := tvImg_eq_of_commute (a := p) (b := stdOpp) h1.eq
    rw [fin_val_zero] at e0
    rw [stdOpp_val] at e1
    simp only [CFSG.SmithD6.ea7InX, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨p.2, e0⟩, e1⟩

end Comm

theorem mem_ea7I_iff {p : ℕ} : p ∈ ea7I ↔ p < 365211 ∧ ea7InX p = true := by
  simp only [ea7I, List.mem_filter, List.mem_range]

section Restr


theorem applyCols_tvCols_lt (k c : ℕ) : applyCols (tvCols k) c < 2 ^ 32 :=
  applyCols_lt (size_tvCols k) (fun _ hc => tvCols_lt k hc) c

theorem eq_of_restr_C16 {p s : Fin 365211} (hp : ea7InX p.val = true) (hs : ea7InX s.val = true)
    (h : ∀ v ∈ C16, tvEquiv p.val v = tvEquiv s.val v) : p = s := by
  by_contra hne
  have hF := ea7F4Check_holds
  simp only [CFSG.SmithD6.ea7ChkF4, List.all_eq_true, List.mem_map, Bool.or_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hF
  rcases hF p.val (mem_ea7I_iff.mpr ⟨p.2, hp⟩) s.val (mem_ea7I_iff.mpr ⟨s.2, hs⟩) with h1 | h1
  · exact hne (Fin.ext h1)
  · apply h1
    simp only [ea7Restr]
    refine List.map_congr_left fun m hm => ?_
    have hm32 : m < 32 := (by decide : ∀ x ∈ ea7Bits, x < 32) m hm
    have e := h _ (decode32_two_pow_mem_C16 (m := ⟨m, hm32⟩) hm)
    rw [tvEquiv_decode p.2, tvEquiv_decode s.2] at e
    exact eq_of_decode32_eq (applyCols_tvCols_lt _ _) (applyCols_tvCols_lt _ _) e

end Restr

end CFSG.GF2Type.SmithTypeE.E7
