
module

public import CFSG.Certificates.Kernel.Th.Max3S.LeafFacts
public import CFSG.Certificates.Kernel.Th.Spec.Big

@[expose] public section

namespace CFSG.KC.Th.Max3S

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.KC.Th.Spec

theorem prod_ofFn_eq_one {M : Type} [Monoid M] :
    ∀ {n : ℕ} (f : Fin n → M), (∀ i, f i = 1) → (List.ofFn f).prod = 1
  | 0, _, _ => by rw [List.ofFn_zero, List.prod_nil]
  | _ + 1, f, hf => by
    rw [List.ofFn_succ, List.prod_cons, hf 0, prod_ofFn_eq_one _ fun i => hf i.succ, one_mul]

theorem prod_ofFn_top {M : Type} [Monoid M] :
    ∀ {n : ℕ} (f g : Fin n → M) (m : Fin n) (a : M), (∀ i, i < m → f i = g i) → f m = a →
      g m = 1 → (∀ i, m < i → f i = 1 ∧ g i = 1) →
      (List.ofFn f).prod = (List.ofFn g).prod * a
  | 0, _, _, m, _, _, _, _, _ => m.elim0
  | n + 1, f, g, m, a, hlt, hm, hg, hgt => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    cases m using Fin.cases with
    | zero =>
      rw [prod_ofFn_eq_one _ fun i => (hgt i.succ (Fin.succ_pos i)).1,
        prod_ofFn_eq_one _ fun i => (hgt i.succ (Fin.succ_pos i)).2, hm, hg]
      simp
    | succ m =>
      rw [hlt 0 (Fin.succ_pos m), mul_assoc]
      congr 1
      refine prod_ofFn_top _ _ m a (fun i hi => hlt i.succ (Fin.succ_lt_succ_iff.2 hi)) hm hg
        fun i hi => hgt i.succ (Fin.succ_lt_succ_iff.2 hi)

def bitsOK (k : ℕ) : Bool :=
  decide (1 ≤ hbit k) && decide (hbit k ≤ 8) && decide (k - 2 ^ hbit k < k) &&
    decide (k % 2 = (k - 2 ^ hbit k) % 2) &&
    (List.range 8).all (fun i => !decide (i + 1 < hbit k) ||
      decide (k / 2 ^ (i + 1) % 2 = (k - 2 ^ hbit k) / 2 ^ (i + 1) % 2)) &&
    decide (k / 2 ^ hbit k % 2 = 1) && decide ((k - 2 ^ hbit k) / 2 ^ hbit k % 2 = 0) &&
    (List.range 8).all (fun i => !decide (hbit k < i + 1) ||
      (decide (k / 2 ^ (i + 1) % 2 = 0) && decide ((k - 2 ^ hbit k) / 2 ^ (i + 1) % 2 = 0)))

set_option maxRecDepth 100000 in
theorem bitsOK_all : (List.range 512).all (fun k => !decide (2 ≤ k) || bitsOK k) = true := by
  decide +kernel

theorem nfBits (k : Fin 512) (hk : 2 ≤ k.val) :
    1 ≤ hbit k.val ∧ hbit k.val ≤ 8 ∧ k.val - 2 ^ hbit k.val < k.val ∧
      k.val % 2 = (k.val - 2 ^ hbit k.val) % 2 ∧
      (∀ i : Fin 8, i.val + 1 < hbit k.val →
        k.val / 2 ^ (i.val + 1) % 2 = (k.val - 2 ^ hbit k.val) / 2 ^ (i.val + 1) % 2) ∧
      k.val / 2 ^ hbit k.val % 2 = 1 ∧ (k.val - 2 ^ hbit k.val) / 2 ^ hbit k.val % 2 = 0 ∧
      (∀ i : Fin 8, hbit k.val < i.val + 1 →
        k.val / 2 ^ (i.val + 1) % 2 = 0 ∧ (k.val - 2 ^ hbit k.val) / 2 ^ (i.val + 1) % 2 = 0) := by
  have h := List.all_eq_true.1 bitsOK_all k.val (List.mem_range.2 k.isLt)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_le] at h
  have hb : bitsOK k.val = true := h.resolve_left (by omega)
  simp only [bitsOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hb
  refine ⟨h1, h2, h3, h4, fun i hi => ?_, h6, h7, fun i hi => ?_⟩
  · exact (h5 i.val i.isLt).resolve_left (not_not.2 hi)
  · exact (h8 i.val i.isLt).resolve_left (not_not.2 hi)

section Nf

variable {A B : Array V4}

end Nf

variable {D : CFSG.KC.Th.Gen.Max3Data}

theorem segPre_length : (segPre D).length = 33 := rfl

theorem segPost_length : (segPost D).length = 22 := rfl

theorem segPre_true (h : CFSG.KC.Th.Gen.max3Chk D = true) (i : ℕ) (hi : i < (segPre D).length) :
    (segPre D)[i] = true :=
  leaves_true D h _ (mem_leaves_segPre (List.getElem_mem hi))

theorem mem_leaves_segPost {b : Bool} (hb : b ∈ segPost D) : b ∈ leaves D := by
  rw [leaves]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hb))))))))

theorem segPost_true (h : CFSG.KC.Th.Gen.max3Chk D = true) (i : ℕ) (hi : i < (segPost D).length) :
    (segPost D)[i] = true :=
  leaves_true D h _ (mem_leaves_segPost (List.getElem_mem hi))

end CFSG.KC.Th.Max3S

end
