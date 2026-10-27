module

public import CFSG.LieType.Steinberg.Minuscule.Ops
public import CFSG.LieType.Steinberg.Basic
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115

public noncomputable section

namespace CFSG.LieType.Steinberg.Minuscule

open CFSG.Blueprint.Chevalley

namespace MinData

variable {τ : Tag} (D : MinData τ)

@[expose] def checkExtra : Bool :=
  decide (D.d ≤ 127) && D.weights.all (fun w => decide (w < 4 ^ τ.rank)) &&
    D.ops.all fun M => (List.range D.d).all fun a =>
      dig M a == 0 || (decide (2 ≤ dig M a) && decide (dig M a / 2 - 1 < D.d))

structure Valid : Prop where
  check : D.check = true
  extra : D.checkExtra = true

@[expose] def deg (a : ℕ) : ℤ := ∑ i : Fin τ.rank, D.grading.getD i 0 * D.wt a i

theorem toWeight_add (x y : Fin τ.rank → ℤ) : toWeight (x + y) = toWeight x + toWeight y := by
  ext j
  simp [toWeight, mul_add, Finset.sum_add_distrib]

theorem toWeight_neg (x : Fin τ.rank → ℤ) : toWeight (-x) = -toWeight x := by
  ext j
  simp [toWeight]

theorem toWeight_smul (c : ℤ) (x : Fin τ.rank → ℤ) : toWeight (c • x) = c • toWeight x := by
  ext j
  simp [toWeight, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem toWeight_sub (x y : Fin τ.rank → ℤ) : toWeight (x - y) = toWeight x - toWeight y := by
  rw [sub_eq_add_neg, toWeight_add, toWeight_neg, ← sub_eq_add_neg]

theorem toWeight_single (i j : Fin τ.rank) : toWeight (Pi.single i 1) j = τ.cartan j i := by
  simp [toWeight, Pi.single_apply]

theorem toWeight_apply (γ : Fin τ.rank → ℤ) (i : Fin τ.rank) :
    toWeight γ i = ∑ j, τ.cartan i j * γ j := rfl

theorem reflect_eq (i : Fin τ.rank) (γ : Fin τ.rank → ℤ) :
    reflect τ i γ = γ - toWeight γ i • Pi.single i 1 := rfl

theorem reflectWeight_apply_self (i : Fin τ.rank) (μ : Fin τ.rank → ℤ) :
    reflectWeight i μ i = -μ i := by
  simp only [reflectWeight, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, toWeight_single,
    Tag.cartan_self]
  ring

theorem reflectWeight_reflectWeight (i : Fin τ.rank) (μ : Fin τ.rank → ℤ) :
    reflectWeight i (reflectWeight i μ) = μ := by
  rw [reflectWeight, reflectWeight_apply_self, reflectWeight]
  ext j
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem reflectWeight_add (i : Fin τ.rank) (μ ν : Fin τ.rank → ℤ) :
    reflectWeight i (μ + ν) = reflectWeight i μ + reflectWeight i ν := by
  ext j
  simp only [reflectWeight, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem toWeight_reflect (i : Fin τ.rank) (γ : Fin τ.rank → ℤ) :
    toWeight (reflect τ i γ) = reflectWeight i (toWeight γ) := by
  rw [reflect_eq, toWeight_sub, toWeight_smul, reflectWeight]

theorem reflectWeight_eq_add_of_eq_neg_one {i : Fin τ.rank} {μ : Fin τ.rank → ℤ}
    (h : μ i = -1) : reflectWeight i μ = μ + toWeight (Pi.single i 1) := by
  rw [reflectWeight, h, neg_one_smul, sub_neg_eq_add]

theorem reflectWeight_eq_sub_of_eq_one {i : Fin τ.rank} {μ : Fin τ.rank → ℤ}
    (h : μ i = 1) : reflectWeight i μ = μ + toWeight (-Pi.single i 1) := by
  rw [reflectWeight, h, one_smul, toWeight_neg, sub_eq_add_neg]

theorem reflectWeight_eq_self_of_eq_zero {i : Fin τ.rank} {μ : Fin τ.rank → ℤ}
    (h : μ i = 0) : reflectWeight i μ = μ := by
  rw [reflectWeight, h, zero_smul, sub_zero]

theorem eq_of_digits_eq {b : ℕ} (hb : 0 < b) :
    ∀ {n x y : ℕ}, x < b ^ n → y < b ^ n → (∀ i < n, x / b ^ i % b = y / b ^ i % b) → x = y
  | 0, x, y, hx, hy, _ => by rw [pow_zero] at hx hy; omega
  | n + 1, x, y, hx, hy, h => by
    have h0 := h 0 (by omega)
    simp only [pow_zero, Nat.div_one] at h0
    have hrec : x / b = y / b := by
      refine eq_of_digits_eq hb (n := n) ?_ ?_ fun i hi => ?_
      · rw [Nat.div_lt_iff_lt_mul hb, ← pow_succ]; exact hx
      · rw [Nat.div_lt_iff_lt_mul hb, ← pow_succ]; exact hy
      · have := h (i + 1) (by omega)
        rwa [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at this
    rw [← Nat.div_add_mod x b, ← Nat.div_add_mod y b, hrec, h0]

theorem root_injOn {k l : ℕ} (hk : k < τ.rootCertificate.roots.length)
    (hl : l < τ.rootCertificate.roots.length)
    (h : τ.rootCertificate.root k = τ.rootCertificate.root l) : k = l := by
  have hn := τ.rootCertificate_checkNodup
  simp only [RootCertificate.checkNodup, decide_eq_true_eq] at hn
  exact List.inj_on_of_nodup_map hn (List.mem_range.2 hk) (List.mem_range.2 hl)
    (congrArg List.ofFn h)

theorem certificate_and :
    (τ.rank ≤ τ.rootCertificate.roots.length ∧
      ∀ j : Fin τ.rank, τ.rootCertificate.root j = Pi.single j 1) ∧
    ∀ k < τ.rootCertificate.roots.length, ∀ i : Fin τ.rank,
      τ.rootCertificate.image k i < τ.rootCertificate.roots.length ∧
        τ.rootCertificate.root (τ.rootCertificate.image k i) =
          reflect τ i (τ.rootCertificate.root k) := by
  have h := τ.rootCertificate_check
  simp only [RootCertificate.check, RootCertificate.checkBasis, RootCertificate.checkTable,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange, List.mem_range,
    true_implies] at h
  exact ⟨⟨h.1.1.1, fun j => RootCertificate.eq_of_ofFn_beq (h.1.1.2 j)⟩,
    fun k hk i => ⟨(h.2 k hk i).1, RootCertificate.eq_of_ofFn_beq (h.2 k hk i).2⟩⟩

theorem rank_le_length : τ.rank ≤ τ.rootCertificate.roots.length := certificate_and.1.1

theorem root_basis (j : Fin τ.rank) : τ.rootCertificate.root j = Pi.single j 1 :=
  certificate_and.1.2 j

theorem image_lt {k : ℕ} (hk : k < τ.rootCertificate.roots.length) (i : Fin τ.rank) :
    τ.rootCertificate.image k i < τ.rootCertificate.roots.length :=
  (certificate_and.2 k hk i).1

theorem root_image {k : ℕ} (hk : k < τ.rootCertificate.roots.length) (i : Fin τ.rank) :
    τ.rootCertificate.root (τ.rootCertificate.image k i) =
      reflect τ i (τ.rootCertificate.root k) :=
  (certificate_and.2 k hk i).2

theorem root_image_self (i : Fin τ.rank) :
    τ.rootCertificate.root (τ.rootCertificate.image i i) = -Pi.single i 1 := by
  rw [root_image (lt_of_lt_of_le i.2 rank_le_length), root_basis, reflect_single_self]

namespace Valid

variable {D} (hV : D.Valid)
include hV

theorem check_and :
    D.checkWeights = true ∧ D.checkWeylTable = true ∧ D.checkSimple = true ∧
      D.checkWeyl = true ∧ D.checkPairs = true ∧ D.checkBraid = true ∧ D.checkPGen = true ∧
        D.checkGrading = true := by
  have h := hV.check
  simp only [MinData.check, Bool.and_eq_true] at h
  tauto

theorem extra_and :
    D.d ≤ 127 ∧ (∀ w ∈ D.weights, w < 4 ^ τ.rank) ∧
      ∀ M ∈ D.ops, ∀ a < D.d, dig M a = 0 ∨ 2 ≤ dig M a ∧ dig M a / 2 - 1 < D.d := by
  have h := hV.extra
  simp only [checkExtra, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem d_le : D.d ≤ 127 := hV.extra_and.1

theorem wf_op (k : ℕ) : WF D.d (D.op k) := by
  intro a ha
  unfold op
  by_cases hk : k < D.ops.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact hV.extra_and.2.2 _ (List.getElem_mem hk) a ha
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Or.inl (by simp [dig])

theorem weights_and :
    D.weights.length = D.d ∧ D.weights.Nodup ∧
      ∀ w ∈ D.weights, ∀ i : Fin τ.rank, w / 4 ^ (i : ℕ) % 4 < 3 := by
  have h := hV.check_and.1
  simp only [checkWeights, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_finRange,
    true_implies, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem weights_length : D.weights.length = D.d := hV.weights_and.1

theorem weight_mem (a : Fin D.d) : D.weights.getD a 0 ∈ D.weights := by
  rw [List.getD_eq_getElem _ _ (by rw [hV.weights_length]; exact a.2)]
  exact List.getElem_mem _

theorem wt_mem (a : Fin D.d) (i : Fin τ.rank) : D.wt a i = -1 ∨ D.wt a i = 0 ∨ D.wt a i = 1 := by
  have := hV.weights_and.2.2 _ (hV.weight_mem a) i
  simp only [wt]
  omega

theorem wt_injective : Function.Injective fun a : Fin D.d => D.wt a := by
  intro a b h
  have hab : D.weights.getD a 0 = D.weights.getD b 0 := by
    refine eq_of_digits_eq (by norm_num) (hV.extra_and.2.1 _ (hV.weight_mem a))
      (hV.extra_and.2.1 _ (hV.weight_mem b)) fun i hi => ?_
    have := congrFun h ⟨i, hi⟩
    simp only [wt] at this
    omega
  have ha : (a : ℕ) < D.weights.length := by rw [hV.weights_length]; exact a.2
  have hb : (b : ℕ) < D.weights.length := by rw [hV.weights_length]; exact b.2
  rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb,
    hV.weights_and.2.1.getElem_inj_iff] at hab
  exact Fin.ext hab

theorem wt_inj {a b : Fin D.d} : D.wt a = D.wt b ↔ a = b :=
  ⟨fun h => hV.wt_injective h, fun h => h ▸ rfl⟩

theorem weylTable_and (a : Fin D.d) (i : Fin τ.rank) :
    D.weyl a i < D.d ∧ D.wt (D.weyl a i) = reflectWeight i (D.wt a) := by
  have h := hV.check_and.2.1
  simp only [checkWeylTable, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    List.mem_finRange, true_implies, decide_eq_true_eq] at h
  exact ⟨(h.2 a a.2 i).1, List.ofFn_injective (h.2 a a.2 i).2⟩

def sRefl (i : Fin τ.rank) (a : Fin D.d) : Fin D.d := ⟨D.weyl a i, (hV.weylTable_and a i).1⟩

theorem sRefl_val (i : Fin τ.rank) (a : Fin D.d) : (hV.sRefl i a : ℕ) = D.weyl a i := (rfl)

theorem weyl_lt {b : ℕ} (hb : b < D.d) (i : Fin τ.rank) : D.weyl b i < D.d :=
  (hV.weylTable_and ⟨b, hb⟩ i).1

theorem wt_sRefl (i : Fin τ.rank) (a : Fin D.d) :
    D.wt (hV.sRefl i a) = reflectWeight i (D.wt a) :=
  (hV.weylTable_and a i).2

theorem sRefl_sRefl (i : Fin τ.rank) (a : Fin D.d) : hV.sRefl i (hV.sRefl i a) = a :=
  hV.wt_injective (by simp only [wt_sRefl, reflectWeight_reflectWeight])

theorem sRefl_injective (i : Fin τ.rank) : Function.Injective (hV.sRefl i) :=
  fun a b h => by rw [← hV.sRefl_sRefl i a, h, hV.sRefl_sRefl]

theorem wt_sRefl_self (i : Fin τ.rank) (a : Fin D.d) :
    D.wt (hV.sRefl i a) i = -D.wt a i := by
  rw [wt_sRefl, reflectWeight_apply_self]

theorem sRefl_eq_self {i : Fin τ.rank} {a : Fin D.d} (h : D.wt a i = 0) : hV.sRefl i a = a :=
  hV.wt_injective (by simp only [wt_sRefl, reflectWeight_eq_self_of_eq_zero h])

theorem sRefl_ne_self {i : Fin τ.rank} {a : Fin D.d} (h : D.wt a i ≠ 0) : hV.sRefl i a ≠ a := by
  intro h'
  have := hV.wt_sRefl_self i a
  rw [h'] at this
  omega

theorem simple_and :
    D.ops.length = τ.rootCertificate.roots.length ∧ ∀ i : Fin τ.rank,
      (D.op i = D.simpleE i ∧ D.op (τ.rootCertificate.image i i) = D.simpleF i) ∧
        D.simpleE i ≠ 0 := by
  have h := hV.check_and.2.2.1
  simp only [checkSimple, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq,
    Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

theorem op_single (i : Fin τ.rank) : D.op i = D.simpleE i := (hV.simple_and.2 i).1.1

theorem op_image_self (i : Fin τ.rank) : D.op (τ.rootCertificate.image i i) = D.simpleF i :=
  (hV.simple_and.2 i).1.2

theorem simpleE_ne_zero (i : Fin τ.rank) : D.simpleE i ≠ 0 := (hV.simple_and.2 i).2

theorem conj_op {k : ℕ} (hk : k < τ.rootCertificate.roots.length) (i : Fin τ.rank) :
    conj D.d (D.weylOp i) (D.op k) =
      if D.signs.getD k 0 / 2 ^ (i : ℕ) % 2 = 1 then neg D.d (D.op (τ.rootCertificate.image k i))
      else D.op (τ.rootCertificate.image k i) := by
  have h := hV.check_and.2.2.2.1
  simp only [checkWeyl, List.all_eq_true, List.mem_range, List.mem_finRange, true_implies,
    beq_iff_eq] at h
  exact h k hk i

theorem pairs {l : ℕ} (hl : l < τ.rootCertificate.roots.length) (j : Fin τ.rank) :
    τ.rootCertificate.root l = -Pi.single j 1 ∨
      (¬ IsRoot τ (Pi.single j 1 + τ.rootCertificate.root l) ∧
        comp D.d (D.op j) (D.op l) = comp D.d (D.op l) (D.op j)) ∨
      ∃ m < τ.rootCertificate.roots.length,
        τ.rootCertificate.root m = Pi.single j 1 + τ.rootCertificate.root l ∧
        disjointDom D.d (comp D.d (D.op j) (D.op l)) (comp D.d (D.op l) (D.op j)) = true ∧
        (union D.d (comp D.d (D.op j) (D.op l)) (neg D.d (comp D.d (D.op l) (D.op j))) = D.op m ∨
          union D.d (comp D.d (D.op j) (D.op l)) (neg D.d (comp D.d (D.op l) (D.op j))) =
            neg D.d (D.op m)) ∧
        comp D.d (comp D.d (D.op j) (D.op l)) (D.op j) = 0 ∧
        comp D.d (comp D.d (D.op l) (D.op j)) (D.op l) = 0 := by
  have h := hV.check_and.2.2.2.2.1
  simp only [checkPairs, List.all_eq_true, List.mem_range, List.mem_finRange,
    true_implies] at h
  have h := h l hl j
  split_ifs at h with hc hs
  · simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl (List.ofFn_injective h)
    · refine Or.inr (Or.inl ⟨fun hr => ?_, h2⟩)
      rw [(StringData.memDec_iff τ.rootCertificate_check τ.stringData_check).2 hr] at h1
      exact absurd h1 (by simp)
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact Or.inr (Or.inr ⟨_, h.1.1.1.1.1, List.ofFn_injective h.1.1.1.1.2, h.1.1.1.2,
      Or.inr h.1.1.2, h.1.2, h.2⟩)
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact Or.inr (Or.inr ⟨_, h.1.1.1.1.1, List.ofFn_injective h.1.1.1.1.2, h.1.1.1.2,
      Or.inl h.1.1.2, h.1.2, h.2⟩)

theorem braid {i j : Fin τ.rank} (hij : i ≠ j) :
    (τ.cartan i j = 0 ∧
        comp D.d (D.weylOp i) (D.weylOp j) = comp D.d (D.weylOp j) (D.weylOp i)) ∨
      (τ.cartan i j * τ.cartan j i = 1 ∧
        comp D.d (D.weylOp i) (comp D.d (D.weylOp j) (D.weylOp i)) =
          comp D.d (D.weylOp j) (comp D.d (D.weylOp i) (D.weylOp j))) := by
  have h := hV.check_and.2.2.2.2.2.1
  simp only [checkBraid, List.all_eq_true, List.mem_finRange, true_implies] at h
  have h := h i j
  simp only [Bool.or_eq_true, decide_eq_true_eq, hij, false_or] at h
  split_ifs at h with hc
  · simp only [beq_iff_eq] at h
    exact Or.inl ⟨hc, h⟩
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact Or.inr h

theorem pgen_and :
    D.pgen.length = τ.rank ∧ ∀ i : Fin τ.rank, (∀ p ∈ D.pgen.getD i [], p.1 < D.d) ∧
      List.ofFn ((D.pgen.getD i []).map fun p => p.2 • D.wt p.1).sum =
        List.ofFn (Pi.single i 1 : Fin τ.rank → ℤ) := by
  have h := hV.check_and.2.2.2.2.2.2.1
  simp only [checkPGen, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq,
    Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

theorem pgen_lt (i : Fin τ.rank) : ∀ p ∈ D.pgen.getD i [], p.1 < D.d := (hV.pgen_and.2 i).1

theorem pgen_sum (i : Fin τ.rank) :
    ((D.pgen.getD i []).map fun p => p.2 • D.wt p.1).sum = Pi.single i 1 :=
  List.ofFn_injective (hV.pgen_and.2 i).2

theorem grading_and :
    (0 < D.scale ∧ D.grading.length = τ.rank) ∧ ∀ j : Fin τ.rank,
      ∑ i : Fin τ.rank, D.grading.getD i 0 * toWeight (Pi.single j 1) i = D.scale := by
  have h := hV.check_and.2.2.2.2.2.2.2
  simp only [checkGrading, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq,
    Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

theorem scale_pos : 0 < D.scale := hV.grading_and.1.1

theorem grading_sum (j : Fin τ.rank) :
    ∑ i : Fin τ.rank, D.grading.getD i 0 * toWeight (Pi.single j 1) i = D.scale :=
  hV.grading_and.2 j

theorem deg_eq_add {a b : ℕ} {γ : Fin τ.rank → ℤ} (h : D.wt b = D.wt a + toWeight γ) :
    D.deg b = D.deg a + D.scale * ht γ := by
  have key : ∑ i : Fin τ.rank, D.grading.getD i 0 * toWeight γ i = D.scale * ht γ := by
    simp only [toWeight_apply, Finset.mul_sum, ht]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := hV.grading_sum j
    simp only [toWeight_single] at this
    rw [← this, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [deg, h, Pi.add_apply, mul_add, Finset.sum_add_distrib, key]

end Valid

end MinData

end CFSG.LieType.Steinberg.Minuscule
