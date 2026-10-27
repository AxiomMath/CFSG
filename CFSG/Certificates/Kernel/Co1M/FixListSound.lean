
module

public import Certificates.Data.Kernel.Co1FixList
public import CFSG.Certificates.Kernel.Co1FixCount

public section

namespace CFSG.KC.Co1Fix

open CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native Matrix

theorem collectBelow_eq (p : Nat → Bool) : ∀ (n : Nat) (acc : List Nat),
    CFSG.Sporadic.Co1.OddNative.collectBelow p n acc = (List.range n).filter p ++ acc
  | 0, acc => rfl
  | n + 1, acc => by
    rw [CFSG.Sporadic.Co1.OddNative.collectBelow, collectBelow_eq p n, List.range_succ,
      List.filter_append]
    cases h : p n <;> simp [h]

theorem strictInc_pairwise : ∀ L : List Nat,
    CFSG.Sporadic.Co1.OddNative.strictInc L = true → L.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: t, h => by
    simp only [CFSG.Sporadic.Co1.OddNative.strictInc, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := strictInc_pairwise (b :: t) h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact h.1.trans (List.rel_of_pairwise_cons ih hc)

theorem spanK_lt : ∀ (F : List Nat), (∀ f ∈ F, f < 2 ^ 24) → ∀ acc < 2 ^ 24,
    ∀ y ∈ spanK F acc, y < 2 ^ 24
  | [], _, acc, hacc, y, hy => by
    rw [spanK, List.mem_singleton] at hy
    rw [hy]; exact hacc
  | f :: F, hF, acc, hacc, y, hy => by
    have hF' : ∀ g ∈ F, g < 2 ^ 24 := fun g hg => hF g (List.mem_cons_of_mem _ hg)
    rw [spanK, List.mem_append] at hy
    rcases hy with hy | hy
    · exact spanK_lt F hF' acc hacc y hy
    · exact spanK_lt F hF' _ (Nat.xor_lt_two_pow hacc (hF f List.mem_cons_self)) y hy

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem spanK_comb : ∀ (F : List Nat) (n : Nat), F.length = n → (∀ f ∈ F, f < 2 ^ 24) →
    ∀ acc < 2 ^ 24, ∀ c : Fin n → ZMod 2, ∃ y ∈ spanK F acc, vecOf acc + comb F n c = vecOf y
  | [], n, hn, _, acc, _, c => by
    subst hn
    refine ⟨acc, List.mem_singleton_self _, ?_⟩
    simp [comb]
  | f :: F, n, hn, hF, acc, hacc, c => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨F.length, by rw [← hn]; rfl⟩
    have hm : F.length = m := by simpa using hn
    have hf : f < 2 ^ 24 := hF f List.mem_cons_self
    have hF' : ∀ g ∈ F, g < 2 ^ 24 := fun g hg => hF g (List.mem_cons_of_mem _ hg)
    rw [comb_cons]
    rcases zmod2_cases (c 0) with h0 | h0
    · obtain ⟨y, hy, e⟩ := spanK_comb F m hm hF' acc hacc (fun i => c i.succ)
      refine ⟨y, by rw [spanK]; exact List.mem_append_left _ hy, ?_⟩
      rw [h0, zero_smul', zero_add, e]
    · obtain ⟨y, hy, e⟩ := spanK_comb F m hm hF' (acc ^^^ f) (Nat.xor_lt_two_pow hacc hf)
        (fun i => c i.succ)
      refine ⟨y, by rw [spanK]; exact List.mem_append_right _ hy, ?_⟩
      rw [h0, one_smul', ← add_assoc, ← e, vecOf, vecOf, vecOf, toVecD_xor]

theorem isFixed_unpackR (T x : Nat) :
    CFSG.Sporadic.Co1.OddNative.isFixedN (unpackR 24 T) x = (vmF 24 T x == x) := by
  rw [CFSG.Sporadic.Co1.OddNative.isFixedN, CFSG.KC.F2W.vecMulN_unpackR]

theorem fixList_eq_of {TA TB Qt k a b : Nat} {F Y W : List Nat}
    (h1 : fixK 24 TA Qt F Y k a b = true) (h2 : fixListK TA TB F W = true) :
    CFSG.Sporadic.Co1.OddNative.fixList [unpackR 24 TA, unpackR 24 TB] = W := by
  obtain ⟨hk, hlen, -, hF, hpF, hpY, -⟩ := fixK_spec h1
  have hset := fixed_set (fun f hf => (hF f hf).2) hpF hpY (by omega)
  unfold fixListK at h2
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, List.contains_iff_mem] at h2
  obtain ⟨⟨hinc, hW⟩, hspan⟩ := h2
  unfold CFSG.Sporadic.Co1.OddNative.fixList
  rw [collectBelow_eq, List.append_nil]
  have hmem : ∀ x, x ∈ (List.range 16777216).filter
      (fun x => [unpackR 24 TA, unpackR 24 TB].all fun Mt =>
        CFSG.Sporadic.Co1.OddNative.isFixedN Mt x) ↔ x ∈ W := by
    intro x
    simp only [List.mem_filter, List.mem_range, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, isFixed_unpackR, beq_iff_eq]
    constructor
    · rintro ⟨hx, hA, hB⟩
      have hx' : x < 2 ^ 24 := hx
      have hv : vecOf x ∈ {v : Fin 24 → ZMod 2 | v ᵥ* rowsMatrix 24 (unpackR 24 TA) = v} := by
        change vecOf x ᵥ* rowsMatrix 24 (unpackR 24 TA) = vecOf x
        rw [vecMul_eq, hA]
      rw [hset] at hv
      obtain ⟨c, hc⟩ := hv
      obtain ⟨y, hy, e⟩ := spanK_comb F F.length rfl (fun f hf => (hF f hf).1) 0
        (Nat.two_pow_pos 24) c
      have h0 : vecOf 0 = 0 := toVecD_zero 24
      rw [h0, zero_add, hc] at e
      have hy24 := spanK_lt F (fun f hf => (hF f hf).1) 0 (Nat.two_pow_pos 24) y hy
      have hxy : x = y := toVecD_injective hx' hy24 e
      subst hxy
      rcases hspan x hy with h | h
      · exact absurd hB h
      · exact h
    · intro hx
      obtain ⟨⟨h1, h2⟩, h3⟩ := hW x hx
      exact ⟨h1, h2, h3⟩
  have hp1 : ((List.range 16777216).filter (fun x => [unpackR 24 TA, unpackR 24 TB].all fun Mt =>
      CFSG.Sporadic.Co1.OddNative.isFixedN Mt x)).Pairwise (· < ·) :=
    List.pairwise_lt_range.filter _
  have hp2 := strictInc_pairwise W hinc
  have hperm := (List.perm_ext_iff_of_nodup (hp1.imp ne_of_lt) (hp2.imp ne_of_lt)).2 hmem
  exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => Nat.le_antisymm h1 h2) (hp1.imp le_of_lt)
    (hp2.imp le_of_lt)

end CFSG.KC.Co1Fix

end
