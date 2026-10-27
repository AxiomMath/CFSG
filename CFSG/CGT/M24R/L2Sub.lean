module

public import CFSG.CGT.M24R.L2Enum

public section

namespace CFSG.CGT.M24R

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable

theorem mem_closure_pair_iff {K : Type*} [Group K] {p q : K} (hp : p * p = 1) (hq : q * q = 1)
    (hpq : p * q = q * p) (x : K) :
    x ∈ Subgroup.closure ({p, q} : Set K) ↔ x = 1 ∨ x = p ∨ x = q ∨ x = p * q := by
  have e1 : p * (p * q) = q := by rw [← mul_assoc, hp, one_mul]
  have e2 : q * (p * q) = p := by rw [← mul_assoc, ← hpq, mul_assoc, hq, mul_one]
  have e4 : p * q * p = q := by rw [mul_assoc, ← hpq, ← mul_assoc, hp, one_mul]
  have e5 : p * q * q = p := by rw [mul_assoc, hq, mul_one]
  have e6 : p * q * (p * q) = 1 := by rw [mul_assoc, e2, hp]
  constructor
  · intro hx
    let S : Subgroup K :=
      { carrier := {y | y = 1 ∨ y = p ∨ y = q ∨ y = p * q}
        one_mem' := Or.inl rfl
        mul_mem' := by
          rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
            simp [hp, hq, e1, e2, e4, e5, e6, hpq.symm]
        inv_mem' := by
          rintro a (rfl | rfl | rfl | rfl)
          · simp
          · simp [inv_eq_of_mul_eq_one_right hp]
          · simp [inv_eq_of_mul_eq_one_right hq]
          · simp [mul_inv_rev, inv_eq_of_mul_eq_one_right hp, inv_eq_of_mul_eq_one_right hq,
              hpq.symm] }
    have hle : Subgroup.closure ({p, q} : Set K) ≤ S := by
      refine (Subgroup.closure_le S).2 ?_
      rintro y (rfl | rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    exact hle hx
  · have hpm : p ∈ Subgroup.closure ({p, q} : Set K) := Subgroup.subset_closure (by simp)
    have hqm : q ∈ Subgroup.closure ({p, q} : Set K) := Subgroup.subset_closure (by simp)
    rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact hpm
    · exact hqm
    · exact mul_mem hpm hqm

theorem card_eq_four_of {K : Type*} [Group K] (S : Subgroup K) {a b c d : K}
    (hS : ∀ y ∈ S, y = a ∨ y = b ∨ y = c ∨ y = d) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hd : d ∈ S) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) : Nat.card S = 4 := by
  have hset : (S : Set K) = {a, b, c, d} := by
    ext y
    simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · exact hS y
    · rintro (rfl | rfl | rfl | rfl) <;> assumption
  have h1 : (S : Set K).ncard = 4 := by
    rw [hset, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hcd]
    · simpa using ⟨hbc, hbd⟩
    · simpa using ⟨hab, hac, had⟩
  rw [← h1, ← Nat.card_coe_set_eq]
  rfl

theorem mem_normalizer_four {N : Type*} [Group N] {K : Subgroup N} {p q : N} (hp : p ∈ K)
    (hq : q ∈ K) (hK : ∀ y ∈ K, y = 1 ∨ y = p ∨ y = q ∨ y = p * q) {x : N} :
    x ∈ Subgroup.normalizer (K : Set N) ↔
      x * p * x⁻¹ ∈ K ∧ x * q * x⁻¹ ∈ K ∧ x⁻¹ * p * x ∈ K ∧ x⁻¹ * q * x ∈ K := by
  have key : ∀ z : N, z * p * z⁻¹ ∈ K → z * q * z⁻¹ ∈ K → ∀ y ∈ K, z * y * z⁻¹ ∈ K := by
    intro z h1 h2 y hy
    rcases hK y hy with rfl | rfl | rfl | rfl
    · simp
    · exact h1
    · exact h2
    · have : z * (p * q) * z⁻¹ = (z * p * z⁻¹) * (z * q * z⁻¹) := by group
      rw [this]
      exact K.mul_mem h1 h2
  constructor
  · intro hx
    have hx' : x⁻¹ ∈ Subgroup.normalizer (K : Set N) := (Subgroup.normalizer (K : Set N)).inv_mem hx
    refine ⟨(Subgroup.mem_normalizer_iff.1 hx p).1 hp, (Subgroup.mem_normalizer_iff.1 hx q).1 hq,
      ?_, ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.1 hx' p).1 hp
    · simpa using (Subgroup.mem_normalizer_iff.1 hx' q).1 hq
  · rintro ⟨h1, h2, h3, h4⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact key x h1 h2 y
    · intro hy
      have := key x⁻¹ (by simpa using h3) (by simpa using h4) _ hy
      simpa [mul_assoc] using this

@[expose] def T8 : Subgroup N8 := Subgroup.closure (Set.range tGen8)

theorem tw_zero : tw 0 = [] := by decide

theorem tw_two_pow (j : Fin 4) : tw (2 ^ j.val) = [(⟨6 + j.val, by omega⟩, true)] := by
  fin_cases j <;> decide

theorem n8_tw_mem (k : ℕ) : n8 (tw k) ∈ T8 := by
  have key : ∀ l : List (Fin 4),
      n8 (l.flatMap fun j => if k.testBit j.val then [(⟨6 + j.val, by omega⟩, true)] else []) ∈
        T8 := by
    intro l
    induction l with
    | nil => simp [n8_nil]
    | cons j l ih =>
      rw [List.flatMap_cons, n8_append]
      refine T8.mul_mem ?_ ih
      by_cases hj : k.testBit j.val
      · simp only [hj, ite_true]
        exact Subgroup.subset_closure ⟨j, rfl⟩
      · simp [hj, n8_nil]
  exact key (List.finRange 4)

theorem isTab_letTab (l : Fin 10 × Bool) :
    IsTab (letTab l) (n8 [l]) := by
  unfold IsTab
  rw [π8_n8, lift_gPerm_cons]
  simpa using rep_letTab l

theorem tt_size (k : ℕ) (hk : k < 16) : ((mkCtx ()).tt[k]!).size = 16 := by
  rw [ctx_tt hk]
  exact wTab_size _

section T

variable (hcard : Nat.card N8 = 322560)
include hcard

omit hcard in
theorem isTab_tt {k : ℕ} (hk : k < 16) : IsTab (mkCtx ()).tt[k]! (n8 (tw k)) := by
  rw [ctx_tt hk]
  exact isTab_wTab _

omit hcard in
theorem tCheck_spec : (∀ k < 16, ∀ l < 16,
      compT 16 (mkCtx ()).tt[k]! (mkCtx ()).tt[l]! = (mkCtx ()).tt[k ^^^ l]!) ∧
    (∀ k < 16, ∀ l < 16, (mkCtx ()).tt[k]! = (mkCtx ()).tt[l]! → k = l) ∧
    ∀ k < 16, codeOf (mkCtx ()).tt[k]! % 16 = k := by
  have h := Certificates.certificate21193.2.2.1
  simp only [tCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun k hk l hl hkl => ?_, h3⟩
  rcases h2 k hk l hl with h | h
  · rw [hkl] at h
    simp at h
  · exact h

theorem tw_mul {k l : ℕ} (hk : k < 16) (hl : l < 16) :
    n8 (tw k) * n8 (tw l) = n8 (tw (k ^^^ l)) := by
  have hkl : k ^^^ l < 16 := Nat.xor_lt_two_pow (n := 4) hk hl
  have h1 := (isTab_tt hk).mul (isTab_tt hl)
  rw [tCheck_spec.1 k hk l hl] at h1
  exact h1.eq_of_eq hcard (isTab_tt hkl)

theorem tw_inj {k l : ℕ} (hk : k < 16) (hl : l < 16) (h : n8 (tw k) = n8 (tw l)) : k = l :=
  tCheck_spec.2.1 k hk l hl
    (((isTab_tt hk).eq_iff hcard (isTab_tt hl) (tt_size k hk) (tt_size l hl)).2 h)

theorem tw_sq {k : ℕ} (hk : k < 16) : n8 (tw k) * n8 (tw k) = 1 := by
  rw [tw_mul hcard hk hk, Nat.xor_self, tw_zero, n8_nil]

theorem mem_T8_iff (x : N8) : x ∈ T8 ↔ ∃ k, k < 16 ∧ x = n8 (tw k) := by
  constructor
  · intro hx
    let S : Subgroup N8 :=
      { carrier := {x | ∃ k, k < 16 ∧ x = n8 (tw k)}
        one_mem' := ⟨0, by norm_num, by rw [tw_zero, n8_nil]⟩
        mul_mem' := by
          rintro _ _ ⟨k, hk, rfl⟩ ⟨l, hl, rfl⟩
          exact ⟨k ^^^ l, Nat.xor_lt_two_pow (n := 4) hk hl, tw_mul hcard hk hl⟩
        inv_mem' := by
          rintro _ ⟨k, hk, rfl⟩
          exact ⟨k, hk, inv_eq_of_mul_eq_one_right (tw_sq hcard hk)⟩ }
    have hle : T8 ≤ S := by
      refine (Subgroup.closure_le S).2 ?_
      rintro _ ⟨j, rfl⟩
      refine ⟨2 ^ j.val, ?_, ?_⟩
      · have : 2 ^ j.val < 2 ^ 4 := Nat.pow_lt_pow_right (by norm_num) j.isLt
        simpa using this
      · rw [tw_two_pow]
        rfl
    exact hle hx
  · rintro ⟨k, -, rfl⟩
    exact n8_tw_mem k

theorem isTt_iff {X : Table} {x : N8} (hX : IsTab X x) (hXs : X.size = 16) :
    (mkCtx ()).isTt X = true ↔ x ∈ T8 := by
  rw [mem_T8_iff hcard]
  constructor
  · intro h
    have hk : codeOf X % 16 < 16 := Nat.mod_lt _ (by norm_num)
    have h' : X = (mkCtx ()).tt[codeOf X % 16]! := by
      simpa [Ctx8.isTt] using h
    refine ⟨_, hk, ?_⟩
    rw [h'] at hX
    exact hX.eq_of_eq hcard (isTab_tt hk)
  · rintro ⟨k, hk, rfl⟩
    have h1 : X = (mkCtx ()).tt[k]! := (hX.eq_iff hcard (isTab_tt hk) hXs (tt_size k hk)).2 rfl
    have h2 : codeOf X % 16 = k := by rw [h1]; exact tCheck_spec.2.2 k hk
    unfold Ctx8.isTt
    rw [h2, h1, beq_self_eq_true]

theorem T8_normal : T8.Normal := by
  have h := Certificates.certificate21193.2.2.2.1
  simp only [tNormCheck, List.all_eq_true, List.mem_finRange, List.mem_range, List.any_eq_true,
    beq_iff_eq, forall_const] at h
  have hconj : ∀ (l : Fin 10 × Bool), ∀ t ∈ T8, n8 [l] * t * (n8 [l])⁻¹ ∈ T8 := by
    rintro ⟨j, b⟩ t ht
    obtain ⟨k, hk, rfl⟩ := (mem_T8_iff hcard t).1 ht
    obtain ⟨l, hl, hkl⟩ := h j b (by cases b <;> simp) k hk
    have e := ((isTab_letTab (j, b)).mul (isTab_tt hk)).eq_of_eq hcard
      (hkl ▸ (isTab_tt hl).mul (isTab_letTab (j, b)))
    rw [e, mul_inv_cancel_right]
    exact n8_tw_mem l
  have hof : ∀ j : Fin 10, n8 [(j, true)] = PresentedGroup.of j := fun j => rfl
  have hofi : ∀ j : Fin 10, n8 [(j, false)] = (PresentedGroup.of j)⁻¹ := by
    intro j
    rw [n8, show FreeGroup.mk [(j, false)] = (FreeGroup.of j)⁻¹ from rfl, map_inv]
    rfl
  have hN : ∀ j : Fin 10,
      (PresentedGroup.of j : N8) ∈ Subgroup.normalizer (T8 : Set N8) := by
    intro j
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      have := hconj (j, true) t ht
      rwa [hof] at this
    · intro ht
      have := hconj (j, false) _ ht
      rw [hofi] at this
      simpa [mul_assoc] using this
  have htop : Subgroup.normalizer (T8 : Set N8) = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← PresentedGroup.closure_range_of]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, rfl⟩
    exact hN j
  exact Subgroup.normalizer_eq_top_iff.1 htop

end T

end CFSG.CGT.M24R
