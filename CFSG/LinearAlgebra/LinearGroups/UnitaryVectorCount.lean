module

public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian

public section

namespace CFSG.LinearGroups

open CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type*} [Field K]

section Count

variable (h : UnitaryFieldData p f K)

@[expose] noncomputable def normSumCount (m : ℕ) (c : K) : ℕ :=
  Nat.card {x : Fin m → K // ∑ i, h.norm (x i) = c}

theorem norm_eq_zero_iff {t : K} : h.norm t = 0 ↔ t = 0 := by
  rw [UnitaryFieldData.norm, mul_eq_zero, map_eq_zero, or_self]

theorem normSumCount_zero_dim_zero : normSumCount h 0 0 = 1 := by
  unfold normSumCount
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩, ⟨⟨Fin.elim0, by simp⟩⟩⟩

theorem normSumCount_zero_dim_of_ne {c : K} (hc : c ≠ 0) : normSumCount h 0 c = 0 := by
  unfold normSumCount
  rw [Nat.card_eq_zero]
  left
  exact ⟨fun ⟨x, hx⟩ => hc (by simpa using hx.symm)⟩

theorem normSumCount_succ [Fintype K] (m : ℕ) (c : K) :
    normSumCount h (m + 1) c = ∑ t : K, normSumCount h m (c - h.norm t) := by
  classical
  unfold normSumCount
  let e : {x : Fin (m + 1) → K // ∑ i, h.norm (x i) = c} ≃
      Σ t : K, {y : Fin m → K // ∑ i, h.norm (y i) = c - h.norm t} :=
    { toFun := fun x => ⟨x.1 0, ⟨Fin.tail x.1, by
        have hx := x.2
        rw [Fin.sum_univ_succ] at hx
        exact eq_sub_of_add_eq' hx⟩⟩
      invFun := fun y => ⟨Fin.cons y.1 y.2.1, by
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, y.2.2]
        ring⟩
      left_inv := fun x => Subtype.ext (Fin.cons_self_tail x.1)
      right_inv := fun y => by
        obtain ⟨t, ⟨y, hy⟩⟩ := y
        rfl }
  rw [Nat.card_congr e, Nat.card_sigma]

theorem normSumCount_eq_of_mem {m : ℕ} {d d' : K} (hd : d ∈ h.fixedField) (hd0 : d ≠ 0)
    (hd' : d' ∈ h.fixedField) (hd'0 : d' ≠ 0) : normSumCount h m d = normSumCount h m d' := by
  have hmem : d' / d ∈ h.fixedField := h.fixedField.div_mem hd' hd
  obtain ⟨μ, hμ⟩ := h.normHom_surjective ⟨d' / d, hmem⟩
  have hμ' : h.norm μ = d' / d := congrArg Subtype.val hμ
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [show h.norm 0 = 0 from (norm_eq_zero_iff h).mpr rfl] at hμ'
    exact div_ne_zero hd'0 hd0 hμ'.symm
  have hnorm_smul : ∀ (a : K) (x : Fin m → K), ∑ i, h.norm ((a • x) i) =
      h.norm a * ∑ i, h.norm (x i) := by
    intro a x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, UnitaryFieldData.norm, map_mul]
    ring
  unfold normSumCount
  refine Nat.card_congr
    { toFun := fun x => ⟨μ • x.1, by rw [hnorm_smul, x.2, hμ', div_mul_cancel₀ _ hd0]⟩
      invFun := fun x => ⟨μ⁻¹ • x.1, by
        rw [hnorm_smul, x.2]
        have : h.norm μ⁻¹ = d / d' := by
          rw [UnitaryFieldData.norm, map_inv₀]
          rw [UnitaryFieldData.norm] at hμ'
          rw [← mul_inv, hμ', inv_div]
        rw [this, div_mul_cancel₀ _ hd'0]⟩
      left_inv := fun x => Subtype.ext (by simp [smul_smul, inv_mul_cancel₀ hμ0])
      right_inv := fun x => Subtype.ext (by simp [smul_smul, mul_inv_cancel₀ hμ0]) }

theorem card_norm_eq_one : Nat.card {t : K // h.norm t = 1} = p ^ f + 1 := by
  rw [← h.card_ker_normUnits_and_surjective.1]
  have hne : ∀ t : K, h.norm t = 1 → t ≠ 0 := by
    rintro t ht rfl
    rw [(norm_eq_zero_iff h).mpr rfl] at ht
    exact zero_ne_one ht
  exact Nat.card_congr
    { toFun := fun t => ⟨Units.mk0 t.1 (hne t.1 t.2),
        (UnitaryFieldData.mem_ker_normUnits h).mpr (by simpa using t.2)⟩
      invFun := fun u => ⟨((u : Kˣ) : K), (UnitaryFieldData.mem_ker_normUnits h).mp u.2⟩
      left_inv := fun t => rfl
      right_inv := fun u => Subtype.ext (Units.ext rfl) }

theorem normSumCount_succ_eq [Fintype K] [DecidableEq K] (m : ℕ) {c : K}
    (hc : c ∈ h.fixedField) :
    normSumCount h (m + 1) c = normSumCount h m c +
      (Finset.univ.filter fun t : K => t ≠ 0 ∧ h.norm t = c).card * normSumCount h m 0 +
      (Finset.univ.filter fun t : K => t ≠ 0 ∧ h.norm t ≠ c).card * normSumCount h m 1 := by
  rw [normSumCount_succ]
  have hN0 : h.norm 0 = 0 := (norm_eq_zero_iff h).mpr rfl
  have hg : ∀ t : K, normSumCount h m (c - h.norm t) =
      (if t = 0 then normSumCount h m c else 0) +
        (if t ≠ 0 ∧ h.norm t = c then normSumCount h m 0 else 0) +
        (if t ≠ 0 ∧ h.norm t ≠ c then normSumCount h m 1 else 0) := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simp [hN0]
    · by_cases hN : h.norm t = c
      · simp [ht, hN]
      · simp only [ht, hN, ite_false, not_false_eq_true, and_self, and_false, ite_true, zero_add,
          ne_eq]
        exact normSumCount_eq_of_mem h (h.fixedField.sub_mem hc (h.norm_mem_fixedField t))
          (sub_ne_zero.mpr (Ne.symm hN)) h.fixedField.one_mem one_ne_zero
  rw [Finset.sum_congr rfl fun t _ => hg t, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (0 : K), Finset.sum_ite, Finset.sum_ite]
  simp only [Finset.mem_univ, ite_true, Finset.sum_const, smul_eq_mul, mul_zero, add_zero]

theorem normSumCount_recursion (m : ℕ) :
    (normSumCount h (m + 1) 0 : ℤ) =
        normSumCount h m 0 + (((p ^ f : ℕ) : ℤ) ^ 2 - 1) * normSumCount h m 1 ∧
      (normSumCount h (m + 1) 1 : ℤ) = (((p ^ f : ℕ) : ℤ) + 1) * normSumCount h m 0 +
        (((p ^ f : ℕ) : ℤ) ^ 2 - ((p ^ f : ℕ) : ℤ) - 1) * normSumCount h m 1 := by
  classical
  have := h.finite
  have := Fintype.ofFinite K
  have hcardK : (Finset.univ : Finset K).card = (p ^ f) ^ 2 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, h.card_eq_sq]
  have hq := h.one_lt_pow
  have hne0 : (Finset.univ.filter fun t : K => t ≠ 0).card = (p ^ f) ^ 2 - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), hcardK]
  have hN1 : ∀ t : K, h.norm t = 1 → t ≠ 0 := by
    rintro t ht rfl
    rw [(norm_eq_zero_iff h).mpr rfl] at ht
    exact zero_ne_one ht
  have c00 : (Finset.univ.filter fun t : K => t ≠ 0 ∧ h.norm t = 0).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun t _ ht => ht.1 ((norm_eq_zero_iff h).mp ht.2)
  have c01 : (Finset.univ.filter fun t : K => t ≠ 0 ∧ h.norm t ≠ 0).card = (p ^ f) ^ 2 - 1 := by
    rw [← hne0]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ht => ht.1, fun ht => ⟨ht, fun h0 => ht ((norm_eq_zero_iff h).mp h0)⟩⟩
  have c10 : (Finset.univ.filter fun t : K => t ≠ 0 ∧ h.norm t = 1).card = p ^ f + 1 := by
    rw [← card_norm_eq_one h, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ht => ht.2, fun ht => ⟨hN1 t ht, ht⟩⟩
  have c11 : (Finset.univ.filter fun t : K => t ≠ 0 ∧ h.norm t ≠ 1).card + (p ^ f + 1) =
      (p ^ f) ^ 2 - 1 := by
    rw [← c10, ← hne0, add_comm]
    rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter
      fun t : K => t ≠ 0) (fun t => h.norm t = 1), Finset.filter_filter, Finset.filter_filter]
  have hq2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
  refine ⟨?_, ?_⟩
  · rw [normSumCount_succ_eq h m h.fixedField.zero_mem, c00, c01]
    push_cast [hq2]
    ring
  · rw [normSumCount_succ_eq h m h.fixedField.one_mem, c10]
    have hc11 : ((Finset.univ.filter fun t : K => t ≠ 0 ∧ h.norm t ≠ 1).card : ℤ) =
        ((p ^ f : ℕ) : ℤ) ^ 2 - 1 - ((p ^ f : ℕ) + 1) := by
      have := congrArg (fun n : ℕ => (n : ℤ)) c11
      push_cast [hq2] at this
      push_cast
      linear_combination this
    push_cast
    rw [hc11]
    push_cast
    ring

theorem normSumCount_closed (k : ℕ) :
    (normSumCount h (k + 1) 1 : ℤ) =
        ((p ^ f : ℕ) : ℤ) ^ k * (((p ^ f : ℕ) : ℤ) ^ (k + 1) - (-1) ^ (k + 1)) ∧
      (normSumCount h (k + 1) 0 : ℤ) = ((p ^ f : ℕ) : ℤ) ^ (2 * k + 1) +
        (-1) ^ (k + 1) * (((p ^ f : ℕ) : ℤ) - 1) * ((p ^ f : ℕ) : ℤ) ^ k := by
  induction k with
  | zero =>
    obtain ⟨hA, hB⟩ := normSumCount_recursion h 0
    rw [hA, hB, normSumCount_zero_dim_zero, normSumCount_zero_dim_of_ne h one_ne_zero]
    push_cast
    constructor <;> ring
  | succ k ih =>
    obtain ⟨hA, hB⟩ := normSumCount_recursion h (k + 1)
    obtain ⟨ihB, ihA⟩ := ih
    rw [hA, hB, ihA, ihB]
    constructor <;> ring

theorem sesq_self_eq_sum_norm {V : Type*} [AddCommGroup V] [Module K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} {n : ℕ} (e : Module.Basis (Fin n) K V)
    (he : ∀ i j, B (e i) (e j) = if i = j then 1 else 0) (v : V) :
    B v v = ∑ i, h.norm (e.equivFun v i) := by
  conv_lhs => rw [← e.sum_equivFun v]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, he, smul_eq_mul,
    mul_ite, mul_one, mul_zero, RingHom.id_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    UnitaryFieldData.norm]

end Count

theorem unitary_hermitian_vector_count (h : UnitaryFieldData p f K) {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {n : ℕ} (hn : Module.finrank K V = n) (hn1 : 1 ≤ n) :
    (Nat.card {v : V // B v v = 0} : ℤ) = ((p ^ f : ℕ) : ℤ) ^ (2 * n - 1) +
        (-1) ^ n * (((p ^ f : ℕ) : ℤ) - 1) * ((p ^ f : ℕ) : ℤ) ^ (n - 1) ∧
      (∀ c ∈ h.fixedField, c ≠ 0 → (Nat.card {v : V // B v v = c} : ℤ) =
        ((p ^ f : ℕ) : ℤ) ^ (n - 1) * (((p ^ f : ℕ) : ℤ) ^ n - (-1) ^ n)) ∧
      (Nat.card {v : V // v ≠ 0 ∧ B v v = 0} : ℤ) = (((p ^ f : ℕ) : ℤ) ^ n - (-1) ^ n) *
        (((p ^ f : ℕ) : ℤ) ^ (n - 1) - (-1) ^ (n - 1)) := by
  classical
  obtain ⟨e₀, he₀⟩ := h.exists_orthonormal_basis hB hBl
  let e : Module.Basis (Fin n) K V := e₀.reindex (finCongr hn)
  have he : ∀ i j, B (e i) (e j) = if i = j then 1 else 0 := by
    intro i j
    simp only [e, Module.Basis.reindex_apply, he₀, (finCongr hn).symm.injective.eq_iff]
  have hcount : ∀ c : K, Nat.card {v : V // B v v = c} = normSumCount h n c := by
    intro c
    refine Nat.card_congr (e.equivFun.subtypeEquiv fun v => ?_)
    rw [sesq_self_eq_sum_norm h e he]
    exact Iff.rfl
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hB1, hA⟩ := normSumCount_closed h k
  have hk1 : k + 1 - 1 = k := by omega
  have hk2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have hzero : (Nat.card {v : V // B v v = 0} : ℤ) = ((p ^ f : ℕ) : ℤ) ^ (2 * k + 1) +
      (-1) ^ (k + 1) * (((p ^ f : ℕ) : ℤ) - 1) * ((p ^ f : ℕ) : ℤ) ^ k := by
    rw [hcount, hA]
  refine ⟨by rw [hzero, hk1, hk2], fun c hc hc0 => ?_, ?_⟩
  · rw [hcount, normSumCount_eq_of_mem h hc hc0 h.fixedField.one_mem one_ne_zero, hB1, hk1]
  · have := h.finite
    have : Finite V := Module.finite_of_finite K
    have := Fintype.ofFinite V
    have hsplit : Nat.card {v : V // B v v = 0} = Nat.card {v : V // v ≠ 0 ∧ B v v = 0} + 1 := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
        Fintype.card_subtype, ← Finset.card_filter_add_card_filter_not
          (s := Finset.univ.filter fun v : V => B v v = 0) (fun v => v ≠ 0),
        Finset.filter_filter]
      congr 1
      · congr 1
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact and_comm
      · rw [Finset.card_eq_one]
        refine ⟨0, ?_⟩
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not, Finset.mem_singleton]
        constructor
        · exact fun hv => hv.2
        · rintro rfl
          exact ⟨by simp, rfl⟩
    have hsq : ((-1 : ℤ) ^ k) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    have := congrArg (fun n : ℕ => (n : ℤ)) hsplit
    push_cast at this
    rw [hk1]
    linear_combination -this + hzero + hsq

end CFSG.LinearGroups
