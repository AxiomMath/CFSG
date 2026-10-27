module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.UnitaryInvolutionIndex

variable {M : Type*} [Group M] (A : Subgroup M) {t : M}

theorem conj_mem_of_mem_normalizer (htA : t ∈ Subgroup.normalizer (A : Set M)) {x : M}
    (hx : x ∈ A) : t * x * t⁻¹ ∈ A :=
  (Subgroup.mem_normalizer_iff.mp htA x).mp hx

@[expose] def commutatorHom (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (htA : t ∈ Subgroup.normalizer (A : Set M)) : A →* A where
  toFun x := ⟨(x : M)⁻¹ * (t * x * t⁻¹),
    A.mul_mem (A.inv_mem x.2) (conj_mem_of_mem_normalizer A htA x.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by
    have hy : (y : M)⁻¹ ∈ A := A.inv_mem y.2
    have hx : (x : M)⁻¹ * (t * x * t⁻¹) ∈ A :=
      A.mul_mem (A.inv_mem x.2) (conj_mem_of_mem_normalizer A htA x.2)
    simp only [Subgroup.coe_mul]
    calc ((x : M) * y)⁻¹ * (t * (x * y) * t⁻¹)
        = (y : M)⁻¹ * ((x : M)⁻¹ * (t * x * t⁻¹)) * (t * y * t⁻¹) := by group
      _ = ((x : M)⁻¹ * (t * x * t⁻¹)) * (y : M)⁻¹ * (t * y * t⁻¹) := by rw [hA _ hy _ hx]
      _ = (x : M)⁻¹ * (t * x * t⁻¹) * ((y : M)⁻¹ * (t * y * t⁻¹)) := by group)

variable {A}

theorem coe_commutatorHom (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (htA : t ∈ Subgroup.normalizer (A : Set M)) (x : A) :
    (commutatorHom A hA htA x : M) = (x : M)⁻¹ * (t * x * t⁻¹) :=
  rfl

theorem map_range_commutatorHom (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (htA : t ∈ Subgroup.normalizer (A : Set M)) :
    (commutatorHom A hA htA).range.map A.subtype =
      Subgroup.closure {y | ∃ x ∈ A, y = x⁻¹ * (t * x * t⁻¹)} := by
  rw [MonoidHom.map_range]
  have hset : {y | ∃ x ∈ A, y = x⁻¹ * (t * x * t⁻¹)} =
      ((A.subtype.comp (commutatorHom A hA htA)).range : Set M) := by
    ext y
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, MonoidHom.mem_range, MonoidHom.coe_comp,
      Function.comp_apply, Subgroup.coe_subtype, coe_commutatorHom]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
  rw [hset, Subgroup.closure_eq]

theorem closure_commutator_le (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (htA : t ∈ Subgroup.normalizer (A : Set M)) :
    Subgroup.closure {y | ∃ x ∈ A, y = x⁻¹ * (t * x * t⁻¹)} ≤ A := by
  rw [← map_range_commutatorHom hA htA]
  exact Subgroup.map_subtype_le _

omit A in
theorem conj_commutator_eq_inv (ht : t ^ 2 = 1) (x : M) :
    t * (x⁻¹ * (t * x * t⁻¹)) * t⁻¹ = (x⁻¹ * (t * x * t⁻¹))⁻¹ := by
  have htt : t * t = 1 := by rw [← sq, ht]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  calc t * (x⁻¹ * (t * x * t⁻¹)) * t⁻¹ = t * x⁻¹ * t * x * (t⁻¹ * t⁻¹) := by group
    _ = t * x⁻¹ * t * x := by rw [htinv, htt, mul_one]
    _ = t * x⁻¹ * t⁻¹ * x := by rw [htinv]
    _ = (x⁻¹ * (t * x * t⁻¹))⁻¹ := by group

variable (ht : t ^ 2 = 1) (htA : t ∈ Subgroup.normalizer (A : Set M))
  (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
include ht htA hA

theorem conj_eq_inv_of_mem {b : M}
    (hb : b ∈ Subgroup.closure {y | ∃ x ∈ A, y = x⁻¹ * (t * x * t⁻¹)}) :
    t * b * t⁻¹ = b⁻¹ := by
  rw [← map_range_commutatorHom hA htA] at hb
  obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := hb
  exact conj_commutator_eq_inv ht x

theorem inf_eq_bot [Finite A] (hodd : Odd (Nat.card A)) :
    A ⊓ Subgroup.centralizer {t} ⊓ Subgroup.closure {y | ∃ x ∈ A, y = x⁻¹ * (t * x * t⁻¹)} =
      ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_inf, Subgroup.mem_inf] at hy
  obtain ⟨⟨hyA, hyC⟩, hyB⟩ := hy
  rw [Subgroup.mem_bot]
  have h1 : t * y * t⁻¹ = y := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hyC
    rw [← hyC, mul_inv_cancel_right]
  have h2 := conj_eq_inv_of_mem ht htA hA hyB
  rw [h1] at h2
  have hy2 : y ^ 2 = 1 := by rw [sq]; nth_rw 2 [h2]; exact mul_inv_cancel y
  have hyN : y ^ Nat.card A = 1 := by
    have := pow_card_eq_one' (G := A) (x := ⟨y, hyA⟩)
    exact congrArg Subtype.val this
  have h := pow_gcd_eq_one.mpr ⟨hy2, hyN⟩
  rwa [Nat.coprime_two_left.mpr hodd, pow_one] at h

theorem sup_eq [Finite A] (hodd : Odd (Nat.card A)) :
    A ⊓ Subgroup.centralizer {t} ⊔ Subgroup.closure {y | ∃ x ∈ A, y = x⁻¹ * (t * x * t⁻¹)} =
      A := by
  refine le_antisymm (sup_le inf_le_left (closure_commutator_le hA htA)) fun x hx => ?_
  obtain ⟨r, hr⟩ := hodd
  set u := x⁻¹ * (t * x * t⁻¹) with hu
  have huA : u ∈ A := A.mul_mem (A.inv_mem hx) (conj_mem_of_mem_normalizer A htA hx)
  have huB : u ∈ Subgroup.closure {y | ∃ x ∈ A, y = x⁻¹ * (t * x * t⁻¹)} :=
    Subgroup.subset_closure ⟨x, hx, rfl⟩
  have hu2 : u ^ (r + 1) * u ^ (r + 1) = u := by
    have hN : u ^ Nat.card A = 1 := by
      have := pow_card_eq_one' (G := A) (x := ⟨u, huA⟩)
      exact congrArg Subtype.val this
    rw [← pow_add, show r + 1 + (r + 1) = Nat.card A + 1 by omega, pow_succ, hN, one_mul]
  have hc : x * u ^ (r + 1) ∈ A ⊓ Subgroup.centralizer {t} := by
    refine Subgroup.mem_inf.mpr ⟨A.mul_mem hx (A.pow_mem huA _), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hconj : t * u ^ (r + 1) * t⁻¹ = (u ^ (r + 1))⁻¹ := by
      have := conj_commutator_eq_inv ht x
      rw [← hu] at this
      rw [show t * u ^ (r + 1) * t⁻¹ = (t * u * t⁻¹) ^ (r + 1) by
        rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply], this, inv_pow]
    have htx : t * x * t⁻¹ = x * u := by rw [hu, mul_inv_cancel_left]
    have key : t * (x * u ^ (r + 1)) * t⁻¹ = x * u ^ (r + 1) := by
      calc t * (x * u ^ (r + 1)) * t⁻¹ = (t * x * t⁻¹) * (t * u ^ (r + 1) * t⁻¹) := by group
        _ = x * u * (u ^ (r + 1))⁻¹ := by rw [htx, hconj]
        _ = x * (u ^ (r + 1) * u ^ (r + 1)) * (u ^ (r + 1))⁻¹ := by rw [hu2]
        _ = x * u ^ (r + 1) := by group
    calc x * u ^ (r + 1) * t = t * (x * u ^ (r + 1)) * t⁻¹ * t := by rw [key]
      _ = t * (x * u ^ (r + 1)) := by group
  have hb : (u ^ (r + 1))⁻¹ ∈ Subgroup.closure {y | ∃ x ∈ A, y = x⁻¹ * (t * x * t⁻¹)} :=
    Subgroup.inv_mem _ (Subgroup.pow_mem _ huB _)
  have := Subgroup.mul_mem_sup hc hb
  rwa [mul_inv_cancel_right] at this

omit ht in
theorem relIndex_eq_card :
    (A ⊓ Subgroup.centralizer {t}).relIndex A =
      Nat.card (Subgroup.closure {y | ∃ x ∈ A, y = x⁻¹ * (t * x * t⁻¹)}) := by
  have hker : (A ⊓ Subgroup.centralizer {t}).subgroupOf A = (commutatorHom A hA htA).ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, hx⟩
      apply Subtype.ext
      rw [coe_commutatorHom, Subgroup.coe_one, ← hx, mul_inv_cancel_right, inv_mul_cancel]
    · intro hx
      refine ⟨x.2, ?_⟩
      have := congrArg Subtype.val hx
      rw [coe_commutatorHom, Subgroup.coe_one, inv_mul_eq_one] at this
      calc (x : M) * t = t * x * t⁻¹ * t := by rw [← this]
        _ = t * x := by group
  rw [Subgroup.relIndex, hker, Subgroup.index_ker, ← map_range_commutatorHom hA htA,
    Subgroup.card_map_of_injective A.subtype_injective]

end CFSG.UnitaryInvolutionIndex
