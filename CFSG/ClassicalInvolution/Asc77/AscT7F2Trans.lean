module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.ClassicalInvolution.Asc77.T7F2

open MulAction Subgroup

section Simple

variable {G : Type*} [Group G]

theorem hom_eq_one_of_isSimpleGroup [IsSimpleGroup G] (hnc : ∃ x y : G, x * y ≠ y * x)
    (f : G →* Multiplicative (ZMod 2)) : f = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    apply f.ker_eq_bot_iff.mp h
    rw [map_mul, map_mul, mul_comm]
  · ext g
    have : g ∈ f.ker := h ▸ Subgroup.mem_top g
    simpa using this

end Simple

section Transfer

variable {G : Type*} [Group G]

theorem minimalPeriod_dvd_orderOf {α : Type*} [MulAction G α] (g : G) (X : α) :
    Function.minimalPeriod (fun x => g • x) X ∣ orderOf g := by
  apply Function.IsPeriodicPt.minimalPeriod_dvd
  change (fun x => g • x)^[orderOf g] X = X
  rw [smul_iterate]
  simp [pow_orderOf_eq_one]

theorem transfer_eq_pow_index [Finite G] {H : Subgroup G} [H.FiniteIndex] {A : Type*}
    [CommGroup A] (ϕ : H →* A) (a : G) (m : ℕ) (hord : orderOf a = 2 ^ m) (c : A)
    (hc : c ^ 2 = 1)
    (h1 : ∀ (x : G) (hx : x⁻¹ * a * x ∈ H), ϕ ⟨x⁻¹ * a * x, hx⟩ = c)
    (h2 : ∀ (i : ℕ) (x : G) (hx : x⁻¹ * a ^ (2 ^ (i + 1)) * x ∈ H),
      ϕ ⟨x⁻¹ * a ^ (2 ^ (i + 1)) * x, hx⟩ = 1) :
    ϕ.transfer a = c ^ H.index := by
  classical
  have : Fintype (Quotient (orbitRel (zpowers a) (G ⧸ H))) := Fintype.ofFinite _
  have : Finite (G ⧸ H) := inferInstance
  have key : ∀ (k : ℕ), (k = 1 ∨ ∃ i : ℕ, k = 2 ^ (i + 1)) → ∀ (x : G)
      (hx : x⁻¹ * a ^ k * x ∈ H), ϕ ⟨x⁻¹ * a ^ k * x, hx⟩ = c ^ k := by
    rintro k (rfl | ⟨i, rfl⟩) x hx
    · have hx' : x⁻¹ * a * x ∈ H := by simpa using hx
      have e : (⟨x⁻¹ * a ^ 1 * x, hx⟩ : H) = ⟨x⁻¹ * a * x, hx'⟩ := Subtype.ext (by simp)
      rw [e, h1 x hx', pow_one]
    · have hq : c ^ (2 ^ (i + 1)) = 1 := by
        rw [pow_succ, pow_mul, pow_right_comm, hc, one_pow]
      rw [hq]
      exact h2 i x hx
  rw [ϕ.transfer_eq_prod_quotient_orbitRel_zpowers_quot a, index_eq_sum_minimalPeriod H a,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun q _ => ?_
  have hdvd : Function.minimalPeriod (a • ·) q.out ∣ 2 ^ m := hord ▸ minimalPeriod_dvd_orderOf a _
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  refine key _ ?_ _ _
  cases i with
  | zero => exact Or.inl (by simpa using hi)
  | succ i => exact Or.inr ⟨i, hi⟩

noncomputable def charOfIndexTwo (K : Subgroup G) (hK : K.index = 2) :
    G →* Multiplicative (ZMod 2) where
  toFun g := open Classical in if g ∈ K then 1 else Multiplicative.ofAdd 1
  map_one' := by simp
  map_mul' x y := by
    classical
    have hxy := Subgroup.mul_mem_iff_of_index_two hK (a := x) (b := y)
    by_cases hx : x ∈ K <;> by_cases hy : y ∈ K <;>
      simp only [hx, hy, hxy, ite_true, ite_false, iff_true, iff_false, mul_one, one_mul,
        not_true_eq_false]
    decide

theorem charOfIndexTwo_apply_of_mem {K : Subgroup G} (hK : K.index = 2) {g : G} (hg : g ∈ K) :
    charOfIndexTwo K hK g = 1 := by
  simp [charOfIndexTwo, hg]

theorem charOfIndexTwo_apply_of_not_mem {K : Subgroup G} (hK : K.index = 2) {g : G}
    (hg : g ∉ K) : charOfIndexTwo K hK g = Multiplicative.ofAdd 1 := by
  simp [charOfIndexTwo, hg]

theorem false_of_fusion [Finite G] (hG : ∀ f : G →* Multiplicative (ZMod 2), f = 1)
    (S : Sylow 2 G) (B : Subgroup G) (hB : B.relIndex (S : Subgroup G) = 2) (a : G)
    (haS : a ∈ (S : Subgroup G))
    (h1 : ∀ x : G, x⁻¹ * a * x ∈ (S : Subgroup G) → x⁻¹ * a * x ∉ B)
    (h2 : ∀ (i : ℕ) (x : G), x⁻¹ * a ^ (2 ^ (i + 1)) * x ∈ (S : Subgroup G) →
      x⁻¹ * a ^ (2 ^ (i + 1)) * x ∈ B) : False := by
  classical
  set H : Subgroup G := (S : Subgroup G) with hH
  have hidx : (B.subgroupOf H).index = 2 := hB
  let ϕ : ↥H →* Multiplicative (ZMod 2) := charOfIndexTwo (B.subgroupOf H) hidx
  have hϕ1 : ∀ (y : G) (hy : y ∈ H), y ∈ B → ϕ ⟨y, hy⟩ = 1 := fun y hy hyB =>
    charOfIndexTwo_apply_of_mem hidx (Subgroup.mem_subgroupOf.mpr hyB)
  have hϕc : ∀ (y : G) (hy : y ∈ H), y ∉ B → ϕ ⟨y, hy⟩ = Multiplicative.ofAdd 1 := fun y hy hyB =>
    charOfIndexTwo_apply_of_not_mem hidx (fun h => hyB (Subgroup.mem_subgroupOf.mp h))
  have hord : ∃ m : ℕ, orderOf a = 2 ^ m := by
    have := (IsPGroup.iff_orderOf (p := 2) (G := ↥H)).mp S.isPGroup' ⟨a, haS⟩
    obtain ⟨m, hm⟩ := this
    exact ⟨m, by simpa using hm⟩
  obtain ⟨m, hm⟩ := hord
  have hc : (Multiplicative.ofAdd (1 : ZMod 2)) ^ 2 = 1 := by decide
  have hT := transfer_eq_pow_index ϕ a m hm (Multiplicative.ofAdd (1 : ZMod 2)) hc
    (fun x hx => hϕc _ hx (h1 x hx)) (fun i x hx => hϕ1 _ hx (h2 i x hx))
  have hodd : Odd H.index := by
    have h2 : ¬ 2 ∣ H.index := S.not_dvd_index
    rw [Nat.odd_iff]
    omega
  have hone : ϕ.transfer a = 1 := by
    have := hG ϕ.transfer
    exact congrArg (fun f => f a) this
  rw [hone] at hT
  obtain ⟨k, hk⟩ := hodd
  rw [hk, pow_succ, pow_mul, hc, one_pow, one_mul] at hT
  exact absurd hT.symm (by decide)

end Transfer

end CFSG.ClassicalInvolution.Asc77.T7F2
