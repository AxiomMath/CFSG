module

public import CFSG.LinearAlgebra.OddSolvableUnitary.LowDegreeScalar
public import CFSG.LinearAlgebra.OddSolvableUnitary.MonomialIndex

public section

namespace CFSG.OddSolvableUnitary

open Module Subgroup

section Plane

variable {K U : Type*} [Field K] [AddCommGroup U] [Module K U] (hU : finrank K U = 2)
  {X : Module.End K U} (hX : ∀ c : K, X ≠ c • 1)
include hU hX

theorem exists_basis_cyclic : ∃ b : Basis (Fin 2) K U, b 1 = X (b 0) := by
  have : FiniteDimensional K U := Module.finite_of_finrank_eq_succ hU
  obtain ⟨u, hu⟩ : ∃ u : U, LinearIndependent K ![u, X u] := by
    by_contra! h
    obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent h
    exact hX a ha
  let b := basisOfLinearIndependentOfCardEqFinrank hu (by simp [hU])
  exact ⟨b, by simp [b]⟩

theorem exists_add_smul_of_commute {Y : Module.End K U} (hYX : Y * X = X * Y) :
    ∃ α β : K, Y = α • 1 + β • X := by
  obtain ⟨b, hb1⟩ := exists_basis_cyclic hU hX
  have h := b.sum_repr (Y (b 0))
  rw [Fin.sum_univ_two, hb1] at h
  set α := b.repr (Y (b 0)) 0
  set β := b.repr (Y (b 0)) 1
  refine ⟨α, β, b.ext fun i => ?_⟩
  fin_cases i
  · change Y (b 0) = (α • 1 + β • X) (b 0)
    rw [← h]
    simp
  · change Y (b 1) = (α • 1 + β • X) (b 1)
    rw [hb1, ← Module.End.mul_apply, hYX, Module.End.mul_apply, ← h]
    simp [map_add, map_smul]

theorem exists_sq_eq_add_smul : ∃ t d : K, X ^ 2 = t • X + d • 1 := by
  obtain ⟨d, t, h⟩ := exists_add_smul_of_commute hU hX (Y := X ^ 2) (by rw [sq, mul_assoc])
  exact ⟨t, d, by rw [h, add_comm]⟩

theorem eq_zero_of_smul_add_smul_eq_zero {α β : K} (h : α • (1 : Module.End K U) + β • X = 0) :
    α = 0 ∧ β = 0 := by
  by_cases hβ : β = 0
  · subst hβ
    have : FiniteDimensional K U := Module.finite_of_finrank_eq_succ hU
    have : Nontrivial U := Module.nontrivial_of_finrank_pos (R := K) (by omega)
    obtain ⟨v, hv⟩ := exists_ne (0 : U)
    have := congrArg (fun f : Module.End K U => f v) h
    simp only [zero_smul, add_zero, LinearMap.smul_apply, Module.End.one_apply,
      LinearMap.zero_apply] at this
    exact ⟨(smul_eq_zero.1 this).resolve_right hv, rfl⟩
  · exfalso
    refine hX (-(β⁻¹ * α)) ?_
    have h' : β • X = -(α • 1) := eq_neg_of_add_eq_zero_right h
    calc X = β⁻¹ • (β • X) := by rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]
      _ = -(β⁻¹ * α) • 1 := by rw [h', smul_neg, smul_smul, neg_smul]

end Plane

section Odd

variable {G : Type*} [Group G] [Finite G] {K U : Type*} [Field K] [Finite K] [CharP K 2]
  [AddCommGroup U] [Module K U]

theorem commute_of_odd_of_finrank_two_of_injective (hodd : Odd (Nat.card G))
    (hsolv : Group.IsSolvable G) (hU : finrank K U = 2) (ρ : G →* Module.End K U)
    (hρ : Function.Injective ρ) (a b : G) : a * b = b * a := by
  classical
  have : FiniteDimensional K U := Module.finite_of_finrank_eq_succ hU
  by_cases hall : ∀ A : Subgroup G, A.Normal → IsMulCommutative A → ∀ x ∈ A, ∃ c : K, ρ x = c • 1
  · obtain ⟨hsc, -⟩ := isCyclic_and_scalar_of_forall_abelian_normal_scalar hodd hsolv (Or.inl hU)
      ρ hρ hall
    obtain ⟨c, hc⟩ := hsc a
    obtain ⟨d, hd⟩ := hsc b
    apply hρ
    rw [map_mul, map_mul, hc, hd, smul_mul_smul_comm, smul_mul_smul_comm, mul_comm c d]
  push Not at hall
  obtain ⟨A, hAn, hAc, x₀, hx₀A, hx₀⟩ := hall
  set X := ρ x₀ with hXdef
  obtain ⟨t, d, hXsq⟩ := exists_sq_eq_add_smul hU hx₀
  have hoddx : Odd (orderOf x₀) := Odd.of_dvd_nat hodd (orderOf_dvd_natCard x₀)
  have ht : t ≠ 0 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hoddx
    have h1 : X ^ orderOf x₀ = 1 := by rw [hXdef, ← map_pow, pow_orderOf_eq_one, map_one]
    have h2 : X = d ^ (k + 1) • 1 := by
      calc X = X ^ orderOf x₀ * X := by rw [h1, one_mul]
        _ = (X ^ 2) ^ (k + 1) := by rw [← pow_mul, ← pow_succ, hk]; ring_nf
        _ = d ^ (k + 1) • 1 := by rw [hXsq, zero_smul, zero_add, smul_pow, one_pow]
    exact hx₀ _ h2
  have hconj : ∀ g : G, ρ (g * x₀ * g⁻¹) = X ∨ ρ (g * x₀ * g⁻¹) = X + t • 1 := by
    intro g
    set Y := ρ (g * x₀ * g⁻¹) with hYdef
    have hgA : g * x₀ * g⁻¹ ∈ A := hAn.conj_mem x₀ hx₀A g
    have hYX : Y * X = X * Y := by
      rw [hYdef, hXdef, ← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hAc.is_comm.comm ⟨_, hgA⟩ ⟨x₀, hx₀A⟩)
    obtain ⟨α, β, hY⟩ := exists_add_smul_of_commute hU hx₀ hYX
    have hgg : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have hgg' : ρ g * ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have e : Y = ρ g * X * ρ g⁻¹ := by rw [hYdef, map_mul, map_mul]
    have hXX : X * X = t • X + d • 1 := by rw [← sq]; exact hXsq
    have hYsq : Y ^ 2 = t • Y + d • 1 := by
      calc Y ^ 2 = ρ g * (X * X) * ρ g⁻¹ := by
            rw [e, sq]
            calc ρ g * X * ρ g⁻¹ * (ρ g * X * ρ g⁻¹) =
                ρ g * X * (ρ g⁻¹ * ρ g) * X * ρ g⁻¹ := by simp only [mul_assoc]
              _ = ρ g * (X * X) * ρ g⁻¹ := by rw [hgg, mul_one]; simp only [mul_assoc]
        _ = t • Y + d • 1 := by
            rw [hXX, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
              smul_mul_assoc, mul_one, hgg', ← e]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have e2 : (α • (1 : Module.End K U) + β • X) ^ 2 =
        (α ^ 2 + β ^ 2 * d) • 1 + (2 * α * β + β ^ 2 * t) • X := by
      calc (α • (1 : Module.End K U) + β • X) ^ 2
          = (α * α) • ((1 : Module.End K U) * 1) + (α * β) • (1 * X) + (β * α) • (X * 1) +
              (β * β) • (X * X) := by
            rw [sq]
            simp only [mul_add, add_mul, smul_mul_smul_comm]
            abel
        _ = _ := by
            rw [hXX, one_mul, one_mul, mul_one]
            module
    have h3 : (α ^ 2 + β ^ 2 * d) • (1 : Module.End K U) + (2 * α * β + β ^ 2 * t) • X =
        t • (α • 1 + β • X) + d • 1 := by
      rw [← e2, ← hY]
      exact hYsq
    rw [h2, zero_mul, zero_mul, zero_add] at h3
    have hrel : (α ^ 2 + β ^ 2 * d - t * α - d) • (1 : Module.End K U) +
        (β ^ 2 * t - t * β) • X = 0 := by
      calc (α ^ 2 + β ^ 2 * d - t * α - d) • (1 : Module.End K U) + (β ^ 2 * t - t * β) • X
          = ((α ^ 2 + β ^ 2 * d) • 1 + (β ^ 2 * t) • X) - (t • (α • 1 + β • X) + d • 1) := by
            module
        _ = 0 := by rw [h3, sub_self]
    obtain ⟨h1, h2'⟩ := eq_zero_of_smul_add_smul_eq_zero hU hx₀ hrel
    have hβ : β = 1 := by
      have : t * β * (β - 1) = 0 := by linear_combination h2'
      rcases mul_eq_zero.1 this with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h ht
        · exfalso
          subst h
          refine hx₀ α ?_
          have e' : X = ρ g⁻¹ * Y * ρ g := by
            rw [e]
            calc X = (ρ g⁻¹ * ρ g) * X * (ρ g⁻¹ * ρ g) := by rw [hgg, one_mul, mul_one]
              _ = ρ g⁻¹ * (ρ g * X * ρ g⁻¹) * ρ g := by simp only [mul_assoc]
          rw [e', hY, zero_smul, add_zero, mul_smul_comm, mul_one, smul_mul_assoc, hgg]
      · exact sub_eq_zero.1 h
    subst hβ
    have hα : α * (α - t) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 hα with h | h
    · left
      rw [hY, h, zero_smul, zero_add, one_smul]
    · right
      rw [hY, sub_eq_zero.1 h, one_smul, add_comm]
  have hcen : ∀ g : G, g * x₀ * g⁻¹ = x₀ := by
    set C := {y | ∃ g ∈ (⊤ : Subgroup G), g * x₀ * g⁻¹ = y}
    have hCsub : ρ '' C ⊆ {X, X + t • 1} := by
      rintro _ ⟨y, ⟨g, -, rfl⟩, rfl⟩
      rcases hconj g with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hCle : C.ncard ≤ 2 := by
      have h1 := Set.ncard_le_ncard hCsub (Set.toFinite _)
      rw [Set.ncard_image_of_injective _ hρ] at h1
      refine h1.trans ((Set.ncard_insert_le _ _).trans ?_)
      rw [Set.ncard_singleton]
    have hdvd : C.ncard ∣ Nat.card G := by
      have h := ncard_conj_mul_card_inf_centralizer (⊤ : Subgroup G) x₀
      rw [card_top] at h
      exact Dvd.intro _ h
    have hpos : 0 < C.ncard := Set.ncard_pos (Set.toFinite _) |>.2 ⟨x₀, 1, mem_top 1, by group⟩
    have hC1 : C.ncard = 1 := by
      interval_cases h : C.ncard
      · rfl
      · exact absurd (even_iff_two_dvd.2 hdvd) (Nat.not_even_iff_odd.2 hodd)
    obtain ⟨y, hy⟩ := Set.ncard_eq_one.1 hC1
    intro g
    have h1 : g * x₀ * g⁻¹ ∈ C := ⟨g, mem_top g, rfl⟩
    have h2 : x₀ ∈ C := ⟨1, mem_top 1, by group⟩
    rw [hy] at h1 h2
    rw [Set.mem_singleton_iff] at h1 h2
    rw [h1, h2]
  have hcomX : ∀ g : G, ρ g * X = X * ρ g := by
    intro g
    rw [hXdef, ← map_mul, ← map_mul]
    congr 1
    calc g * x₀ = g * x₀ * g⁻¹ * g := by group
      _ = x₀ * g := by rw [hcen g]
  obtain ⟨αa, βa, ha⟩ := exists_add_smul_of_commute hU hx₀ (hcomX a)
  obtain ⟨αb, βb, hb⟩ := exists_add_smul_of_commute hU hx₀ (hcomX b)
  apply hρ
  rw [map_mul, map_mul, ha, hb]
  simp only [mul_add, add_mul, smul_mul_smul_comm, one_mul, mul_one]
  rw [mul_comm αa αb, mul_comm βa βb, mul_comm αa βb, mul_comm βa αb]
  abel

theorem commute_of_odd_of_finrank_two (hodd : Odd (Nat.card G)) (hsolv : Group.IsSolvable G)
    (hU : finrank K U = 2) (ρ : G →* Module.End K U) (a b : G) : ρ a * ρ b = ρ b * ρ a := by
  let G' := (ρ.toHomUnits).range
  have : Finite G' := Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective ρ.toHomUnits)
  have hodd' : Odd (Nat.card G') := Odd.of_dvd_nat hodd (Subgroup.card_range_dvd _)
  have hsolv' : Group.IsSolvable G' :=
    Group.isSolvable_of_surjective (MonoidHom.rangeRestrict_surjective ρ.toHomUnits)
  let ρ' : G' →* Module.End K U := (Units.coeHom _).comp G'.subtype
  have hρ' : Function.Injective ρ' := fun x y h => Subtype.ext (Units.ext h)
  have h := commute_of_odd_of_finrank_two_of_injective hodd' hsolv' hU ρ' hρ'
    ⟨ρ.toHomUnits a, a, rfl⟩ ⟨ρ.toHomUnits b, b, rfl⟩
  exact congrArg (fun x : G' => ((x : (Module.End K U)ˣ) : Module.End K U)) h

end Odd

end CFSG.OddSolvableUnitary
