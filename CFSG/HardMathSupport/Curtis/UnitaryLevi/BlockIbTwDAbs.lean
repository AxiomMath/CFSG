module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

section Flag

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]

theorem fixed_of_flag (hK : ∀ c : K, c = 0 ∨ c = 1) {A : V ≃ₗ[K] V}
    (hA3 : ∀ v, A (A (A v)) = v) (S : ℕ → Submodule K V) (hS0 : S 0 = ⊥) {M : ℕ}
    (hS : ∀ j < M, ∃ u, S (j + 1) = S j ⊔ Submodule.span K {u})
    (hst : ∀ m ≤ M, ∀ v ∈ S m, A v ∈ S m) : ∀ v ∈ S M, A v = v := by
  have hadd : ∀ v : V, v + v = 0 := fun v => by
    rw [← two_smul K v, CharTwo.two_eq_zero, zero_smul]
  suffices h : ∀ m ≤ M, ∀ v ∈ S m, A v = v from h M le_rfl
  intro m
  induction m with
  | zero =>
    intro _ v hv
    rw [hS0, Submodule.mem_bot] at hv
    rw [hv, map_zero]
  | succ m ih =>
    intro hm v hv
    have ih' := ih (by omega)
    obtain ⟨u, hu⟩ := hS m (by omega)
    rw [hu] at hv
    obtain ⟨z, hz, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    have hAu : A u ∈ S m ⊔ Submodule.span K {u} := by
      rw [← hu]
      exact hst (m + 1) hm u (hu ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self u))
    obtain ⟨z', hz', w', hw', hAu0⟩ := Submodule.mem_sup.mp hAu
    obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hw'
    have hAu' : A u = z' + c' • u := hAu0.symm
    have hfu : A u = u := by
      rcases hK c' with rfl | rfl
      · rw [zero_smul, add_zero] at hAu'
        have h1 : A (A u) = A u := by rw [hAu']; exact ih' z' hz'
        have h2 := hA3 u
        rw [h1, h1] at h2
        exact h2
      · rw [one_smul] at hAu'
        have h1 : A (A u) = u := by
          rw [hAu', map_add, ih' z' hz', hAu', ← add_assoc, hadd, zero_add]
        have h2 := hA3 u
        rw [h1] at h2
        exact h2
    rw [map_add, map_smul, hfu, ih' z hz]

end Flag

section Quotient

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem trivial_on_quotient_of_perfect (hK : Nat.card K = 2) (U : Subgroup (V ≃ₗ[K] V))
    (hU : ⁅U, U⁆ = U) {W N : Submodule K V} (hWN : W ≤ N)
    (hdim : Module.finrank K N = Module.finrank K W + 2)
    (hW : ∀ g ∈ U, ∀ w ∈ W, g w ∈ W) (hN : ∀ g ∈ U, ∀ u ∈ N, g u ∈ N) :
    ∀ g ∈ U, ∀ u ∈ N, g u - u ∈ W := by
  classical
  have : Finite V := Module.finite_of_finite K
  let ρ : Representation K U V :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom).comp U.subtype
  have hρ : ∀ (g : U) (v : V), ρ g v = (g : V ≃ₗ[K] V) v := fun g v => rfl
  let ρN : Representation K U N :=
    ρ.subrepresentation N (fun g u hu => hN g g.2 u hu)
  let W' : Submodule K N := W.comap N.subtype
  let ρT : Representation K U (N ⧸ W') :=
    ρN.quotient W' (fun g u hu => hW g g.2 u hu)
  have hW'dim : Module.finrank K W' = Module.finrank K W :=
    (Submodule.comapSubtypeEquivOfLe hWN).finrank_eq
  have hTdim : Module.finrank K (N ⧸ W') = 2 := by
    have := Submodule.finrank_quotient_add_finrank W'
    omega
  have hTcard : Nat.card (N ⧸ W') ≤ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := K), hK, hTdim]; norm_num
  let ψ : U →* Equiv.Perm (N ⧸ W') :=
    { toFun := fun g =>
        { toFun := fun t => ρT g t
          invFun := fun t => ρT g⁻¹ t
          left_inv := fun t => by
            show ρT g⁻¹ (ρT g t) = t
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
          right_inv := fun t => by
            show ρT g (ρT g⁻¹ t) = t
            rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl }
      map_one' := by ext t; simp
      map_mul' := fun g h => by ext t; simp [map_mul] }
  have : Finite N := inferInstance
  have : Finite (N ⧸ W') := Quotient.finite _
  have hsolv : Group.IsSolvable (Equiv.Perm (N ⧸ W')) := Equiv.Perm.isSolvable hTcard
  have hperf : Group.IsPerfect ↥U := Subgroup.isPerfect_iff.mpr hU
  have hrange : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
  have hψ1 : ∀ g : U, ψ g = 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hg⟩ := hcon
    have : Nontrivial ψ.range := ⟨⟨⟨ψ g, g, rfl⟩, 1, fun h => hg (congrArg Subtype.val h)⟩⟩
    exact Group.IsPerfect.not_isSolvable (G := ψ.range) inferInstance
  intro g hg u hu
  have h1 := congrArg (fun e : Equiv.Perm (N ⧸ W') => e (Submodule.Quotient.mk ⟨u, hu⟩))
    (hψ1 ⟨g, hg⟩)
  simp only [ψ, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk, Equiv.Perm.coe_one, id_eq] at h1
  have h2 : ρT ⟨g, hg⟩ (Submodule.Quotient.mk ⟨u, hu⟩) =
      Submodule.Quotient.mk ⟨g u, hN g hg u hu⟩ := rfl
  rw [h2, Submodule.Quotient.eq] at h1
  exact h1

end Quotient

end CFSG.HardMathSupport.Curtis.UnitaryLevi
