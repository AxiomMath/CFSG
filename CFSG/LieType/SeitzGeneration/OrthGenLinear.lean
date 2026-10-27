module

public import CFSG.LieType.SeitzGeneration.OrthEvenSingular

public section

namespace CFSG.LieType.SeitzGeneration.OrthBlk

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [Finite K] in
theorem exists_perp_not_perp_two {S : Submodule K V} (hS : PolarNondegOn Q S) {x y₁ y₂ : V}
    (hx : x ∈ S) (hy₁ : y₁ ∈ S) (hy₂ : y₂ ∈ S) (hind : ∀ c₁ c₂ : K, x ≠ c₁ • y₁ + c₂ • y₂) :
    ∃ t ∈ S, polar Q t y₁ = 0 ∧ polar Q t y₂ = 0 ∧ polar Q t x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  let L : V →ₗ[K] V →ₗ[K] K := (polarBilin Q).flip
  let Lx : ↥S →ₗ[K] K := (L x).comp S.subtype
  let ℓ : Fin 2 → ↥S →ₗ[K] K := ![(L y₁).comp S.subtype, (L y₂).comp S.subtype]
  have hL : ∀ (y : V) (t : ↥S), L y t = polar Q (t : V) y := fun y t => by
    simp [L, polarBilin_apply_apply]
  have hker : ⨅ i, LinearMap.ker (ℓ i) ≤ LinearMap.ker Lx := by
    intro t ht
    have h1 : ℓ 0 t = 0 := LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp ht 0)
    have h2 : ℓ 1 t = 0 := LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp ht 1)
    have e1 : polar Q (t : V) y₁ = 0 := by
      have : L y₁ t = 0 := h1
      rwa [hL] at this
    have e2 : polar Q (t : V) y₂ = 0 := by
      have : L y₂ t = 0 := h2
      rwa [hL] at this
    have : L x t = 0 := by rw [hL]; exact hcon t t.2 e1 e2
    exact this
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1
    (FiniteDimensional.mem_span_of_iInf_ker_le_ker (L := ℓ) hker)
  have hall : ∀ t : ↥S, polar Q (t : V) (x - (c 0 • y₁ + c 1 • y₂)) = 0 := by
    intro t
    have := congrArg (fun f : ↥S →ₗ[K] K => f t) hc
    simp only [Fin.sum_univ_two, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at this
    have h0 : ℓ 0 t = polar Q (t : V) y₁ := hL y₁ t
    have h1 : ℓ 1 t = polar Q (t : V) y₂ := hL y₂ t
    have hx' : Lx t = polar Q (t : V) x := hL x t
    rw [polar_sub_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, ← h0, ← h1,
      ← hx', ← this]
    ring
  have : x - (c 0 • y₁ + c 1 • y₂) = 0 :=
    hS _ (S.sub_mem hx (S.add_mem (S.smul_mem _ hy₁) (S.smul_mem _ hy₂))) fun y hy => by
      rw [polar_comm]
      exact hall ⟨y, hy⟩
  exact hind (c 0) (c 1) (sub_eq_zero.mp this)

theorem exists_singular_in_kernel_fin {n : ℕ} {S : Submodule K V} (h : n + 3 ≤ finrank K S)
    (f : Fin n → V →ₗ[K] K) : ∃ s ∈ S, s ≠ 0 ∧ Q s = 0 ∧ ∀ i, f i s = 0 := by
  let Φ : ↥S →ₗ[K] (Fin n → K) := LinearMap.pi fun i => (f i).comp S.subtype
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  have hrange : finrank K Φ.range ≤ n := by
    have := Submodule.finrank_le Φ.range
    simpa using this
  set U : Submodule K V := (LinearMap.ker Φ).map S.subtype with hU
  have hUdim : 3 ≤ finrank K U := by
    have hinj : Function.Injective S.subtype := S.injective_subtype
    have : finrank K U = finrank K (LinearMap.ker Φ) :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective S.subtype hinj (LinearMap.ker Φ))).symm
    omega
  obtain ⟨s, hsU, hs0, hsQ⟩ := exists_singular_of_three_le_any (Q := Q) hUdim
  obtain ⟨s', hs', rfl⟩ := Submodule.mem_map.mp hsU
  refine ⟨(s' : V), s'.2, hs0, hsQ, fun i => ?_⟩
  have := congrFun (LinearMap.mem_ker.mp hs') i
  simpa [Φ] using this

end CFSG.LieType.SeitzGeneration.OrthBlk
