module

public import CFSG.HardMathSupport.GuralnickMalle.CyclicTwoDecomp

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open Module
open scoped TensorProduct

variable {K : Type*} [Field K] [CharP K 2]

@[expose] noncomputable def iterFixed {V : Type*} [AddCommGroup V] [Module K V] {r : ℕ}
    (T : Fin r → V ≃ₗ[K] V) (i : ℕ) : Submodule K V :=
  ⨅ j : {j : Fin r // (j : ℕ) < i}, LinearMap.ker ((T j.1 : V →ₗ[K] V) - 1)

@[expose] noncomputable def tensorFixed {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {r : ℕ}
    (T : Fin r → V ≃ₗ[K] V) (S : Fin r → W ≃ₗ[K] W) : Submodule K (V ⊗[K] W) :=
  ⨅ i : Fin r, LinearMap.ker (TensorProduct.map (T i : V →ₗ[K] V) (S i : W →ₗ[K] W) - 1)

theorem mem_iterFixed {V : Type*} [AddCommGroup V] [Module K V] {r : ℕ}
    {T : Fin r → V ≃ₗ[K] V} {i : ℕ} {v : V} :
    v ∈ iterFixed T i ↔ ∀ j : Fin r, (j : ℕ) < i → T j v = v := by
  simp only [iterFixed, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    Module.End.one_apply, sub_eq_zero, Subtype.forall, LinearEquiv.coe_coe]

theorem iterFixed_zero {V : Type*} [AddCommGroup V] [Module K V] {r : ℕ}
    (T : Fin r → V ≃ₗ[K] V) : iterFixed T 0 = ⊤ := by
  ext v
  simp [mem_iterFixed]

theorem iterFixed_succ {V : Type*} [AddCommGroup V] [Module K V] {r : ℕ}
    {T : Fin r → V ≃ₗ[K] V} {i : ℕ} (hi : i < r) :
    iterFixed T (i + 1) = iterFixed T i ⊓ LinearMap.ker ((T ⟨i, hi⟩ : V →ₗ[K] V) - 1) := by
  ext v
  rw [mem_iterFixed, Submodule.mem_inf, mem_iterFixed, LinearMap.mem_ker,
    LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  constructor
  · intro h
    exact ⟨fun j hj => h j (by omega), h ⟨i, hi⟩ (by simp)⟩
  · rintro ⟨h1, h2⟩ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
    · exact h1 j hj'
    · have hji : j = ⟨i, hi⟩ := Fin.ext hj'
      rw [hji]
      exact h2

theorem iterFixed_castSucc {V : Type*} [AddCommGroup V] [Module K V] {r : ℕ}
    (T : Fin (r + 1) → V ≃ₗ[K] V) {i : ℕ} (hi : i ≤ r) :
    iterFixed (fun j : Fin r => T (Fin.castSucc j)) i = iterFixed T i := by
  ext v
  rw [mem_iterFixed, mem_iterFixed]
  constructor
  · intro h j hj
    have hj' : (j : ℕ) < r := by omega
    have h' := h ⟨j, hj'⟩ hj
    simpa using h'
  · intro h j hj
    exact h (Fin.castSucc j) (by simpa using hj)

theorem iInf_fin_succ {M : Type*} [AddCommGroup M] [Module K M] {r : ℕ}
    (p : Fin (r + 1) → Submodule K M) :
    (⨅ i, p i) = (⨅ i : Fin r, p (Fin.castSucc i)) ⊓ p (Fin.last r) := by
  ext x
  simp only [Submodule.mem_inf, Submodule.mem_iInf]
  exact ⟨fun h => ⟨fun i => h _, h _⟩, fun h i => by
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact h.1 j
    · exact h.2⟩

theorem tensorFixed_castSucc {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {r : ℕ}
    (T : Fin (r + 1) → V ≃ₗ[K] V) (S : Fin (r + 1) → W ≃ₗ[K] W) :
    tensorFixed T S =
      tensorFixed (fun j : Fin r => T (Fin.castSucc j))
          (fun j : Fin r => S (Fin.castSucc j)) ⊓
        LinearMap.ker
          (TensorProduct.map (T (Fin.last r) : V →ₗ[K] V)
            (S (Fin.last r) : W →ₗ[K] W) - 1) := by
  rw [tensorFixed, tensorFixed]
  exact iInf_fin_succ _

theorem restrict_comp_self {V : Type*} [AddCommGroup V] [Module K V]
    {f : V →ₗ[K] V} (hf : f.comp f = 1) {A : Submodule K V}
    (hA : ∀ x ∈ A, f x ∈ A) : (f.restrict hA).comp (f.restrict hA) = 1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [LinearMap.comp_apply, LinearMap.coe_restrict_apply, Module.End.one_apply]
  exact congrArg (fun g : V →ₗ[K] V => g (x : V)) hf

theorem finrank_ker_restrict_sub_one {M : Type*} [AddCommGroup M] [Module K M]
    {f : M →ₗ[K] M} {A : Submodule K M} (hA : ∀ x ∈ A, f x ∈ A) :
    Module.finrank K (LinearMap.ker ((f.restrict hA) - 1)) =
      Module.finrank K ↥(A ⊓ LinearMap.ker (f - 1)) := by
  have hsub : ((f.restrict hA) - 1 : A →ₗ[K] A) =
      (f - 1).restrict (fun x hx => A.sub_mem (hA x hx) hx) := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp [LinearMap.restrict_apply, LinearMap.sub_apply]
  rw [hsub, LinearMap.ker_restrict]
  exact (Submodule.finrank_map_subtype_eq A
    ((LinearMap.ker (f - 1)).comap A.subtype)).symm.trans
      (by rw [Submodule.map_comap_subtype])

end CFSG.HardMathSupport.GuralnickMalle
