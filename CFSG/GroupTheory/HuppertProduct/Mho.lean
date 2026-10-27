module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory.HuppertProduct

variable {G : Type*} [Group G]

@[expose] def mho (S : Subgroup G) (n : ℕ) : Subgroup G :=
  Subgroup.closure {z | ∃ g ∈ S, z = g ^ n}

theorem pow_mem_mho {S : Subgroup G} {n : ℕ} {g : G} (hg : g ∈ S) : g ^ n ∈ mho S n :=
  Subgroup.subset_closure ⟨g, hg, rfl⟩

theorem mho_le_of_forall {S K : Subgroup G} {n : ℕ} (h : ∀ g ∈ S, g ^ n ∈ K) : mho S n ≤ K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨g, hg, rfl⟩
  exact h g hg

theorem mho_le (S : Subgroup G) (n : ℕ) : mho S n ≤ S :=
  mho_le_of_forall fun _ hg => S.pow_mem hg n

theorem conj_mem_mho {S : Subgroup G} {n : ℕ} {h : G} (hh : ∀ s ∈ S, h * s * h⁻¹ ∈ S) {x : G}
    (hx : x ∈ mho S n) : h * x * h⁻¹ ∈ mho S n := by
  have hle : mho S n ≤ (mho S n).comap (MulAut.conj h).toMonoidHom := by
    refine mho_le_of_forall fun g hg => ?_
    change h * g ^ n * h⁻¹ ∈ mho S n
    have : h * g ^ n * h⁻¹ = (h * g * h⁻¹) ^ n := by
      simp [conj_pow]
    rw [this]
    exact pow_mem_mho (hh g hg)
  exact hle hx

theorem mho_le_normalizer (S : Subgroup G) (n : ℕ) :
    S ≤ Subgroup.normalizer (mho S n : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact conj_mem_mho (fun s hs => S.mul_mem (S.mul_mem hh hs) (S.inv_mem hh)) hx
  · intro hx
    have hh' : h⁻¹ ∈ S := S.inv_mem hh
    have := conj_mem_mho (n := n) (h := h⁻¹)
      (fun s hs => S.mul_mem (S.mul_mem hh' hs) (S.inv_mem hh')) hx
    simpa [mul_assoc] using this

end CFSG.GroupTheory.HuppertProduct
