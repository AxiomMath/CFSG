module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.OuterDerived

open Matrix CFSG.ClassicalGroups.UnitaryFlag UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem isCyclic_map_mk_and_card_dvd {Y : Type*} [Group Y] (I D : Subgroup Y) [I.Normal]
    (h : IsCyclic (D ⧸ I.subgroupOf D)) :
    IsCyclic (D.map (QuotientGroup.mk' I)) ∧
      Nat.card (D.map (QuotientGroup.mk' I)) ∣ Nat.card (D ⧸ I.subgroupOf D) := by
  set ρ := (QuotientGroup.mk' I).subgroupMap D
  have hle : I.subgroupOf D ≤ ρ.ker := fun x hx => by
    rw [MonoidHom.mem_ker]
    refine Subtype.ext ?_
    change QuotientGroup.mk' I (x : Y) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hx
  have hsurj : Function.Surjective (QuotientGroup.lift (I.subgroupOf D) ρ hle) := fun y => by
    obtain ⟨x, rfl⟩ := (QuotientGroup.mk' I).subgroupMap_surjective D y
    exact ⟨x, QuotientGroup.lift_mk _ _ _⟩
  exact ⟨isCyclic_of_surjective _ hsurj, Subgroup.card_dvd_of_surjective hsurj⟩

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem commutator_mem_primeFormD (h : UnitaryFieldData p f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ p ^ f = 2))
    (α β : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
    α * β * α⁻¹ * β⁻¹ ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have : Finite K := h.finite
  have : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  obtain ⟨-, -, -, -, -, -, -, hFker, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h isPrimeFormGram_one hn hq
  set F := primeFormFieldFactor h (isPrimeFormGram_one (n := n) (K := K)) hn hq
  rw [← hFker, MonoidHom.mem_ker, map_mul F, map_mul F, map_mul F, map_inv F, map_inv F,
    (IsCyclic.isMulCommutative (α := K ≃+* K)).is_comm.comm (F α) (F β), mul_inv_cancel_right,
    mul_inv_cancel]

theorem exists_unitary_outer_diagonal (h : UnitaryFieldData p f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ p ^ f = 2)) :
    ∃ N : Subgroup (Outer (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))),
      IsCyclic N ∧ Nat.card N ∣ Nat.gcd n (p ^ f + 1) ∧
      ∀ a b : Outer (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
        a * b * a⁻¹ * b⁻¹ ∈ N := by
  obtain ⟨-, hcyc, hcard, -⟩ := unitary_full_diagonal_outer_order h hn hq
  obtain ⟨hNcyc, hNcard⟩ := isCyclic_map_mk_and_card_dvd _ _ hcyc
  refine ⟨_, hNcyc, hNcard.trans (dvd_of_eq hcard), fun a b => ?_⟩
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨β, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨_, commutator_mem_primeFormD h hn hq α β, rfl⟩

end CFSG.LocalAnalysis.ComponentInitial.OuterDerived
