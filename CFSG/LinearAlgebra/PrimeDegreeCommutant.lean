module

public import CFSG.RankThree.SubgroupLists.SchurCommutant
public import Mathlib.FieldTheory.Finite.GaloisField

public noncomputable section

namespace CFSG.LinearAlgebra

open Matrix CFSG.RankThree.SubgroupLists CFSG.RepresentationTheory

variable {K : Type*} [Field K] [Finite K] {n : ℕ}

omit [Finite K] in
theorem mem_commutant_of_mem_of_isCyclic {H : Subgroup (GL (Fin n) K)} (hHcyc : IsCyclic H)
    {g : GL (Fin n) K} (hg : g ∈ H) :
    (g : Matrix (Fin n) (Fin n) K) ∈ commutant H := by
  rw [mem_commutant]
  intro h hh
  exact congrArg (fun u : H => ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (IsCyclic.commGroup.mul_comm (⟨h, hh⟩ : H) (⟨g, hg⟩ : H))

theorem finrank_commutant_eq_of_prime_of_cyclic_irreducible (hn : n.Prime)
    {H : Subgroup (GL (Fin n) K)} (hHirr : IsIrreducibleMatrixRep H.subtype)
    (hHcyc : IsCyclic H) :
    Module.finrank K (commutant H) = n := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, hn.pos⟩⟩
  have hHOn : IsIrreducibleOn H := isIrreducibleOn_iff.mpr hHirr
  have hdvd : Module.finrank K (commutant H) ∣ n := by
    simpa [Fintype.card_fin] using finrank_commutant_dvd hHOn
  rcases (Nat.dvd_prime hn).mp hdvd with h1 | hfull
  · exfalso
    have hbot : commutant H = ⊥ := Subalgebra.finrank_eq_one_iff.mp h1
    refine not_irreducible_of_forall_scalar hn.two_le (G := H) (fun g hg => ?_) hHirr
    have hmem : (g : Matrix (Fin n) (Fin n) K) ∈ commutant H :=
      mem_commutant_of_mem_of_isCyclic hHcyc hg
    rw [hbot, Algebra.mem_bot] at hmem
    obtain ⟨a, ha⟩ := hmem
    refine ⟨a, ?_⟩
    rw [← ha]
    simp [Matrix.algebraMap_eq_diagonal]
  · exact hfull

theorem natCard_commutant_eq_pow_of_prime_of_cyclic_irreducible (hn : n.Prime)
    {H : Subgroup (GL (Fin n) K)} (hHirr : IsIrreducibleMatrixRep H.subtype)
    (hHcyc : IsCyclic H) :
    Nat.card (commutant H) = Nat.card K ^ n := by
  rw [Module.natCard_eq_pow_finrank (K := K) (V := commutant H),
    finrank_commutant_eq_of_prime_of_cyclic_irreducible hn hHirr hHcyc]

theorem natCard_algEquiv_commutant_eq_of_prime_of_cyclic_irreducible (hn : n.Prime)
    {H : Subgroup (GL (Fin n) K)} (hHirr : IsIrreducibleMatrixRep H.subtype)
    (hHcyc : IsCyclic H) :
    Nat.card (commutant H ≃ₐ[K] commutant H) = n := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, hn.pos⟩⟩
  letI : Field (commutant H) := commutantField (isIrreducibleOn_iff.mpr hHirr)
  let : Finite (Matrix (Fin n) (Fin n) K) := inferInstance
  let : Finite (commutant H) := inferInstance
  rw [IsGalois.card_aut_eq_finrank K (commutant H),
    finrank_commutant_eq_of_prime_of_cyclic_irreducible hn hHirr hHcyc]

end CFSG.LinearAlgebra
