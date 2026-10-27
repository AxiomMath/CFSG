module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4PerfApply
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvSpor
public import CFSG.LocalAnalysis.OddStandard.MathieuInvolution
public import Certificates.Certificate5155

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.Sporadic.Schreier CFSG.OddStandard
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open scoped commutatorElement

theorem perfect_of_commProdOK {n : ℕ} (S : List (Equiv.Perm (Fin n)))
    (W : List (List (List ℤ × List ℤ))) (h : Certificates.CommProd.commProdOK S W = true) :
    ⁅Subgroup.closure {g | g ∈ S}, Subgroup.closure {g | g ∈ S}⁆ = Subgroup.closure {g | g ∈ S} := by
  set Q : Subgroup (Equiv.Perm (Fin n)) := Subgroup.closure {g | g ∈ S} with hQ
  have hword : ∀ w : List ℤ, evalCodes S w ∈ Q := by
    intro w
    induction w with
    | nil => exact Q.one_mem
    | cons z w ih =>
      refine Q.mul_mem ?_ ih
      by_cases hz : 0 < z
      · simp only [hz, ↓reduceIte]
        by_cases hlt : z.toNat - 1 < S.length
        · exact Subgroup.subset_closure (by
            rw [List.getD_eq_getElem _ _ hlt]
            exact List.getElem_mem _)
        · rw [List.getD_eq_default _ _ (by omega)]
          exact Q.one_mem
      · simp only [hz, ↓reduceIte]
        refine Q.inv_mem ?_
        by_cases hlt : (-z).toNat - 1 < S.length
        · exact Subgroup.subset_closure (by
            rw [List.getD_eq_getElem _ _ hlt]
            exact List.getElem_mem _)
        · rw [List.getD_eq_default _ _ (by omega)]
          exact Q.one_mem
  have hcomm : ∀ p : List ℤ × List ℤ, Certificates.CommProd.commVal S p ∈ ⁅Q, Q⁆ := by
    intro p
    have := Subgroup.commutator_mem_commutator (hword p.1) (hword p.2)
    rw [commutatorElement_def] at this
    exact this
  have hprod : ∀ l : List (List ℤ × List ℤ), Certificates.CommProd.prodComm S l ∈ ⁅Q, Q⁆ := by
    intro l
    induction l with
    | nil => exact (⁅Q, Q⁆).one_mem
    | cons p r ih => exact (⁅Q, Q⁆).mul_mem (hcomm p) ih
  apply le_antisymm
  · exact Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact Q.mul_mem (Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem ha)) (Q.inv_mem hb)
  · rw [hQ, Subgroup.closure_le]
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    have hall := List.all_eq_true.1 (Bool.and_eq_true_iff.1 h).2 i (List.mem_range.2 hi)
    have hi' := of_decide_eq_true hall
    rw [List.getD_eq_getElem _ _ hi] at hi'
    rw [hi']
    exact hprod _

theorem m23_inv_centralizer_data :
    ∀ u ∈ NativeSporadic.M23, orderOf u = 2 →
      ⁅centralizerIn NativeSporadic.M23 u, centralizerIn NativeSporadic.M23 u⁆ =
          centralizerIn NativeSporadic.M23 u ∧
        Nat.card ↥(centralizerIn NativeSporadic.M23 u) = 2688 := by
  obtain ⟨hrecs, -, hcover⟩ := m23_innerRecordsValid
  intro u hu hu2
  obtain ⟨r, hr, g, hg, hug⟩ := hcover u hu hu2
  have hr1 : r = m23Rec1 := by simpa [m23Records] using hr
  subst hr1
  obtain ⟨-, -, -, hcard, -, hclos, -⟩ := hrecs _ hr
  have hperf0 : ⁅centralizerIn NativeSporadic.M23 m23Rec1.representative,
      centralizerIn NativeSporadic.M23 m23Rec1.representative⁆ =
      centralizerIn NativeSporadic.M23 m23Rec1.representative := by
    rw [← hclos]
    exact perfect_of_commProdOK m23Cg1 Certificates.CommProd.m23CentPerfWit
      Certificates.certificate5155
  refine ⟨?_, ?_⟩
  · have h2 := GHInv.commutator_centralizerIn_conj hg hperf0
    rw [← hug] at h2
    exact h2
  · rw [GHInv.card_centralizerIn_eq_of_mem_conjClass NativeSporadic.M23 (t := m23Rec1.representative)
      ⟨g, hg, hug⟩]
    exact hcard

theorem ivk73_m23 :
    Ivk73Empty (fun X _ => NativeSporadic.IsSporadic X .M23) := by
  refine ivk73_empty_of_perfect_centralizers (P := fun X _ => NativeSporadic.IsSporadic X .M23) ?_ ?_
  · intro L _ _ hL
    obtain ⟨e⟩ := hL
    have e' : L ≃* NativeSporadic.M23 := e
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
    exact Sporadic.Schreier.at_m23_schreier.1
  · intro L _ _ hL y hy2 hy1
    obtain ⟨e⟩ := hL
    have e' : L ≃* NativeSporadic.M23 := e
    have hord : orderOf ((e' y : NativeSporadic.M23) : Equiv.Perm (Fin 23)) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
    obtain ⟨hperf, hcard⟩ := m23_inv_centralizer_data _ (e' y).2 hord
    refine ⟨GHInv.isPerfect_centralizer_of_equiv NativeSporadic.M23 e' y hperf, Or.inr ?_⟩
    rw [GHInv.card_centralizer_eq_centralizerIn NativeSporadic.M23 e' y]
    exact hcard

end CFSG.GH74.GLS.IVK
