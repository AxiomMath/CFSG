module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Partner
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotNeighbourParam

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Coset

variable {f : ℕ} {K' : Type} [Field K'] (h : UnitaryFieldData 2 f K') {m : ℕ}

theorem ringEquiv_mul_barRingEquiv_comm (ψ : K' ≃+* K') :
    ψ * UnitaryPilot.barRingEquiv h = UnitaryPilot.barRingEquiv h * ψ := by
  ext x
  change ψ (UnitaryPilot.barRingEquiv h x) = UnitaryPilot.barRingEquiv h (ψ x)
  rw [UnitaryPilot.barRingEquiv_apply, UnitaryPilot.barRingEquiv_apply, h.bar_apply,
    h.bar_apply, map_pow]

theorem cosetInnConjInput_fieldBar (C : GL (Fin m) K') (hC : IsPrimeFormGram C) (hm : 3 ≤ m)
    (hq : ¬(m = 3 ∧ 2 ^ f = 2)) :
    CosetInnConjInput (primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h)) := by
  intro y _ ⟨β, hβ⟩
  set fb := primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h) with hfb
  obtain ⟨⟨A, ψ⟩, rfl⟩ := primeFormPsi_surjective h hC hm hq β
  rw [primeFormPsi_apply] at hβ
  set d := primeFormConjHom h (C : Matrix (Fin m) (Fin m) K') A with hd
  have hψ : primeFormFieldHom h hC ψ * fb = fb * primeFormFieldHom h hC ψ := by
    rw [hfb, ← map_mul, ← map_mul, ringEquiv_mul_barRingEquiv_comm]
  have h1 : MulAut.conj y * fb = d * fb * d⁻¹ := by
    have h2 : MulAut.conj y * fb * (d * primeFormFieldHom h hC ψ) =
        d * primeFormFieldHom h hC ψ * fb := hβ.symm
    calc MulAut.conj y * fb
        = (MulAut.conj y * fb * (d * primeFormFieldHom h hC ψ)) *
            (primeFormFieldHom h hC ψ)⁻¹ * d⁻¹ := by group
      _ = d * (primeFormFieldHom h hC ψ * fb) * (primeFormFieldHom h hC ψ)⁻¹ * d⁻¹ := by
          rw [h2]
          group
      _ = d * fb * d⁻¹ := by
          rw [hψ]
          group
  have hcoset : d * fb * d⁻¹ * fb⁻¹ ∈ inner (primeFormP h (C : Matrix (Fin m) (Fin m) K')) := by
    rw [← h1, mul_inv_cancel_right]
    exact ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := exists_conj_eq_of_fieldBar_conj_mem_coset h C hC hm
    (fun x => UnitaryPilot.barRingEquiv_apply h x) ⟨A, rfl⟩ hcoset
  exact ⟨z, h1.trans hz⟩

end Coset

section Card

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup) in
theorem card_matrixIsometryGroup_one_eq {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    (hn : 2 ≤ n) (p : Fin n) :
    Nat.card (matrixIsometryGroup ((1 : GL (Fin (2 * n)) F) :
      Matrix (Fin (2 * n)) (Fin (2 * n)) F)) =
        Nat.card (centralizer ({siegDiag F p 1} : Set (StatedSp n F))) := by
  obtain ⟨H', hconj, -⟩ := exists_normalForm_conj_siegDiag hf hF hn p
  have hc : Nat.card (fixedSubgroup (LinearFlag.conjAut (2 * n) F H' *
      LinearFlag.dualAut (2 * n) F * (LinearFlag.conjAut (2 * n) F H')⁻¹)) =
        Nat.card (centralizer ({siegDiag F p 1} : Set (StatedSp n F))) := by
    rw [← hconj, fixedSubgroup_conj_siegDiag_mul_graph hf hF hn p,
      Subgroup.card_map_of_injective (spModelPSL_injective (by omega))]
  rw [← LinearPilot.mulAut_congr_eq_mul, LinearPilot.card_fixedSubgroup_congr] at hc
  obtain ⟨E⟩ := CFSG.ComponentClassification.CatLeafProof.nonempty_fixed_canonical_equiv hf hF
    (by omega) (1 : GL (Fin (2 * n)) F) (Or.inl rfl)
  have hδ : LinearFlag.conjAut (2 * n) F 1 * LinearFlag.dualAut (2 * n) F =
      LinearFlag.dualAut (2 * n) F := by rw [map_one, one_mul]
  rw [hδ] at E
  rw [← hc, Nat.card_congr E.toEquiv]

end Card

end CFSG.SeitzReduction.SymplecticPilot
