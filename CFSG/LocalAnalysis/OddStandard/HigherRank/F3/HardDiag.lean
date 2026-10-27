module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSwap
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardCentral

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.ComponentClassification.HarrisLit

theorem ker_swapDiag_le_center {X : Type} [Group X] {K : Subgroup X} {t : X}
    (hc : K ≤ centralizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup X) : Set X)) :
    (swapDiag K t hc).ker ≤ center ↥K := by
  intro k hk
  rw [MonoidHom.mem_ker] at hk
  have hk1 : (k : X) * MulAut.conj t (k : X) = 1 := by
    rw [← swapDiag_apply K t hc k]; exact hk
  have hk' : (k : X)⁻¹ = MulAut.conj t (k : X) := inv_eq_of_mul_eq_one_right hk1
  have hmem : (k : X)⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom := ⟨k, k.2, hk'.symm⟩
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have h0 : Commute ((k : X)⁻¹) (y : X) := mem_centralizer_iff.mp (hc y.2) _ hmem
  exact (Commute.inv_left_iff.mp h0).symm.eq

theorem isQuasisimple_range_swapDiag {X : Type} [Group X] {K : Subgroup X} {t : X}
    (hc : K ≤ centralizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup X) : Set X))
    (hK : CFSG.IsQuasisimple ↥K) : CFSG.IsQuasisimple ↥(swapDiag K t hc).range := by
  have hker : (swapDiag K t hc).rangeRestrict.ker ≤ center ↥K := by
    rw [MonoidHom.ker_rangeRestrict]
    exact ker_swapDiag_le_center hc
  exact isQuasisimple_of_central_ker hK (swapDiag K t hc).rangeRestrict
    (swapDiag K t hc).rangeRestrict_surjective hker

theorem nonempty_quotCenter_equiv_swapDiag {X : Type} [Group X] {K : Subgroup X} {t : X}
    (hc : K ≤ centralizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup X) : Set X))
    (hK : CFSG.IsQuasisimple ↥K) :
    Nonempty (↥K ⧸ center ↥K ≃*
      ↥(swapDiag K t hc).range ⧸ center ↥(swapDiag K t hc).range) := by
  have hker : (swapDiag K t hc).rangeRestrict.ker ≤ center ↥K := by
    rw [MonoidHom.ker_rangeRestrict]
    exact ker_swapDiag_le_center hc
  exact nonempty_quotCenter_equiv_of_central_ker hK (swapDiag K t hc).rangeRestrict
    (swapDiag K t hc).rangeRestrict_surjective hker

theorem exists_center_swapDiag {X : Type} [Group X] {K : Subgroup X} {t : X}
    (hc : K ≤ centralizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup X) : Set X))
    (hK : CFSG.IsQuasisimple ↥K) {z : X} (hz : z ∈ (swapDiag K t hc).range)
    (hzc : ∀ y ∈ (swapDiag K t hc).range, y * z = z * y) :
    ∃ ν : ↥K, ν ∈ center ↥K ∧ swapDiag K t hc ν = z := by
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hz
  have hker : (swapDiag K t hc).rangeRestrict.ker ≤ center ↥K := by
    rw [MonoidHom.ker_rangeRestrict]
    exact ker_swapDiag_le_center hc
  refine ⟨k, mem_center_of_map_mem_center hK (swapDiag K t hc).rangeRestrict hker ?_, hk⟩
  refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
  show (g : X) * (swapDiag K t hc k) = (swapDiag K t hc k) * (g : X)
  rw [hk]
  exact hzc (g : X) g.2

end CFSG.OddStandard.HigherRank.F3
