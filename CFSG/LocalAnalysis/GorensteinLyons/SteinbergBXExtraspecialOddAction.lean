module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXSymplecticCentralProduct

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup
open scoped commutatorElement IsMulCommutative

open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)

section Extraspecial

variable {P : Type*} [Group P]

theorem commPairHyp_of_extraspecial [Finite P] (hP : IsExtraspecialPGroup 2 P) {z : P}
    (hz : center P = zpowers z) : CommPairHyp P z := by
  obtain ⟨hP2, hcomm, hfrat, hcard⟩ := hP
  have hzo : orderOf z = 2 := by rw [← Nat.card_zpowers, ← hz, hcard]
  refine ⟨hz ▸ mem_zpowers z, hzo, fun a b => ?_, fun a => ?_⟩
  · refine eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hzo ?_
    rw [← hz, ← hcomm, _root_.commutator_def]
    exact commutator_mem_commutator (mem_top a) (mem_top b)
  · rw [← hfrat, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact (CFSG.GroupTheory.frattini_elementary_quotient (p := 2) hP2).2.2.1 _

theorem mulAut_apply_eq_of_center_eq {z : P} (hz : center P = zpowers z) (hzo : orderOf z = 2)
    (σ : MulAut P) : σ z = z := by
  have hzc : z ∈ center P := hz ▸ mem_zpowers z
  have hσz : σ z ∈ center P := by
    rw [mem_center_iff]
    intro g
    have h1 := mem_center_iff.mp hzc (σ.symm g)
    calc g * σ z = σ (σ.symm g * z) := by rw [map_mul, MulEquiv.apply_symm_apply]
      _ = σ (z * σ.symm g) := by rw [h1]
      _ = σ z * g := by rw [map_mul, MulEquiv.apply_symm_apply]
  rw [hz] at hσz
  rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hzo hσz with h | h
  · exfalso
    have : z = 1 := σ.injective (by rw [h, map_one])
    rw [this, orderOf_one] at hzo
    exact absurd hzo (by norm_num)
  · exact h

@[expose] noncomputable def sqVal (z : P) (u : P ⧸ center P) : ZMod 2 :=
  zlog z (Quotient.out u ^ 2)

namespace CommPairHyp

variable {z : P} (H : CommPairHyp P z)
include H

theorem sqVal_mk (hz : center P = zpowers z) (x : P) :
    sqVal z (x : P ⧸ center P) = zlog z (x ^ 2) := by
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul (center P) x
  have hs2 : (s : P) ^ 2 = 1 := by
    have hs' : (s : P) ∈ zpowers z := hz ▸ s.2
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two H.orderOf_eq hs' with h | h <;> rw [h]
    · exact one_pow 2
    · rw [pow_two]; exact H.z_mul_z
  rw [sqVal, hs, Commute.mul_pow (mem_center_iff.mp s.2 x) 2, hs2, mul_one]

theorem sq_eq_zpow_sqVal (hz : center P = zpowers z) (x : P) :
    x ^ 2 = z ^ (sqVal z (x : P ⧸ center P)).val := by
  rw [H.sqVal_mk hz]
  exact H.eq_zpow_zlog (eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two H.orderOf_eq
    (hz ▸ H.sq_mem_center x))

theorem sqVal_mul (hz : center P = zpowers z) (u v : P ⧸ center P) :
    sqVal z (u * v) = sqVal z u + sqVal z v + commVal z u v := by
  induction u using QuotientGroup.induction_on with | H x =>
  induction v using QuotientGroup.induction_on with | H y =>
  have hp : ∀ t : P, t ^ 2 = 1 ∨ t ^ 2 = z := fun t =>
    eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two H.orderOf_eq (hz ▸ H.sq_mem_center t)
  rw [← QuotientGroup.mk_mul, H.sqVal_mk hz, H.sqVal_mk hz, H.sqVal_mk hz, H.commVal_mk,
    H.sq_mul, H.zlog_mul (H.pair_mul (H.comm_pair y x) (hp x)) (hp y),
    H.zlog_mul (H.comm_pair y x) (hp x), H.comm_symm]
  ring

end CommPairHyp

end Extraspecial

end CFSG.LocalAnalysis.GorensteinLyons
