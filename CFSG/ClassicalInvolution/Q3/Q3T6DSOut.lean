module

public import CFSG.ClassicalInvolution.Asc77.AscT3SOut
public import CFSG.ClassicalInvolution.Q3.Q3T6FaAut
public import CFSG.ClassicalInvolution.Q3.Q3T6AutInn

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.T3CII.T3R CFSG.RankThree.PartTwo.KFacts
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

section Out

theorem isInnerAut_commutator_of_equiv_sl2_three {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 3) {P : Type*} [Group P] (e : P ≃* SL(2, F)) (α β : MulAut P) :
    IsInnerAut (α * β * α⁻¹ * β⁻¹) := by
  obtain ⟨ρ⟩ := Q3T6.Fa.nonempty_ringEquiv_zmod_three hF
  let e' : P ≃* SL(2, ZMod 3) := e.trans (S19K.slMap2 ρ)
  rw [← isInnerAut_congr e']
  simp only [map_mul, map_inv]
  show _ ∈ Q3T6.inn3
  simp only [Subgroup.mul_mem_iff_of_index_two Q3T6.inn3_index, Subgroup.inv_mem_iff]
  tauto

theorem outCommMod_of_chart3 {G : Type} [Group G] {K : Subgroup G}
    (e : ↥K ⧸ classicalInvolutionOddCore ↥K ≃* SL(2, GaloisField 3 1)) : T3S.OutCommMod K := by
  intro x hx y hy
  have hF3 : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 (by norm_num)]
    norm_num
  have hxi : x⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hx
  have hyi : y⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hy
  have hxy : x * y ∈ Subgroup.normalizer (K : Set G) := Subgroup.mul_mem _ hx hy
  have hxyx : x * y * x⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.mul_mem _ hxy hxi
  have hc : ⁅x, y⁆ ∈ Subgroup.normalizer (K : Set G) := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ hxyx hyi
  obtain ⟨s, hs⟩ := isInnerAut_commutator_of_equiv_sl2_three hF3
    (MulEquiv.refl SL(2, GaloisField 3 1)) (phiG K e x) (phiG K e y)
  obtain ⟨k, rfl⟩ := eta_surjective K e s
  have hphi : phiG K e ⁅x, y⁆ = phiG K e x * phiG K e y * (phiG K e x)⁻¹ * (phiG K e y)⁻¹ := by
    rw [commutatorElement_def, phiG_mul hxyx hyi, phiG_mul hxy hxi, phiG_mul hx hy,
      phiG_inv hx, phiG_inv hy]
  refine ⟨k, k.2, fun g hg => ?_⟩
  have h1 := phiG_apply_eta (L := K) (e := e) hc ⟨g, hg⟩
  rw [hphi, ← hs] at h1
  have h2 : (MulAut.conj (eta K e k) : MulAut SL(2, GaloisField 3 1)) (eta K e ⟨g, hg⟩) =
      eta K e (k * ⟨g, hg⟩ * k⁻¹) := by
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  rw [h2] at h1
  have hB : ⁅x, y⁆ * g * ⁅x, y⁆⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hc g).mp hg
  have hAB : (k * ⟨g, hg⟩ * k⁻¹)⁻¹ * (⟨⁅x, y⁆ * g * ⁅x, y⁆⁻¹, hB⟩ : ↥K) ∈
      classicalInvolutionOddCore ↥K := by
    rw [← eta_eq_one_iff K e, map_mul, map_inv, h1]
    exact inv_mul_cancel _
  exact mem_oddCoreOf_iff.mpr ⟨((k * ⟨g, hg⟩ * k⁻¹)⁻¹ * (⟨⁅x, y⁆ * g * ⁅x, y⁆⁻¹, hB⟩ : ↥K)).2,
    hAB⟩

end Out

end CFSG.ClassicalInvolution.Q3.Q3T6D
