module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RN
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RNIso
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UCentSound

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem exists_eD {G : Type} [Group G] [Finite G] {S : Subgroup G} {s z t : G}
    (hS : S16Gen S s z t) (hS16 : Nat.card ↥S = 16) :
    ∃ eD : ↥(Dsub s z) ≃* DihedralGroup 4,
      sElt eD 1 = s * s ∧ sElt eD 4 = s * z ∧ sElt eD 2 = t ∧
      z * sElt eD 1 * z⁻¹ = (sElt eD 1)⁻¹ ∧ z * sElt eD 4 * z⁻¹ = (sElt eD 1)⁻¹ * sElt eD 4 ∧
      sElt eD 0 = 1 := by
  have ha4 : (s * s) ^ 4 = 1 := by
    rw [← hS.hs8, show (8 : ℕ) = 2 * 4 from rfl, pow_mul, pow_two]
  have hb2 : (s * z) * (s * z) = 1 := b_sq hS.hz2 hS.hzs
  have hba : (s * z) * (s * s) * (s * z)⁻¹ = (s * s)⁻¹ := b_inv_a hS.hz2 hS.hzs
  have hcard : Nat.card ↥(Dsub s z) = 8 :=
    card_Dsub hS.hs hS.hzS hS.hs8 hS.hz2 hS.hzs hS.hord hS.hzns hS.hgen hS16
  obtain ⟨e, he1, he2⟩ : ∃ e : ↥(Dsub s z) ≃* DihedralGroup 4,
      e ⟨s * s, a_mem_Dsub⟩ = DihedralGroup.r 1 ∧ e ⟨s * z, b_mem_Dsub⟩ = DihedralGroup.sr 0 :=
    exists_dihedral4_equiv ha4 hb2 hba hcard
  have hsq : e ⟨t, t_mem_Dsub hS.hs4⟩ = DihedralGroup.r 2 := by
    have h : (⟨t, t_mem_Dsub hS.hs4⟩ : ↥(Dsub s z)) =
        ⟨s * s, a_mem_Dsub⟩ * ⟨s * s, a_mem_Dsub⟩ :=
      Subtype.ext (a_sq hS.hs4).symm
    rw [h, map_mul, he1]
    decide
  have hd1 : dih 1 = DihedralGroup.r 1 := by decide
  have hd2 : dih 2 = DihedralGroup.r 2 := by decide
  have hd4 : dih 4 = DihedralGroup.sr 0 := by decide
  have hr1 : e.symm (DihedralGroup.r 1) = ⟨s * s, a_mem_Dsub⟩ :=
    (MulEquiv.symm_apply_eq e).mpr he1.symm
  have hsr0 : e.symm (DihedralGroup.sr 0) = ⟨s * z, b_mem_Dsub⟩ :=
    (MulEquiv.symm_apply_eq e).mpr he2.symm
  have hr2 : e.symm (DihedralGroup.r 2) = ⟨t, t_mem_Dsub hS.hs4⟩ :=
    (MulEquiv.symm_apply_eq e).mpr hsq.symm
  have hE1 : sElt e 1 = s * s := by
    unfold sElt
    rw [hd1, hr1]
  have hE4 : sElt e 4 = s * z := by
    unfold sElt
    rw [hd4, hsr0]
  have hE2 : sElt e 2 = t := by
    unfold sElt
    rw [hd2, hr2]
  have hconj : z * (s * s) * z⁻¹ = (s * s)⁻¹ := by
    calc z * (s * s) * z⁻¹ = (z * s * z⁻¹) * (z * s * z⁻¹) := by group
      _ = s⁻¹ * s⁻¹ := by rw [hS.hzs]
      _ = (s * s)⁻¹ := by group
  have hzs' : z * s = s⁻¹ * z := by
    calc z * s = (z * s * z⁻¹) * z := by group
      _ = s⁻¹ * z := by rw [hS.hzs]
  refine ⟨e, hE1, hE4, hE2, ?_, ?_, sElt_zero e⟩
  · rw [hE1]
    exact hconj
  · rw [hE1, hE4]
    calc z * (s * z) * z⁻¹ = z * s := by group
      _ = s⁻¹ * z := hzs'
      _ = (s * s)⁻¹ * (s * z) := by group

end CFSG.EvenSporadicStandard.Fin76b
