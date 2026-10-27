module

public import CFSG.GF2Type.Smith1979.CaseIIA8
public import CFSG.GF2Type.Smith1979.CaseIIBKbar
public import CFSG.GF2Type.Smith1979.CaseIIDCentre
public import CFSG.Assembly.ComponentTypeDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case2

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.Open CFSG.ComponentClassification

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace Data

variable (D : Data S g t)
include D

theorem tM_not_mem_layer : CaseI25Transfer.tM D.ht ∉ timmesfeldLayer S.Mbar := by
  intro h
  have hEperf : ⁅timmesfeldLayer S.Mbar, timmesfeldLayer S.Mbar⁆ = timmesfeldLayer S.Mbar :=
    Subgroup.isPerfect_iff.mp (Layer.perfect S.Mbar)
  have hmem : CaseI25Transfer.tM D.ht ∈ _root_.commutator S.Mbar := by
    rw [commutator_def]
    have hle : ⁅timmesfeldLayer S.Mbar, timmesfeldLayer S.Mbar⁆ ≤ ⁅(⊤ : Subgroup S.Mbar), ⊤⁆ :=
      Subgroup.commutator_mono le_top le_top
    rw [hEperf] at hle
    exact hle h
  exact D.not_mem_commutator_Mbar ⟨_, hmem, rfl⟩

theorem eq_one_of_central_Rder (hCE : S4.CentralExtInput.{0}) {z : S.O} (hz : z ∈ Rder S g t)
    (hc : ∀ s ∈ Rder S g t, s * z = z * s) : z = 1 := by
  obtain ⟨-, -, h3, h4, h5, h6, -⟩ := Rbar_structure_II D hCE
  have hzR : z ∈ Rbar S g t := h4 hz
  have hzt : z * t = t * z := h3 z hzR
  have hcR : ∀ r ∈ Rbar S g t, r * z = z * r := by
    have hle : Rbar S g t ≤ centralizer ({z} : Set S.O) := by
      rw [← h6]
      refine sup_le (fun s hs => ?_) (zpowers_le.mpr ?_)
      · exact mem_centralizer_singleton_iff.mpr (hc s hs)
      · exact mem_centralizer_singleton_iff.mpr hzt.symm
    intro r hr
    exact mem_centralizer_singleton_iff.mp (hle hr)
  set zR : Rbar S g t := ⟨z, hzR⟩
  haveI : Nontrivial (Vt S g t) := Module.nontrivial_of_finrank_pos (by rw [D.h3]; norm_num)
  have hzN : z ∈ Nbar S g t := by
    let ψ : Vt S g t ≃ₗ[ZMod 2] Vt S g t := resV D.H.conj_mem t zR
    have hcomm : ∀ (h : Vt S g t ≃ₗ[ZMod 2] Vt S g t) (x : Vt S g t),
        (ψ : Vt S g t →ₗ[ZMod 2] Vt S g t) (h x) = h (ψ x) := by
      intro h x
      obtain ⟨r, hr⟩ : h ∈ (resV D.H.conj_mem t).range := by
        rw [range_resV, D.hL.eq_top]
        exact mem_top h
      rw [← hr]
      show (resV D.H.conj_mem t zR * resV D.H.conj_mem t r) x =
        (resV D.H.conj_mem t r * resV D.H.conj_mem t zR) x
      rw [← map_mul, ← map_mul]
      congr 2
      exact Subtype.ext (hcR r.1 r.2).symm
    rcases Sp.end_eq_zero_or_id D.h3 (ψ : Vt S g t →ₗ[ZMod 2] Vt S g t) hcomm with h0 | h1
    · exfalso
      obtain ⟨v, hv0⟩ := exists_ne (0 : Vt S g t)
      exact hv0 (ψ.injective ((h0 v).trans (map_zero ψ).symm))
    · exact (resV_eq_one_iff D.H.conj_mem zR).mp (LinearEquiv.ext h1)
  have hγ : D.resR zR ∈ D.Gam0 := ⟨⟨z, hzN⟩, rfl⟩
  have hγAlt := D.Gam0_le_Alt hCE hγ
  have hγ1 : D.resR zR = 1 := by
    refine Sp.eq_one_of_central D.spData D.isGamma hγAlt ?_
    rintro _ ⟨r, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcR r.1 r.2)
  rcases (D.resR_eq_one_iff zR).mp hγ1 with h | h
  · exact h
  · have hzt' : z = t := h
    exact absurd (hzt' ▸ hz) h5

theorem layer_inf_Rbar (hCE : S4.CentralExtInput.{0})
    (hRE : Rder S g t ≤ (timmesfeldLayer S.Mbar).map S.Mbar.subtype) :
    (timmesfeldLayer S.Mbar).map S.Mbar.subtype ⊓ Rbar S g t = Rder S g t := by
  obtain ⟨-, h2, -, h4, -, -, -, h8, -⟩ := Rbar_structure_II D hCE
  set B := (timmesfeldLayer S.Mbar).map S.Mbar.subtype ⊓ Rbar S g t
  have hRB : Rder S g t ≤ B := le_inf hRE h4
  have hBR : B ≤ Rbar S g t := inf_le_right
  have hd1 : 1344 ∣ Nat.card B := h8 ▸ Subgroup.card_dvd_of_le hRB
  have hd2 : Nat.card B ∣ 2688 := h2 ▸ Subgroup.card_dvd_of_le hBR
  have hne : Nat.card B ≠ 2688 := by
    intro h
    have hBeq : B = Rbar S g t := Subgroup.eq_of_le_of_card_ge hBR (h2 ▸ h.ge)
    have htB : t ∈ B := by
      rw [hBeq]
      exact Lbar_le_Rbar D.ht D.ht
    obtain ⟨e, he, het⟩ := htB.1
    have : e = CaseI25Transfer.tM D.ht := Subtype.ext het
    exact D.tM_not_mem_layer (this ▸ he)
  have hpos : 0 < Nat.card B := Nat.card_pos
  have hc : Nat.card B ≤ 1344 := by
    obtain ⟨k, hk⟩ := hd1
    have hle := Nat.le_of_dvd (by norm_num) hd2
    rcases k with _ | _ | _ | k <;> omega
  exact (Subgroup.eq_of_le_of_card_ge hRB (h8 ▸ hc)).symm

theorem conj_mem_Rder_inf_Nbar (hCE : S4.CentralExtInput.{0}) {r s : S.O}
    (hr : r ∈ Rder S g t) (hs : s ∈ Rder S g t ⊓ Nbar S g t) :
    r * s * r⁻¹ ∈ Rder S g t ⊓ Nbar S g t := by
  obtain ⟨-, -, -, h4, -⟩ := Rbar_structure_II D hCE
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar (h4 hr))
  have hkt : S.ρ k * t = t * S.ρ k := by
    rw [hk]
    exact commute_of_mem_Rbar D.H.conj_mem (h4 hr)
  have h1 : r * s * r⁻¹ ∈ Rder S g t :=
    (Rder S g t).mul_mem ((Rder S g t).mul_mem hr hs.1) ((Rder S g t).inv_mem hr)
  have h2 := conj_mem_Nbar D.H.conj_mem hkt hs.2
  rw [hk] at h2
  exact ⟨h1, h2⟩

end Data

end CFSG.GF2Type.Smith1979.Case2
