module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.JRSplit
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.GenericPhi

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {G : Type} [Group G] [Finite G]

structure JRData (t z : G) : Prop where
  J_le_C : Jg t z ≤ Cz z
  relIndex_KJ : (Kg t z).relIndex (Jg t z) = 2
  card_R : Nat.card ↥(Rg t z) = 2 ^ 13
  R_inf_K : Rg t z ⊓ Kg t z = OKg t z
  V_le_R : Vtz t z ≤ Rg t z
  R_normal : ∀ j ∈ Jg t z, ∀ r ∈ Rg t z, j * r * j⁻¹ ∈ Rg t z
  quot : ∃ (X : Type) (_ : Group X) (π : ↥(Jg t z) →* X), Function.Surjective π ∧
    π.ker = (Rg t z).subgroupOf (Jg t z) ∧ IsU42Two X
  center_R : ∀ x ∈ Rg t z, (∀ y ∈ Rg t z, x * y = y * x) ↔ x ∈ zpowers z
  cent_R : centralizer (Rg t z : Set G) = zpowers z
  phi_card : Nat.card ↥(Phi2 (Rg t z)) ≤ 16

theorem jrData {t z : G} (hK : KleinPair t z) (hJ : JBasic t z) (hS : RSplit t z)
    (hKD : KData t z) : JRData t z := by
  have hOK_le_R : OKg t z ≤ Rg t z := by
    rw [← hS.R_inf_K]; exact inf_le_left
  have hV_le_R : Vtz t z ≤ Rg t z := hKD.V_le.trans hOK_le_R
  have htR : t ∈ Rg t z := hV_le_R (t_mem_Vtz)
  have hzR : z ∈ Rg t z := hV_le_R (z_mem_Vtz)
  have hidx : (OKg t z).relIndex (Rg t z) = 2 := by
    have h := Subgroup.relIndex_mul_card (H := OKg t z) (K := Rg t z)
    rw [inf_eq_left.mpr hOK_le_R] at h
    rw [hKD.card_OK, hS.card_R] at h
    norm_num at h
    omega
  have hex : ∃ y₀ ∈ Rg t z, y₀ ∉ Kg t z := by
    by_contra h
    have hle : Rg t z ≤ Kg t z := by
      intro y hy
      by_contra hyK
      exact h ⟨y, hy, hyK⟩
    have heq : Rg t z = OKg t z := by
      rw [← hS.R_inf_K, inf_eq_left.mpr hle]
    have hcard : Nat.card ↥(Rg t z) = Nat.card ↥(OKg t z) := by rw [heq]
    rw [hS.card_R, hKD.card_OK] at hcard
    exact absurd hcard (by norm_num)
  obtain ⟨y₀, hy₀R, hy₀K⟩ := hex
  have hy₀J : y₀ ∈ Jg t z := (Rg_le_Jg t z) hy₀R
  have hy₀t : y₀ * t * y₀⁻¹ = t * z := hJ.swap_of_not_mem y₀ hy₀J hy₀K
  have hy₀z : y₀ * z = z * y₀ := by
    have h := hJ.J_le_C hy₀J
    rwa [mem_Cz] at h
  have hy₀z' : y₀ * z * y₀⁻¹ = z := by rw [hy₀z]; group
  have hcenter : ∀ x ∈ Rg t z, (∀ y ∈ Rg t z, x * y = y * x) ↔ x ∈ zpowers z := by
    intro x hxR
    constructor
    · intro hx
      have hxK : x ∈ Kg t z := mem_Kg.mpr ⟨hx t htR, hx z hzR⟩
      have hxOK : x ∈ OKg t z := by
        rw [← hS.R_inf_K]; exact ⟨hxR, hxK⟩
      have hxcentOK : ∀ y ∈ OKg t z, x * y = y * x := fun y hy => hx y (hOK_le_R hy)
      have hxV : x ∈ Vtz t z := (hKD.center_OK x hxOK).mp hxcentOK
      rcases (mem_Vtz_iff hK).mp hxV with hx1 | hxt | hxz | hxtz
      · rw [hx1]; exact one_mem _
      · exfalso
        have hcomm := hx y₀ hy₀R
        rw [hxt] at hcomm
        have htz : t * z = t := by
          rw [← hy₀t, ← hcomm]; group
        exact hK.z_ne (mul_left_cancel (by rw [htz, mul_one]))
      · rw [hxz]; exact Subgroup.mem_zpowers z
      · exfalso
        have hcomm := hx y₀ hy₀R
        rw [hxtz] at hcomm
        have hcomp : y₀ * (t * z) * y₀⁻¹ = t := by
          calc y₀ * (t * z) * y₀⁻¹ = (y₀ * t * y₀⁻¹) * (y₀ * z * y₀⁻¹) := by group
            _ = (t * z) * z := by rw [hy₀t, hy₀z']
            _ = t := by rw [mul_assoc, ← pow_two, hK.z_sq, mul_one]
        have hconj : y₀ * (t * z) * y₀⁻¹ = t * z := by
          rw [← hcomm]; group
        have htz : t * z = t := by
          rw [hcomp] at hconj; exact hconj.symm
        exact hK.z_ne (mul_left_cancel (by rw [htz, mul_one]))
    · intro hxzp y hyR
      have hyz : y * z = z * y := by
        have h := hJ.J_le_C ((Rg_le_Jg t z) hyR)
        rwa [mem_Cz] at h
      have hz_cent : z ∈ centralizer ({y} : Set G) :=
        mem_centralizer_singleton_iff.mpr hyz.symm
      have hx_cent : x ∈ centralizer ({y} : Set G) :=
        (Subgroup.zpowers_le.mpr hz_cent) hxzp
      exact mem_centralizer_singleton_iff.mp hx_cent
  have hcentR : centralizer (Rg t z : Set G) = zpowers z := by
    apply le_antisymm
    · intro g hg
      have hgcomm : ∀ y ∈ Rg t z, g * y = y * g :=
        fun y hy => (mem_centralizer_iff.mp hg y hy).symm
      have hgK : g ∈ Kg t z := mem_Kg.mpr ⟨hgcomm t htR, hgcomm z hzR⟩
      have hgcentOK : g ∈ centralizer (OKg t z : Set G) :=
        mem_centralizer_iff.mpr (fun y hy => (hgcomm y (hOK_le_R hy)).symm)
      have hgOK : g ∈ OKg t z := hKD.cent_OK ⟨hgK, hgcentOK⟩
      have hgR : g ∈ Rg t z := hOK_le_R hgOK
      exact (hcenter g hgR).mp hgcomm
    · intro g hg
      have hgR : g ∈ Rg t z := (Subgroup.zpowers_le.mpr hzR) hg
      exact mem_centralizer_iff.mpr (fun y hy => ((hcenter g hgR).mpr hg y hy).symm)
  obtain ⟨Y, hYK, _, _, hlat⟩ := hKD.perfect
  have hphi : Nat.card ↥(Phi2 (Rg t z)) ≤ 16 :=
    phi_card_le (R := Rg t z) (O := OKg t z) (V := Vtz t z) (Y := Y)
      hOK_le_R hidx hKD.card_OK hKD.V_le (card_Vtz hK)
      (fun r hr v hv =>
        ((mem_normalizer_iff.mp (show r ∈ normalizer (Vtz t z : Set G) from
          (Rg_le_Jg t z) hr)) v).mp hv)
      (fun r hr o ho => hJ.conj_OK r ((Rg_le_Jg t z) hr) o ho)
      hKD.phi_sq hKD.phi_comm
      (fun y hy o ho => hJ.conj_OK y ((Kg_le_Jg t z) (hYK hy)) o ho)
      (fun y hy v hv =>
        ((mem_normalizer_iff.mp (show y ∈ normalizer (Vtz t z : Set G) from
          (Kg_le_Jg t z) (hYK hy))) v).mp hv)
      (fun y hy r hr => by
        have h := inv_mem (hS.cent_RK r hr y (hYK hy))
        rwa [show (r * y * r⁻¹ * y⁻¹)⁻¹ = y * r * y⁻¹ * r⁻¹ from by group] at h)
      hlat
  exact
    { J_le_C := hJ.J_le_C
      relIndex_KJ := hJ.relIndex_KJ
      card_R := hS.card_R
      R_inf_K := hS.R_inf_K
      V_le_R := hV_le_R
      R_normal := hS.R_normal
      quot := hS.quot
      center_R := hcenter
      cent_R := hcentR
      phi_card := hphi }

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
