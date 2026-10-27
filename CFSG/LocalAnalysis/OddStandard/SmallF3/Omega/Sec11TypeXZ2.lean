module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11TypeXZ1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S105S

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatFactsSmall.PSp43
  Certificates.OmegaInv Certificates.OmegaT11

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G}
  {K1 K2 T R : Subgroup G} {h z' : G}

theorem t11_zp_conj_z
    (D : T11Frame t L S z K1 K2 T R h z') :
    ∃ l ∈ L, l⁻¹ * z * l = z' := by
  have hzA := t11_invCent_of_i4p D.F D.hyp.ctx.toSec10Ctx.toSec10Z.pocket
  have hzA' : InvCent 1152 (D.F.ψ ⟨z', D.mem⟩) := by
    rw [D.psi]
    exact t11_invCent_zeta0
  exact t11_conj_of_1152 D.F _ D.mem hzA hzA'

theorem t11_zp_i4p
    (D : T11Frame t L S z K1 K2 T R h z') :
    InducesTypeSome (CFSG.conjugate L h) z' 5 1 4 1 := by
  rcases t11_zp_type D with h1 | h1
  · exact h1
  · exfalso
    have H := D.hyp
    obtain ⟨l, -, hlz⟩ := t11_zp_conj_z D
    have hmem : l⁻¹ * z * l ∈ centralizer ({h⁻¹ * t * h} : Set G) := by
      rw [hlz]
      exact Subgroup.mem_centralizer_singleton_iff.mpr (t11_zp_comm_s D)
    have h37 := H.pre.s3.l37 G (h⁻¹ * t * h) (CFSG.conjugate L h)
      (t11_ctx' H).toSec10Z.toSec10Setting.toSec3SettingLB z l (t11_z_i4p' H) hmem
    rw [hlz] at h37
    exact H.pre.facts.factsC.lay G (CFSG.conjugate L h) (t11_psp' H) z' h1 h37

theorem t11_zp_mem'
    (D : T11Frame t L S z K1 K2 T R h z') :
    z' ∈ CFSG.conjugate L h := by
  have H := D.hyp
  have hpsp := t11_psp' H
  obtain ⟨F'⟩ := exists_pspFrame hpsp
  obtain ⟨hzN, hI⟩ := (TyDict.inducesTypeSome_four_plus_iff hpsp F' z').1 (t11_zp_i4p D)
  have hP : F'.φ ⟨z', hzN⟩ ∈ QP45.originalSubgroup :=
    (MoInv.mem_P_iff_of_invCent hI).2 (Or.inl rfl)
  obtain ⟨⟨w, hw⟩, hwe⟩ := F'.ψ_surj hP
  obtain ⟨c, hc⟩ : ∃ c, c = w⁻¹ * z' := ⟨_, rfl⟩
  have hz'e : z' = w * c := by
    rw [hc]
    group
  have hcN : c ∈ normalizer ((CFSG.conjugate L h : Subgroup G) : Set G) := by
    rw [hc]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hw)) hzN
  have hcC : c ∈ centralizer ((CFSG.conjugate L h : Subgroup G) : Set G) := by
    refine (F'.ker_iff ⟨c, hcN⟩).1 ?_
    have e1 : (⟨c, hcN⟩ : ↥(normalizer ((CFSG.conjugate L h : Subgroup G) : Set G))) =
        (⟨w, Subgroup.le_normalizer hw⟩)⁻¹ * ⟨z', hzN⟩ := Subtype.ext hc
    have e2 : F'.φ ⟨w, Subgroup.le_normalizer hw⟩ = F'.φ ⟨z', hzN⟩ := hwe
    rw [e1, map_mul, map_inv, e2, inv_mul_cancel]
  have hwc : w * c = c * w := Subgroup.mem_centralizer_iff.mp hcC w hw
  have hww : w * w = 1 := by
    have e3 : F'.ψ ⟨w * w, Subgroup.mul_mem _ hw hw⟩ = F'.ψ ⟨1, Subgroup.one_mem _⟩ := by
      rw [t11_psi_mul F' hw hw, hwe,
        show (⟨1, Subgroup.one_mem _⟩ : ↥(CFSG.conjugate L h)) = 1 from rfl, map_one]
      exact hI.2.1
    exact t11_eq_of_psi F' _ _ e3
  have hcc : c * c = 1 := by
    have e4 : z' * z' = w * w * (c * c) := by
      rw [hz'e]
      calc w * c * (w * c) = w * (c * w) * c := by group
        _ = w * (w * c) * c := by rw [hwc]
        _ = w * w * (c * c) := by group
    rw [t11_zp_sq D, hww, one_mul] at e4
    exact e4.symm
  have hws : Commute w (h⁻¹ * t * h) :=
    Subgroup.mem_centralizer_singleton_iff.mp (t11_le_cent' H hw)
  have hzs : Commute z' (h⁻¹ * t * h) := t11_zp_comm_s D
  have hcs : c * (h⁻¹ * t * h) = h⁻¹ * t * h * c := by
    rw [hc]
    exact hws.inv_left.mul_left hzs
  by_cases hc1 : c = 1
  · rw [hz'e, hc1, mul_one]
    exact hw
  · exfalso
    have hcs' : c = h⁻¹ * t * h := t11_invol_eq' H hcC hcs hcc hc1
    have hwI : InvCent 1152 (F'.ψ ⟨w, hw⟩) := by
      rw [hwe]
      exact hI
    obtain ⟨l', hl', hl'z⟩ := t11_conj_of_1152 F' _ hw (t11_invCent_of_i4p F' (t11_z_i4p' H)) hwI
    obtain ⟨l, -, hlz⟩ := t11_zp_conj_z D
    obtain ⟨g5, hg5⟩ := H.pre.r10.l105 G t L S z K1 K2 H.ctx.toSec10Ctx
    obtain ⟨-, -, -, -, -, htz⟩ := sec10D_basic H.pre.basic H.ctx.toSec10Ctx
    have hhz : h * z = z * h := Subgroup.mem_centralizer_singleton_iff.mp H.cent
    have hzh : h * z * h⁻¹ = z := by rw [hhz, mul_inv_cancel_right]
    have hl's : l' * (h⁻¹ * t * h) = h⁻¹ * t * h * l' :=
      Subgroup.mem_centralizer_singleton_iff.mp (t11_le_cent' H hl')
    apply sec10_not_conj_z H.pre.s3.l37 H.ctx.toSec10Ctx (l * (g5 * h * l')⁻¹)
    calc (l * (g5 * h * l')⁻¹)⁻¹ * z * (l * (g5 * h * l')⁻¹)
        = g5 * h * l' * (l⁻¹ * z * l) * (g5 * h * l')⁻¹ := by group
      _ = g5 * h * l' * (w * c) * (g5 * h * l')⁻¹ := by rw [hlz, hz'e]
      _ = g5 * h * l' * (w * (h⁻¹ * t * h)) * (g5 * h * l')⁻¹ := by rw [hcs']
      _ = g5 * h * l' * (l'⁻¹ * z * l' * (h⁻¹ * t * h)) * (g5 * h * l')⁻¹ := by rw [hl'z]
      _ = g5 * h * l' * (l'⁻¹ * z * (l' * (h⁻¹ * t * h))) * (g5 * h * l')⁻¹ := by group
      _ = g5 * h * l' * (l'⁻¹ * z * (h⁻¹ * t * h * l')) * (g5 * h * l')⁻¹ := by rw [hl's]
      _ = g5 * (h * z * h⁻¹) * t * g5⁻¹ := by group
      _ = g5 * (z * t) * g5⁻¹ := by rw [hzh, mul_assoc g5 z t]
      _ = g5 * (t * z) * g5⁻¹ := by rw [htz]
      _ = g5 * (g5⁻¹ * t * g5) * g5⁻¹ := by rw [hg5]
      _ = t := by group

theorem t11_zp_psi'
    (D : T11Frame t L S z K1 K2 T R h z')
    (F' : PspFrame (CFSG.conjugate L h)) (hF' : F'.φ ⟨t, t11_t_norm' D.hyp⟩ = r3 ()) :
    F'.ψ ⟨z', t11_zp_mem' D⟩ = zeta0 () := by
  have H := D.hyp
  have hpsp := t11_psp' H
  have hm := t11_zp_mem' D
  obtain ⟨hzN, hI⟩ := (TyDict.inducesTypeSome_four_plus_iff hpsp F' z').1 (t11_zp_i4p D)
  have hI' : InvCent 1152 (F'.ψ ⟨z', hm⟩) := hI
  refine t11_eq_zeta0 (F'.ψ_mem _) hI' ?_ ?_
  · rw [← hF']
    exact t11_phi_comm F' (Subgroup.le_normalizer hm) (t11_t_norm' H) (t11_zp_comm_t D)
  · intro g hgA hgr hg3
    obtain ⟨⟨y, hy⟩, hye⟩ := F'.ψ_surj (t11_mem_P_of_pow3 hgA hg3)
    have hyt : y * t = t * y := by
      have e : F'.φ ⟨t, t11_t_norm' H⟩ * F'.ψ ⟨y, hy⟩ =
          F'.ψ ⟨y, hy⟩ * F'.φ ⟨t, t11_t_norm' H⟩ := by
        rw [hF', hye]
        exact hgr.symm
      exact ((F'.comm_phi_psi_iff _ _).1 e).symm
    have hy3 : y ^ 3 = 1 := by
      have e : F'.ψ (⟨y, hy⟩ ^ 3) = F'.ψ 1 := by rw [map_pow, hye, hg3, map_one]
      simpa using congrArg Subtype.val (F'.ψ_injective e)
    have hys := Subgroup.mem_centralizer_singleton_iff.mp (t11_le_cent' H hy)
    have hzy := t11_zp_comm_cube D hys hyt hy3
    rw [← hye]
    exact t11_psi_comm F' hy hm hzy.symm

end CFSG.OddStandard.SmallF3.Omega
