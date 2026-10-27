module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11TypeXFr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11TypeXCert
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11TypeXB
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint Certificates.OmegaInv Certificates.OmegaT11

variable {G : Type} [Group G]

structure T11Frame [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 T R : Subgroup G)
    (h z' : G) where
  hyp : T11Hyp t L S z K1 K2 T R h
  F : PspFrame L
  hF : F.φ ⟨h⁻¹ * t * h, t11_s_norm hyp⟩ = r3 ()
  mem : z' ∈ L
  psi : F.ψ ⟨z', mem⟩ = zeta0 ()

variable [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G} {h z' : G}

theorem t11_t_norm' (H : T11Hyp t L S z K1 K2 T R h) :
    t ∈ normalizer ((CFSG.conjugate L h : Subgroup G) : Set G) :=
  t11_norm' H (Subgroup.mem_centralizer_singleton_iff.mpr (t11_s_comm_t H).symm)

theorem t11_zp_comm_t (D : T11Frame t L S z K1 K2 T R h z') : z' * t = t * z' :=
  Subgroup.mem_centralizer_singleton_iff.mp (t11_le_cent D.hyp.ctx.toSec10Ctx D.mem)

theorem t11_zp_comm_s
    (D : T11Frame t L S z K1 K2 T R h z') : z' * (h⁻¹ * t * h) = h⁻¹ * t * h * z' := by
  have h1 : D.F.φ ⟨h⁻¹ * t * h, t11_s_norm D.hyp⟩ * D.F.ψ ⟨z', D.mem⟩ =
      D.F.ψ ⟨z', D.mem⟩ * D.F.φ ⟨h⁻¹ * t * h, t11_s_norm D.hyp⟩ := by
    rw [D.hF, D.psi]
    exact t11_zeta0_comm_r3.symm
  exact ((D.F.comm_phi_psi_iff _ _).1 h1).symm

theorem t11_zp_sq
    (D : T11Frame t L S z K1 K2 T R h z') : z' * z' = 1 := by
  have h1 : D.F.ψ ⟨z' * z', L.mul_mem D.mem D.mem⟩ = D.F.ψ ⟨1, L.one_mem⟩ := by
    rw [t11_psi_mul D.F D.mem D.mem, D.psi, show (⟨1, L.one_mem⟩ : ↥L) = 1 from rfl, map_one]
    exact t11_invCent_zeta0.2.1
  exact t11_eq_of_psi D.F _ _ h1

theorem t11_zp_ne_one
    (D : T11Frame t L S z K1 K2 T R h z') : z' ≠ 1 := by
  intro e
  have h1 : D.F.ψ ⟨z', D.mem⟩ = 1 := by
    have e' : (⟨z', D.mem⟩ : ↥L) = 1 := Subtype.ext e
    rw [e', map_one]
  exact t11_invCent_zeta0.2.2.1 (D.psi.symm.trans h1)

theorem t11_zp_comm_odd
    (D : T11Frame t L S z K1 K2 T R h z') {y : G}
    (hys : y * (h⁻¹ * t * h) = h⁻¹ * t * h * y) (hyt : y * t = t * y)
    (hodd : Odd (orderOf y)) : z' * y = y * z' := by
  have hyN : y ∈ normalizer (L : Set G) :=
    t11_cent_le_norm D.hyp.pre D.hyp.ctx.toSec10Ctx
      (Subgroup.mem_centralizer_singleton_iff.mpr hyt)
  have hA := D.F.mem_A ⟨y, hyN⟩
  have hr : D.F.φ ⟨y, hyN⟩ * r3 () = r3 () * D.F.φ ⟨y, hyN⟩ := by
    rw [← D.hF]
    exact t11_phi_comm D.F hyN (t11_s_norm D.hyp) hys
  have hodd' : Odd (orderOf (D.F.φ ⟨y, hyN⟩)) := by
    have e : orderOf (⟨y, hyN⟩ : ↥(normalizer (L : Set G))) = orderOf y :=
      (Subgroup.orderOf_coe _).symm
    have h1 := orderOf_map_dvd D.F.φ ⟨y, hyN⟩
    rw [e] at h1
    exact Odd.of_dvd_nat hodd h1
  have hc := t11_comm_zeta0 hA hr (t11_pow3_of_odd hA hr hodd')
  have h1 : D.F.φ ⟨y, hyN⟩ * D.F.ψ ⟨z', D.mem⟩ = D.F.ψ ⟨z', D.mem⟩ * D.F.φ ⟨y, hyN⟩ := by
    rw [D.psi]
    exact hc
  exact ((D.F.comm_phi_psi_iff _ _).1 h1).symm

theorem t11_zp_comm_cube
    (D : T11Frame t L S z K1 K2 T R h z') {y : G}
    (hys : y * (h⁻¹ * t * h) = h⁻¹ * t * h * y) (hyt : y * t = t * y) (hy3 : y ^ 3 = 1) :
    z' * y = y * z' :=
  t11_zp_comm_odd D hys hyt (Odd.of_dvd_nat ⟨1, rfl⟩ (orderOf_dvd_of_pow_eq_one hy3))

theorem t11_zp_comm_oTwo
    (D : T11Frame t L S z K1 K2 T R h z') :
    ∀ g ∈ oTwoRes (CFSG.conjugate L h ⊓ centralizer ({t} : Set G)), z' * g = g * z' := by
  have hle : oTwoRes (CFSG.conjugate L h ⊓ centralizer ({t} : Set G)) ≤
      centralizer ({z'} : Set G) := by
    unfold oTwoRes
    rw [Subgroup.closure_le]
    rintro x ⟨hx, hodd⟩
    obtain ⟨hxL, hxt⟩ := Subgroup.mem_inf.1 hx
    have hxs := Subgroup.mem_centralizer_singleton_iff.mp (t11_le_cent' D.hyp hxL)
    have hxt' := Subgroup.mem_centralizer_singleton_iff.mp hxt
    exact Subgroup.mem_centralizer_singleton_iff.mpr (t11_zp_comm_odd D hxs hxt' hodd).symm
  intro g hg
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hg)).symm

theorem t11_zp_type
    (D : T11Frame t L S z K1 K2 T R h z') :
    InducesTypeSome (CFSG.conjugate L h) z' 5 1 4 1 ∨
      InducesTypeSome (CFSG.conjugate L h) z' 5 1 4 (-1) := by
  have H := D.hyp
  obtain ⟨-, htC, htL, -⟩ := H.pre.basic G t L S z H.ctx.toSec10Ctx.toSec10Z
  obtain ⟨ht2, -⟩ := sec10D_basic H.pre.basic H.ctx.toSec10Ctx
  have hzs := t11_zp_comm_s D
  have hzt := t11_zp_comm_t D
  have hsC : h⁻¹ * t * h ∉ L ⊔ centralizer (L : Set G) := t11_s_not_inner H
  have hzN : z' ∈ normalizer ((CFSG.conjugate L h : Subgroup G) : Set G) :=
    t11_norm' H (Subgroup.mem_centralizer_singleton_iff.mpr hzs)
  have hzz : z' * z' ∈ centralizer ((CFSG.conjugate L h : Subgroup G) : Set G) := by
    rw [t11_zp_sq D]
    exact Subgroup.one_mem _
  have hn1 : z' ∉ centralizer ((CFSG.conjugate L h : Subgroup G) : Set G) := by
    intro hc
    have e := t11_invol_eq' H hc hzs (t11_zp_sq D) (t11_zp_ne_one D)
    rw [← e] at hsC
    exact hsC (Subgroup.mem_sup_left D.mem)
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hn2 : t⁻¹ * z' ∉ centralizer ((CFSG.conjugate L h : Subgroup G) : Set G) := by
    rw [hti]
    intro hc
    have hst := t11_s_comm_t H
    have h1 : t * z' * (h⁻¹ * t * h) = h⁻¹ * t * h * (t * z') := by
      calc t * z' * (h⁻¹ * t * h) = t * (z' * (h⁻¹ * t * h)) := by group
        _ = t * (h⁻¹ * t * h * z') := by rw [hzs]
        _ = t * (h⁻¹ * t * h) * z' := by group
        _ = h⁻¹ * t * h * t * z' := by rw [hst]
        _ = h⁻¹ * t * h * (t * z') := by group
    have h2 : t * z' * (t * z') = 1 := by
      calc t * z' * (t * z') = t * (z' * t) * z' := by group
        _ = t * (t * z') * z' := by rw [hzt]
        _ = t * t * (z' * z') := by group
        _ = 1 := by rw [ht2, t11_zp_sq D, one_mul]
    have h3 : t * z' ≠ 1 := by
      intro e
      apply htL
      rw [eq_inv_of_mul_eq_one_left e]
      exact L.inv_mem D.mem
    have e := t11_invol_eq' H hc h1 h2 h3
    apply hsC
    rw [← e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right htC) (Subgroup.mem_sup_left D.mem)
  exact H.pre.facts.f218f G (CFSG.conjugate L h) (t11_psp' H) t z' (Or.inl (t11_type_t H))
    hzN hzz hn1 hn2 (t11_zp_comm_oTwo D)

end CFSG.OddStandard.SmallF3.Omega
