module

public import CFSG.GH74.GLS.C3.Layer1.Th2P412Om
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS.Th2.P43f

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Bk
  CFSG.GH74.GLS.C3.Layer1.Back CFSG.GH74.GLS.Th2 Equiv Equiv.Perm
  CFSG.LieType.SteinbergBR.SmallAlt

variable {G : Type} [Group G] {x : G} {K T S : Subgroup G} {a z : G} {psi : G → Perm (Fin 7)}

namespace Frame

variable (F : Frame x K T S a z psi)

include F

theorem not_isConj_x_of_swap [Finite G] (hG : C3Hyp G) {y : G} (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) {s : G} (hsS : s ∈ S) (hsT : s ∉ T) (hs2 : s * s = 1) :
    ¬ IsConj x s := by
  intro hxs
  obtain ⟨g, hg⟩ := isConj_iff.1 hxs
  have hR := F.R_four hG hs e7 hP2 hQ4
  obtain ⟨r, hrR, hr1, hrz⟩ := F.exists_nc hR
  have hrP : r ∈ T ⊓ K := hR.1 hrR
  have hr2 : r * r = 1 := (forall_of_isElementaryAbelian hR.2.1).2 r hrR
  have hzR : z ∈ conjugate (T ⊓ CxK x K) a⁻¹ := F.z_mem_four hR
  have hr'P' : s * r * s⁻¹ ∈ conjugate (T ⊓ K) a := F.swap_P hsS hsT hrP
  obtain ⟨r', hr'⟩ : ∃ r', r' = s * r * s⁻¹ := ⟨_, rfl⟩
  rw [← hr'] at hr'P'
  have hr'2 : r' * r' = 1 := by
    calc r' * r' = s * (r * r) * s⁻¹ := by rw [hr']; group
      _ = 1 := by rw [hr2]; group
  have hr's : s * r' * s⁻¹ = r := by
    calc s * r' * s⁻¹ = (s * s) * r * (s * s)⁻¹ := by rw [hr']; group
      _ = r := by rw [hs2]; group
  have hwP : a * r' * a⁻¹ ∈ T ⊓ K := mem_conjugate_iff'.1 hr'P'
  have hw2 : (a * r' * a⁻¹) * (a * r' * a⁻¹) = 1 := by
    calc (a * r' * a⁻¹) * (a * r' * a⁻¹) = a * (r' * r') * a⁻¹ := by group
      _ = 1 := by rw [hr'2]; group
  have hr'1 : r' ≠ 1 := by
    intro h
    apply hr1
    rw [← hr's, h]
    group
  have hw1 : a * r' * a⁻¹ ≠ 1 := by
    intro h
    apply hr'1
    calc r' = a⁻¹ * (a * r' * a⁻¹) * a := by group
      _ = 1 := by rw [h]; group
  have hwz : a * r' * a⁻¹ ≠ z := by
    intro h
    have hr'x : r' = x := by
      calc r' = a⁻¹ * (a * r' * a⁻¹) * a := by group
        _ = a⁻¹ * z * a := by rw [h]
        _ = x := F.a_z_a
    apply hrz
    calc r = s * r' * s⁻¹ := hr's.symm
      _ = s * x * s⁻¹ := by rw [hr'x]
      _ = z := F.swap_x hsS hsT
  have hrr' : r * r' = r' * r := F.core.comm_P_conj r hrP r' hr'P'
  have hδ2 : (r * r') * (r * r') = 1 := by
    calc (r * r') * (r * r') = r * (r' * r) * r' := by group
      _ = r * (r * r') * r' := by rw [← hrr']
      _ = (r * r) * (r' * r') := by group
      _ = 1 := by rw [hr2, hr'2, one_mul]
  have hδs : (r * r') * s = s * (r * r') := by
    have h1 : s * (r * r') * s⁻¹ = r * r' := by
      calc s * (r * r') * s⁻¹ = (s * r * s⁻¹) * (s * r' * s⁻¹) := by group
        _ = r' * r := by rw [← hr', hr's]
        _ = r * r' := hrr'.symm
    calc (r * r') * s = (s * (r * r') * s⁻¹) * s := by rw [h1]
      _ = s * (r * r') := by group
  have hvs : (z * x) * s = s * (z * x) := by
    have h1 := F.S_centralizes_v s hsS
    calc (z * x) * s = (s * (z * x) * s⁻¹) * s := by rw [h1]
      _ = s * (z * x) := by group
  have hvT : z * x ∈ T := T.mul_mem F.z_mem.1 F.x_mem_T
  have hδT : r * r' ∈ T := T.mul_mem hrP.1 (F.core.conj_le F.core.P_le hr'P')
  have hδvcomm : (r * r') * (z * x) = (z * x) * (r * r') := by
    have h1 := F.S_centralizes_v (r * r') (F.core.T_le_S hδT)
    calc (r * r') * (z * x) = ((r * r') * (z * x) * (r * r')⁻¹) * (r * r') := by group
      _ = (z * x) * (r * r') := by rw [h1]
  have hδv : IsConj (r * r') (z * x) := by
    have e : tt a r (a * r' * a⁻¹) = r * r' := by
      unfold tt
      congr 1
      group
    rw [← e]
    exact F.isConj_tt_v_of_left hrP hwP hr2 hw2 hr1 hw1 (F.psi_R hrR)
  have hδvv : IsConj ((z * x) * (r * r')) (z * x) := by
    have hwzP : a * r' * a⁻¹ * z ∈ T ⊓ K := Subgroup.mul_mem _ hwP F.z_mem
    have hrzP : r * z ∈ T ⊓ K := Subgroup.mul_mem _ hrP F.z_mem
    have hrzR : r * z ∈ conjugate (T ⊓ CxK x K) a⁻¹ := Subgroup.mul_mem _ hrR hzR
    have hrzc : r * z = z * r := F.z_central r hrP
    have hwzc : a * r' * a⁻¹ * z = z * (a * r' * a⁻¹) := F.z_central _ hwP
    have hrz2 : (r * z) * (r * z) = 1 := by
      calc (r * z) * (r * z) = r * (z * r) * z := by group
        _ = r * (r * z) * z := by rw [← hrzc]
        _ = (r * r) * (z * z) := by group
        _ = 1 := by rw [hr2, F.z_sq, one_mul]
    have hrz1 : r * z ≠ 1 := by
      intro h
      apply hrz
      rw [mul_eq_one_iff_eq_inv.1 h]
      exact inv_eq_of_mul_eq_one_right F.z_sq
    have hwz2 : (a * r' * a⁻¹ * z) * (a * r' * a⁻¹ * z) = 1 := by
      calc (a * r' * a⁻¹ * z) * (a * r' * a⁻¹ * z)
          = (a * r' * a⁻¹) * (z * (a * r' * a⁻¹)) * z := by group
        _ = (a * r' * a⁻¹) * ((a * r' * a⁻¹) * z) * z := by rw [← hwzc]
        _ = ((a * r' * a⁻¹) * (a * r' * a⁻¹)) * (z * z) := by group
        _ = 1 := by rw [hw2, F.z_sq, one_mul]
    have hwz1 : a * r' * a⁻¹ * z ≠ 1 := by
      intro h
      apply hwz
      rw [mul_eq_one_iff_eq_inv.1 h]
      exact inv_eq_of_mul_eq_one_right F.z_sq
    have hw' : a⁻¹ * (a * r' * a⁻¹ * z) * a = r' * x := by
      calc a⁻¹ * (a * r' * a⁻¹ * z) * a = r' * (a⁻¹ * z * a) := by group
        _ = r' * x := by rw [F.a_z_a]
    have hzr' : z * r' = r' * z := F.core.comm_P_conj z F.z_mem r' hr'P'
    have e : (z * x) * (r * r') = tt a (r * z) (a * r' * a⁻¹ * z) := by
      unfold tt
      rw [hw']
      calc (z * x) * (r * r') = (r * r') * (z * x) := hδvcomm.symm
        _ = r * (r' * z) * x := by group
        _ = r * (z * r') * x := by rw [hzr']
        _ = (r * z) * (r' * x) := by group
    rw [e]
    exact F.isConj_tt_v_of_left hrzP hwzP hrz2 hwz2 hrz1 hwz1 (F.psi_R hrzR)
  have key : ∀ t : G, t ∈ T → t * t = 1 → t * s = s * t → IsConj x (s * t) := by
    intro t htT ht2 hts
    have hst : s * t ∈ S := S.mul_mem hsS (F.core.T_le_S htT)
    have hstT : s * t ∉ T := fun h => hsT (by simpa using T.mul_mem h (T.inv_mem htT))
    have hst2 : (s * t) * (s * t) = 1 := by
      calc (s * t) * (s * t) = s * (t * s) * t := by group
        _ = s * (s * t) * t := by rw [hts]
        _ = (s * s) * (t * t) := by group
        _ = 1 := by rw [hs2, ht2, one_mul]
    obtain ⟨u, -, hu⟩ := F.exists_conj_of_involutions hsS hsT hst hstT hs2 hst2
    exact hxs.trans (isConj_iff.2 ⟨u, hu⟩)
  have hvδ : (z * x) * (r * r') = (r * r') * (z * x) := hδvcomm.symm
  have hvδ2 : ((z * x) * (r * r')) * ((z * x) * (r * r')) = 1 := by
    calc ((z * x) * (r * r')) * ((z * x) * (r * r'))
        = (z * x) * ((r * r') * (z * x)) * (r * r') := by group
      _ = (z * x) * ((z * x) * (r * r')) * (r * r') := by rw [← hvδ]
      _ = ((z * x) * (z * x)) * ((r * r') * (r * r')) := by group
      _ = 1 := by rw [F.v_sq, hδ2, one_mul]
  have hvδs : ((z * x) * (r * r')) * s = s * ((z * x) * (r * r')) := by
    calc ((z * x) * (r * r')) * s = (z * x) * ((r * r') * s) := by group
      _ = (z * x) * (s * (r * r')) := by rw [hδs]
      _ = ((z * x) * s) * (r * r') := by group
      _ = (s * (z * x)) * (r * r') := by rw [hvs]
      _ = s * ((z * x) * (r * r')) := by group
  have k1 := key (z * x) hvT F.v_sq hvs
  have k2 := key (r * r') hδT hδ2 hδs
  have k3 := key ((z * x) * (r * r')) (T.mul_mem hvT hδT) hvδ2 hvδs
  have hu₁ : OmegaX x (z * x) (g⁻¹ * (z * x) * g) :=
    omegaX_pull hg F.v_sq hvs (IsConj.refl _) k1
  have hu₂ : OmegaX x (z * x) (g⁻¹ * (r * r') * g) :=
    omegaX_pull hg hδ2 hδs hδv.symm k2
  have hu₁₂ : OmegaX x (z * x) ((g⁻¹ * (z * x) * g) * (g⁻¹ * (r * r') * g)) := by
    have e : (g⁻¹ * (z * x) * g) * (g⁻¹ * (r * r') * g) = g⁻¹ * ((z * x) * (r * r')) * g := by
      group
    rw [e]
    exact omegaX_pull hg hvδ2 hvδs hδvv.symm k3
  have hc : (g⁻¹ * (z * x) * g) * (g⁻¹ * (r * r') * g) =
      (g⁻¹ * (r * r') * g) * (g⁻¹ * (z * x) * g) := by
    calc (g⁻¹ * (z * x) * g) * (g⁻¹ * (r * r') * g) = g⁻¹ * ((z * x) * (r * r')) * g := by group
      _ = g⁻¹ * ((r * r') * (z * x)) * g := by rw [hvδ]
      _ = (g⁻¹ * (r * r') * g) * (g⁻¹ * (z * x) * g) := by group
  exact F.omega_pair_false hG hs e7 hP2 hQ4 hu₁ hu₂ hc hu₁₂

end Frame

end CFSG.GH74.GLS.Th2.P43f
