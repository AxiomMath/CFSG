module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big3
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big32
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big18
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigPi

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Defs

variable {Y : Type} [Group Y]

@[expose] def ActsInE (R : Subgroup Y) (t : Y) (J : Subgroup Y) (u : Y) (w : Y) : Prop :=
  (ActsTriv (linkLayer R t) w ∨ ActsLike (linkLayer R t) w u) ∧
    (ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) w ∨
      ActsLike (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) w t)

theorem actsTriv_one' (Λ : Subgroup Y) : ActsTriv Λ 1 := by
  intro z hz
  simpa using (oddCoreOf Λ).one_mem

theorem actsTriv_symm_a_of_not_forall {B Λ : Subgroup Y} {m : ℕ}
    (eB : ↥B ≃* QuaternionGroup (2 ^ m))
    (hN : ∀ y ∈ B, y ∈ Subgroup.normalizer (Λ : Set Y))
    (hinj : ¬ ∀ y ∈ B, ActsTriv Λ y → y = 1) :
    ActsTriv Λ
      ((eB.symm (QuaternionGroup.a ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m))) : ↥B) : Y) := by
  classical
  push Not at hinj
  obtain ⟨y, hyB, hy', hy1⟩ := hinj
  have heB1 : eB ⟨y, hyB⟩ ≠ 1 := by
    intro h
    apply hy1
    have hsub : (⟨y, hyB⟩ : ↥B) = 1 := by
      apply eB.injective
      rw [h, map_one]
    simpa using congrArg Subtype.val hsub
  obtain ⟨k, hk⟩ := QuatAutH.exists_pow_eq_center (eB ⟨y, hyB⟩) heB1
  have hk' : y ^ k =
      ((eB.symm (QuaternionGroup.a ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m))) : ↥B) : Y) := by
    have hcongr := congrArg eB.symm hk
    rw [map_pow, MulEquiv.symm_apply_apply] at hcongr
    have hval := congrArg (fun z : ↥B => (z : Y)) hcongr
    simpa using hval
  rw [← hk']
  exact actsTriv_pow (hN y hyB) hy' k

end Defs

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem Z2SetR.mem_E_of_actsInE (hs : Z2SetR r n R S t J u R₀ T₀ P) {w : Y}
    (hw : w ∈ edgeCent (P : Subgroup Y) t u) (h : ActsInE R t J u w) :
    w ∈ Subgroup.closure ({t, u} : Set Y) := by
  obtain ⟨h1, h2⟩ := h
  have ctu := hs.comm_t_u
  have ht := hs.large.datum.isUniqueInvolution_core
  have htE : t ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have huE : u ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have htΛ : t ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u :=
    hs.R₀_le_linkLayerAt hs.t_mem_R₀
  have huΛ : u ∈ linkLayer R t := hs.T₀_le_linkLayer hs.u_mem_T₀
  have hΛt : ∀ y ∈ linkLayer R t, t * y = y * t := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer hy)).symm
  have hΛu : ∀ y ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u, u * y = y * u :=
    fun y hy => (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer hy)).symm
  have key : ∀ e ∈ Subgroup.closure ({t, u} : Set Y),
      ActsTriv (linkLayer R t) (w * e) →
      ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) (w * e) →
        w ∈ Subgroup.closure ({t, u} : Set Y) := by
    intro e he h1' h2'
    have h3 := hs.eq_one_of_actsTriv
      ((edgeCent (P : Subgroup Y) t u).mul_mem hw (hs.aux_E_le he)) h1' h2'
    rw [eq_inv_of_mul_eq_one_left h3]
    exact Subgroup.inv_mem _ he
  by_cases hwt : ActsTriv (linkLayer R t) w
  · by_cases hwu : ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) w
    · exact key 1 (Subgroup.one_mem _) (by rw [mul_one]; exact hwt)
        (by rw [mul_one]; exact hwu)
    · exact key t htE (actsTriv_mul_of_comm hΛt hwt)
        (actsTriv_mul_of_actsLike htΛ ht.sq (h2.resolve_left hwu))
  · have htlike : ActsLike (linkLayer R t) w u := h1.resolve_left hwt
    by_cases hwu : ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) w
    · exact key u huE (actsTriv_mul_of_actsLike huΛ hs.hu.sq htlike) (actsTriv_mul_of_comm hΛu hwu)
    · refine key (u * t) (Subgroup.mul_mem _ huE htE) ?_ ?_
      · rw [← mul_assoc]
        exact actsTriv_mul_of_comm hΛt (actsTriv_mul_of_actsLike huΛ hs.hu.sq htlike)
      · rw [← ctu, ← mul_assoc]
        exact actsTriv_mul_of_comm hΛu
          (actsTriv_mul_of_actsLike htΛ ht.sq (h2.resolve_left hwu))

theorem Z2SetR.actsInE_of_cyc (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r) {x : Y}
    (hx : x ∈ edgeCent (P : Subgroup Y) t u) (hx1 : x ^ 2 ^ (r - 1) = 1) :
    ActsInE R t J u (x ^ 2 ^ (r - 2)) := by
  obtain ⟨p, f, hm⟩ := hs.exists_linkModel hr (z2BigModelArith_holds r)
  have hE : padicValNat 2 f + 2 ≤ r := hm.padicValNat_f_add_two_le hr
  have hKlt : padicValNat 2 f < r - 1 := by omega
  have hsub : r - 1 - 1 = r - 2 := by omega
  have h1t : ActsTriv (linkLayer R t) (x ^ 2 ^ (r - 1)) := by
    rw [hx1]; exact actsTriv_one' _
  have h1u : ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)
      (x ^ 2 ^ (r - 1)) := by
    rw [hx1]; exact actsTriv_one' _
  refine ⟨?_, ?_⟩
  · by_cases ht : ActsTriv (linkLayer R t) (x ^ 2 ^ (r - 2))
    · exact Or.inl ht
    · refine Or.inr ?_
      have h2t : ¬ ActsTriv (linkLayer R t) (x ^ 2 ^ (r - 1 - 1)) := by
        simpa [hsub] using ht
      have hlike := hs.pi_t_cyc hr (z2BigModelPiCyc_holds r) hm hx (K := r - 1) hKlt h1t h2t
      simpa [hsub] using hlike
  · by_cases hu : ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)
        (x ^ 2 ^ (r - 2))
    · exact Or.inl hu
    · refine Or.inr ?_
      have h2u : ¬ ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)
          (x ^ 2 ^ (r - 1 - 1)) := by
        simpa [hsub] using hu
      have hlike := hs.pi_u_cyc hr (z2BigModelPiCyc_holds r) hm hx (K := r - 1) hKlt h1u h2u
      simpa [hsub] using hlike

theorem Z2SetR.actsInE_of_quat (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    {B : Subgroup Y} (hB : B ≤ edgeCent (P : Subgroup Y) t u) {m : ℕ} (hm1 : 1 ≤ m)
    (eB : ↥B ≃* QuaternionGroup (2 ^ m)) :
    ActsInE R t J u
      ((eB.symm (QuaternionGroup.a ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m))) : ↥B) : Y) := by
  obtain ⟨p, f, hm⟩ := hs.exists_linkModel hr (z2BigModelArith_holds r)
  refine ⟨?_, ?_⟩
  · by_cases hinj : ∀ y ∈ B, ActsTriv (linkLayer R t) y → y = 1
    · exact Or.inr (hs.pi_t_quat hr (z2BigModelPiQuat_holds r) hm hB hm1 eB hinj)
    · exact Or.inl (actsTriv_symm_a_of_not_forall eB
        (fun y hy => hs.mem_normalizer_linkLayer (hB hy).1.2) hinj)
  · by_cases hinj : ∀ y ∈ B,
        ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) y → y = 1
    · exact Or.inr (hs.pi_u_quat hr (z2BigModelPiQuat_holds r) hm hB hm1 eB hinj)
    · exact Or.inl (actsTriv_symm_a_of_not_forall eB
        (fun y hy => hs.mem_normalizer_linkLayerAt (hB hy).2) hinj)

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
