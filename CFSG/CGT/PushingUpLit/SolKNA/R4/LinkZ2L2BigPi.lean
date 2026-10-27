module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigPiB
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigPiN
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big8

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Gen

theorem edgeCent_isPGroup {Y : Type} [Group Y] [Finite Y] (P : Sylow 2 Y) (t u : Y) :
    IsPGroup 2 ↥(edgeCent (P : Subgroup Y) t u) :=
  P.isPGroup'.to_le fun _ hx => hx.1.1

theorem Z2BigLinkModel.padicValNat_f_add_two_le {r : ℕ} (hr : 4 ≤ r) {X : Type} [Group X] [Finite X]
    {p f : ℕ} (hm : Z2BigLinkModel r X p f) : padicValNat 2 f + 2 ≤ r :=
  padicValNat_add_two_le (by omega) (hm.prime.odd_of_ne_two hm.odd) hm.even hm.arith

end Gen

section Cit3

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem Z2SetR.lieLinkSectionR (hs : Z2SetR r n R S t J u R₀ T₀ P) :
    LieLinkSectionR r (linkFam R t) :=
  ⟨(typeRFam_coreLinkFam hs.large).restrict _, oddCore_linkGrp_eq_bot hs.large,
    omegaGen_linkRestrict, hs.z2.1⟩

theorem Z2SetR.exists_linkModel (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    (hArith : Z2BigModelArith r) : ∃ p f : ℕ, Z2BigLinkModel r ↥(linkGrp R t) p f := by
  obtain ⟨p, f, hp, hp2, hf, -, hk⟩ := hs.model
  exact ⟨p, f, hs.simple, hs.index, hp, hp2, hf, hk,
    hArith hr _ (linkFam R t) hs.lieLinkSectionR hs.simple hs.index p f hp hp2 hf hk⟩

theorem Z2SetR.exists_quat_T₀ (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r) :
    ∃ e : ↥T₀ ≃* QuaternionGroup (2 ^ (r - 2)), quatInvolution r e = u := by
  obtain ⟨e⟩ := (TightLargeHypR.typeRFam hs.large).quat J hs.hJ.1 T₀ hs.hT₀
  exact ⟨e, quatInvolution_eq_of_uniqueInvolution hr hs.hu hs.hT₀.1 e⟩

theorem Z2SetR.exists_quat_R₀ (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r) :
    ∃ e : ↥R₀ ≃* QuaternionGroup (2 ^ (r - 2)), quatInvolution r e = t := by
  obtain ⟨e⟩ := (TightLargeHypR.typeRFam hs.large).quat (tightCore R)
    (CoreAssembly.mem_conjClass_self _) R₀ hs.hR₀
  exact ⟨e, quatInvolution_eq_of_uniqueInvolution hr hs.large.datum.isUniqueInvolution_core
    hs.hR₀.1 e⟩

theorem Z2SetR.pi_t_cyc (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    (hCyc : Z2BigModelPiCyc r) {p f : ℕ} (hm : Z2BigLinkModel r ↥(linkGrp R t) p f) {x : Y}
    (hx : x ∈ edgeCent (P : Subgroup Y) t u) {K : ℕ} (hK : padicValNat 2 f < K)
    (h1 : ActsTriv (linkLayer R t) (x ^ 2 ^ K))
    (h2 : ¬ ActsTriv (linkLayer R t) (x ^ 2 ^ (K - 1))) :
    ActsLike (linkLayer R t) (x ^ 2 ^ (K - 1)) u := by
  obtain ⟨e, he⟩ := hs.exists_quat_T₀ hr
  exact pi_cyc_of_concl (A' := edgeCent (P : Subgroup Y) t u) hs.T₀_le_linkLayer hs.hT₀.2.1 e he
    (fun y hy => hs.mem_normalizer_linkLayer hy.1.2) (edgeCent_isPGroup P t u)
    (fun y hy z hz => hs.conj_mem_T₀ hy.1.1 hy.2 hz)
    (piCycConcl_congr (linkLayerEquiv hs.large) (piCycConcl_of_model hCyc hr hm)) hx hK h1 h2

theorem Z2SetR.pi_t_quat (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    (hQuat : Z2BigModelPiQuat r) {p f : ℕ} (hm : Z2BigLinkModel r ↥(linkGrp R t) p f)
    {B : Subgroup Y} (hB : B ≤ edgeCent (P : Subgroup Y) t u) {m : ℕ} (hm1 : 1 ≤ m)
    (eB : ↥B ≃* QuaternionGroup (2 ^ m))
    (hinj : ∀ y ∈ B, ActsTriv (linkLayer R t) y → y = 1) :
    ActsLike (linkLayer R t)
      ((eB.symm (QuaternionGroup.a ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m))) : ↥B) : Y) u := by
  obtain ⟨e, he⟩ := hs.exists_quat_T₀ hr
  exact pi_quat_of_concl (A' := edgeCent (P : Subgroup Y) t u) hs.T₀_le_linkLayer hs.hT₀.2.1 e he
    (fun y hy => hs.mem_normalizer_linkLayer hy.1.2) (edgeCent_isPGroup P t u)
    (fun y hy z hz => hs.conj_mem_T₀ hy.1.1 hy.2 hz)
    (piQuatConcl_congr (linkLayerEquiv hs.large) (piQuatConcl_of_model hQuat hr hm)) hm1 hB eB
    hinj

theorem Z2SetR.pi_t_pi4_involution (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    (hPi4 : Z2BigModelPi4 r) {p f : ℕ} (hm : Z2BigLinkModel r ↥(linkGrp R t) p f) {x : Y}
    (hx : x ∈ edgeCent (P : Subgroup Y) t u) {L : ℕ} (hL : 2 ≤ L) (hxL : x ^ 2 ^ L = 1) :
    ActsTriv (linkLayer R t) (x ^ 2 ^ (L - 1)) ∨ ActsLike (linkLayer R t) (x ^ 2 ^ (L - 1)) u ∨
      ¬ InnerModOdd (linkLayer R t) (x ^ 2 ^ (L - 1)) := by
  obtain ⟨e, he⟩ := hs.exists_quat_T₀ hr
  exact pi4_involution_of_concl (A' := edgeCent (P : Subgroup Y) t u) hs.T₀_le_linkLayer
    hs.hT₀.2.1 e he
    (fun y hy => hs.mem_normalizer_linkLayer hy.1.2) (edgeCent_isPGroup P t u)
    (fun y hy z hz => hs.conj_mem_T₀ hy.1.1 hy.2 hz)
    (pi4Concl_congr (linkLayerEquiv hs.large) (pi4Concl_of_model hPi4 hr hm)) hx hL hxL

theorem Z2SetR.pi_u_cyc (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    (hCyc : Z2BigModelPiCyc r) {p f : ℕ} (hm : Z2BigLinkModel r ↥(linkGrp R t) p f) {x : Y}
    (hx : x ∈ edgeCent (P : Subgroup Y) t u) {K : ℕ} (hK : padicValNat 2 f < K)
    (h1 : ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) (x ^ 2 ^ K))
    (h2 : ¬ ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) (x ^ 2 ^ (K - 1))) :
    ActsLike (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) (x ^ 2 ^ (K - 1)) t := by
  obtain ⟨e, he⟩ := hs.exists_quat_R₀ hr
  obtain ⟨g, -, -, hΛ⟩ := hs.exists_linkLayerAt_eq
  have hQΛ := hs.R₀_le_linkLayerAt
  have hN : ∀ y ∈ edgeCent (P : Subgroup Y) t u, y ∈ Subgroup.normalizer
      ((linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u : Subgroup Y) : Set Y) :=
    fun y hy => hs.mem_normalizer_linkLayerAt hy.2
  rw [hΛ] at hQΛ hN h1 h2 ⊢
  exact pi_cyc_of_concl hQΛ hs.hR₀.2.1 e he hN (edgeCent_isPGroup P t u)
    (fun y hy z hz => hs.conj_mem_R₀ hy.1.1 hy.1.2 hz)
    (piCycConcl_congr (conjQuotEquiv g (linkLayer R t))
      (piCycConcl_congr (linkLayerEquiv hs.large) (piCycConcl_of_model hCyc hr hm))) hx hK h1 h2

theorem Z2SetR.pi_u_quat (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    (hQuat : Z2BigModelPiQuat r) {p f : ℕ} (hm : Z2BigLinkModel r ↥(linkGrp R t) p f)
    {B : Subgroup Y} (hB : B ≤ edgeCent (P : Subgroup Y) t u) {m : ℕ} (hm1 : 1 ≤ m)
    (eB : ↥B ≃* QuaternionGroup (2 ^ m))
    (hinj : ∀ y ∈ B, ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) y →
      y = 1) :
    ActsLike (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)
      ((eB.symm (QuaternionGroup.a ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m))) : ↥B) : Y) t := by
  obtain ⟨e, he⟩ := hs.exists_quat_R₀ hr
  obtain ⟨g, -, -, hΛ⟩ := hs.exists_linkLayerAt_eq
  have hQΛ := hs.R₀_le_linkLayerAt
  have hN : ∀ y ∈ edgeCent (P : Subgroup Y) t u, y ∈ Subgroup.normalizer
      ((linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u : Subgroup Y) : Set Y) :=
    fun y hy => hs.mem_normalizer_linkLayerAt hy.2
  rw [hΛ] at hQΛ hN hinj ⊢
  exact pi_quat_of_concl hQΛ hs.hR₀.2.1 e he hN (edgeCent_isPGroup P t u)
    (fun y hy z hz => hs.conj_mem_R₀ hy.1.1 hy.1.2 hz)
    (piQuatConcl_congr (conjQuotEquiv g (linkLayer R t))
      (piQuatConcl_congr (linkLayerEquiv hs.large) (piQuatConcl_of_model hQuat hr hm))) hm1 hB eB
    hinj

theorem Z2SetR.pi_u_pi4_involution (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    (hPi4 : Z2BigModelPi4 r) {p f : ℕ} (hm : Z2BigLinkModel r ↥(linkGrp R t) p f) {x : Y}
    (hx : x ∈ edgeCent (P : Subgroup Y) t u) {L : ℕ} (hL : 2 ≤ L) (hxL : x ^ 2 ^ L = 1) :
    ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) (x ^ 2 ^ (L - 1)) ∨
      ActsLike (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) (x ^ 2 ^ (L - 1)) t ∨
      ¬ InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)
        (x ^ 2 ^ (L - 1)) := by
  obtain ⟨e, he⟩ := hs.exists_quat_R₀ hr
  obtain ⟨g, -, -, hΛ⟩ := hs.exists_linkLayerAt_eq
  have hQΛ := hs.R₀_le_linkLayerAt
  have hN : ∀ y ∈ edgeCent (P : Subgroup Y) t u, y ∈ Subgroup.normalizer
      ((linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u : Subgroup Y) : Set Y) :=
    fun y hy => hs.mem_normalizer_linkLayerAt hy.2
  rw [hΛ] at hQΛ hN ⊢
  exact pi4_involution_of_concl hQΛ hs.hR₀.2.1 e he hN (edgeCent_isPGroup P t u)
    (fun y hy z hz => hs.conj_mem_R₀ hy.1.1 hy.1.2 hz)
    (pi4Concl_congr (conjQuotEquiv g (linkLayer R t))
      (pi4Concl_congr (linkLayerEquiv hs.large) (pi4Concl_of_model hPi4 hr hm))) hx hL hxL

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
