module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L113Lift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L113Frame

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint Equiv

variable {G : Type} [Group G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 T : Subgroup G}
  {Alt : Subgroup (Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}

theorem sec113_Q_eq [Finite G] (hp : Asc82Pre11) (hctx : Sec10Ctx G t L S z K1 K2) :
    secQ K1 K2 = twoCoreIn K1 ⊔ twoCoreIn K2 :=
  sec10KS_twoCore_sup hp.facts.pockets5 hp.facts.centZ5
    (hp.basic G t L S z hctx.toSec10Z).1 hctx

theorem sec113_sq_mem {Q1 Q2 : Subgroup G} (P : Sec11Q8Pair z Q1 Q2) {q : G}
    (hq : q ∈ Q1 ⊔ Q2) : q * q ∈ zpowers z := by
  obtain ⟨q1, hq1, q2, hq2, rfl⟩ := P.exists_mul_of_mem_sup hq
  have h1 : q1 * q1 ∈ zpowers z := (P.elem1 q1 hq1 q1 hq1).2
  have h2 : q2 * q2 ∈ zpowers z := (P.elem2 q2 hq2 q2 hq2).2
  have e : q1 * q2 * (q1 * q2) = (q1 * q1) * (q2 * q2) := by
    calc q1 * q2 * (q1 * q2) = q1 * (q2 * q1) * q2 := by group
      _ = q1 * (q1 * q2) * q2 := by rw [P.comm q1 hq1 q2 hq2]
      _ = (q1 * q1) * (q2 * q2) := by group
  rw [e]
  exact (zpowers z).mul_mem h1 h2

theorem sec113_seedA [Finite G] (hp : Asc82Pre11) {R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) (hm : Sec11Model t L S z K1 K2 T Alt φ) :
    ∃ y ∈ secM t S L, y * y = 1 ∧ hm.perm.rho y = swap 2 3 * swap 4 5 := by
  have hTM := sec113_T_le_M hctx
  have hQT := sec113_Q_le_T hp hctx
  have hs : swap (2 : Fin 6) 3 * swap 4 5 ∈ sec11V4 := by
    unfold sec11V4
    decide
  obtain ⟨q, hq, hact⟩ := hm.Q_act_surj _ hs
  have hqM : q ∈ secM t S L := hTM (hQT hq)
  have hρq : hm.perm.rho q = swap 2 3 * swap 4 5 := hm.perm.rho_eq hqM _ hact
  have hF := sec113_frame hp hctx.toSec10Ctx
  have hsq : q * q ∈ zpowers z :=
    sec113_sq_mem hF.pair (by rw [← sec113_Q_eq hp hctx.toSec10Ctx]; exact hq)
  by_cases hq1 : q * q = 1
  · exact ⟨q, hqM, hq1, hρq⟩
  · have hqq : q * q = z := (hF.pair.mem_zpowers_iff.mp hsq).resolve_left hq1
    obtain ⟨p, hpdef⟩ : ∃ p : G, p = φ (Pi.single 2 1 + Pi.single 4 1) := ⟨_, rfl⟩
    have hpA : p ∈ secA t S L := by rw [hpdef]; exact hm.perm.mem _
    have hpM : p ∈ secM t S L := Subgroup.le_normalizer hpA
    have hqp : q * p * q⁻¹ = z * p := by
      rw [hpdef, hact, sec113_seed_vec, hm.perm.mul, hm.perm.mul,
        (hm.perm.ker _).2 (Or.inr rfl), mul_one, ← sec113_z_eq hm]
    have hzp : z * p = p * z := by
      rw [sec113_z_eq hm, hpdef]
      exact hm.perm.comm _ _
    refine ⟨q * p, (secM t S L).mul_mem hqM hpM, ?_, ?_⟩
    · calc q * p * (q * p) = (q * p * q⁻¹) * (q * q) * p := by group
        _ = (z * p) * z * p := by rw [hqp, hqq]
        _ = z * (p * z) * p := by group
        _ = z * (z * p) * p := by rw [← hzp]
        _ = (z * z) * (p * p) := by group
        _ = 1 := by
          rw [hF.pair.z_sq, hpdef, hm.perm.sq]
          group
    · rw [hm.perm.rho_mul hqM hpM, sec113_rho_of_mem_A hm hpA, mul_one, hρq]

theorem sec113_conj_seed (hm : Sec11Model t L S z K1 K2 T Alt φ) {y : G}
    (hyM : y ∈ secM t S L) (hy2 : y * y = 1) {g τ : Perm (Fin 6)} (hg : g ∈ Alt)
    (hgτ : g * hm.perm.rho y * g⁻¹ = τ) :
    ∃ y1 ∈ secM t S L, y1 * y1 = 1 ∧ hm.perm.rho y1 = τ := by
  obtain ⟨m, hmM, hact⟩ := hm.perm.act_surj g hg
  have hρm : hm.perm.rho m = g := hm.perm.rho_eq hmM g hact
  refine ⟨m * y * m⁻¹, (secM t S L).mul_mem ((secM t S L).mul_mem hmM hyM)
    ((secM t S L).inv_mem hmM), ?_, ?_⟩
  · calc m * y * m⁻¹ * (m * y * m⁻¹) = m * (y * y) * m⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  · rw [hm.perm.rho_mul ((secM t S L).mul_mem hmM hyM) ((secM t S L).inv_mem hmM),
      hm.perm.rho_mul hmM hyM, hρm, sec113_rho_inv hm hmM, hρm]
    exact hgτ

end CFSG.OddStandard.SmallF3.Omega
