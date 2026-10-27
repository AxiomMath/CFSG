module

public import CFSG.LocalAnalysis.EvenBN.Tits.Model.HypStar
public import Certificates.Certificate27000

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Model

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open Certificates.TitsAschbacherStar
open CFSG.Quasithin.RuRank3 (titsAux titsAuxArr titsAux_mem titsAux_not_mem_D titsAux_comm
  rep_titsAux mem_titsCNt_of_mem_D)

theorem starCheck_eq_true : starCheck = true :=
  Certificates.certificate27000

theorem starWit_mem : starWit ∈ titsCNt := by
  rw [starWit, List.getD_eq_getElem _ _ (by rw [titsCNt_check.2.1]; decide)]
  exact List.getElem_mem _

theorem exists_starWit :
    ∃ w : Equiv.Perm (Fin 1755), Rep 1755 starWit w ∧ w ∈ titsD ∧
      w * titsTInv = titsTInv * w := by
  obtain ⟨hinv, hcomm, hN⟩ := titsCNt_facts starWit_mem
  have hw := (rep_permOfArr hinv).1
  exact ⟨_, hw, titsN_le_titsD (mem_titsN_of_sift hw hN), (commA_iff hw titsTInv_rep).1 hcomm⟩

theorem exists_conj_not_mem_zpowers_of_starOK
    {a : Array ℕ}
    {u : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a u) (hok : starOK a = true)
    (hu : u ^ 2 = titsTInv) :
    ∃ c ∈ titsD, c * titsTInv = titsTInv * c ∧ c * u * c⁻¹ ∉ zpowers u := by
  obtain ⟨w, hw, hwD, hwt⟩ := exists_starWit
  have hsq : eqA 1755 (compA 1755 a a) titsTArr = true :=
    (eqA_iff (rep_compA ha ha) titsTInv_rep).2 (by rw [← hu, sq])
  rw [starOK, hsq, Bool.not_true, Bool.false_or, escapes, Bool.and_eq_true,
    Bool.not_eq_true', Bool.not_eq_true'] at hok
  obtain ⟨h1, h2⟩ := hok
  refine ⟨w, hwD, hwt, fun hmem => ?_⟩
  have hu4 : u ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, hu, sq, titsTInv_mul_self]
  have hw2 : (w * u * w⁻¹) ^ 2 = u ^ 2 := by
    rw [conj_pow, hu, hwt, mul_inv_cancel_right]
  rcases eq_or_eq_inv_of_sq_eq hu4 (hu ▸ titsTInv_ne_one) hmem hw2 with h | h
  · have hc : w * u = u * w := by
      calc w * u = w * u * w⁻¹ * w := by group
        _ = u * w := by rw [h]
    rw [(commA_iff hw ha).2 hc] at h1
    exact Bool.true_eq_false.mp h1
  · have hc : u * w * u = w := by
      calc u * w * u = u * (w * u * w⁻¹) * w * u⁻¹ * u := by group
        _ = w := by rw [h]; group
    rw [(eqA_iff (rep_compA (rep_compA ha hw) ha) hw).2 hc] at h2
    exact Bool.true_eq_false.mp h2

theorem exists_rep_of_comm_titsTInv
    {u : Equiv.Perm (Fin 1755)}
    (huA : u ∈ titsA) (hut : u * titsTInv = titsTInv * u) :
    ∃ c ∈ titsCNt, Rep 1755 c u ∨ Rep 1755 (compA 1755 titsAuxArr c) u := by
  by_cases huD : u ∈ titsD
  · obtain ⟨c, hc, rfl⟩ := mem_titsCNt_of_mem_D huD hut
    exact ⟨c, hc, Or.inl (rep_permOfArr (titsCNt_facts hc).1).1⟩
  · have hcD : titsAux⁻¹ * u ∈ titsD :=
      (mul_mem_titsD_iff (inv_mem titsAux_mem) huA).2
        (iff_of_false (fun h => titsAux_not_mem_D (by simpa using inv_mem h)) huD)
    have hcomm : titsAux⁻¹ * u * titsTInv = titsTInv * (titsAux⁻¹ * u) := by
      have h1 : titsAux⁻¹ * titsTInv = titsTInv * titsAux⁻¹ :=
        (Commute.inv_left (show Commute titsAux titsTInv from titsAux_comm)).eq
      rw [mul_assoc, hut, ← mul_assoc, h1, mul_assoc]
    obtain ⟨c, hc, hcu⟩ := mem_titsCNt_of_mem_D hcD hcomm
    refine ⟨c, hc, Or.inr ?_⟩
    have := rep_compA rep_titsAux (rep_permOfArr (titsCNt_facts hc).1).1
    rwa [hcu, ← mul_assoc, mul_inv_cancel, one_mul] at this

theorem shortStarEscape :
    ShortStarEscape := by
  intro u huA hu
  have hut : u * titsTInv = titsTInv * u := by
    rw [← hu]
    group
  obtain ⟨c, hc, hrep⟩ := exists_rep_of_comm_titsTInv huA hut
  have h := starCheck_eq_true
  rw [starCheck, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ ▸ h c hc
  rcases hrep with hr | hr
  · exact exists_conj_not_mem_zpowers_of_starOK hr h1 hu
  · exact exists_conj_not_mem_zpowers_of_starOK hr h2 hu

theorem hypothesisOneStar_titsD :
    CFSG.SeitzReduction.RankOne.HypothesisOneStar titsD :=
  hypothesisOneStar_of_shortStarEscape shortStarEscape

theorem kernel_eq_zpowers_of_hyp
    {G : Type} [Group G] [Finite G] {d : Data G} (hd : d.Hyp) :
    centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) = zpowers d.t :=
  kernel_eq_zpowers_of_shortStarEscape hd shortStarEscape

theorem ker_ρ_eq_zpowers_of_hyp
    {G : Type} [Group G] [Finite G] {d : Data G} (hd : d.Hyp) :
    d.ρ.ker.map (centralizer ({d.t} : Set G)).subtype = zpowers d.t :=
  hd.ker_ρ_eq_zpowers hypothesisOneStar_titsD

end CFSG.LocalAnalysis.EvenBN.Tits.Model
