module

public import CFSG.ClassicalInvolution.Asc77.AscC25H2
public import CFSG.ClassicalInvolution.Asc77.AscC25V10

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25H

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77.C25V
open scoped MatrixGroups commutatorElement

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem conj_t'_mem_normalizer (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') {x : G}
    (hxz : x * z = z * x) (hxK : conjSub x K = K) :
    t' * x * t' ∈ Subgroup.normalizer (K : Set G) := by
  have hxK' : conjSub x K' = K' := (cz_fix_iff h hxz).mp hxK
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  rw [conjSub_mul, conjSub_mul, conjSub_t'_K h, hxK', conjSub_t'_K' h]

theorem triv_conj_mem (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {c y : G}
    (hcz : c * z = z * c) (hy : y ∈ Triv hp hq e z t' h.ht'2) :
    c * y * c⁻¹ ∈ Triv hp hq e z t' h.ht'2 := by
  have htz : t' * z = z * t' := t'_comm_z h
  rcases cz_cover h hcz with hc | hc
  · exact triv_conj_of_normalizer (mem_normalizer_iff_conjSub_eq.mpr hc) hcz
      (conj_t'_mem_normalizer h hcz hc) hy
  · have hc0z : (c * t') * z = z * (c * t') := by
      calc c * t' * z = c * (t' * z) := by rw [mul_assoc]
        _ = c * (z * t') := by rw [htz]
        _ = (c * z) * t' := by rw [mul_assoc]
        _ = (z * c) * t' := by rw [hcz]
        _ = z * (c * t') := by rw [mul_assoc]
    have e1 : c * y * c⁻¹ = (c * t') * (t' * y * t') * (c * t')⁻¹ := by
      rw [mul_inv_rev, h.ht'inv]
      calc c * y * c⁻¹ = c * (t' * t') * y * (t' * t') * c⁻¹ := by rw [h.ht'2]; group
        _ = (c * t') * (t' * y * t') * (t' * c⁻¹) := by group
    rw [e1]
    exact triv_conj_of_normalizer (mem_normalizer_iff_conjSub_eq.mpr hc) hc0z
      (conj_t'_mem_normalizer h hc0z hc) (triv_swap htz hy)

theorem conjSub_R_of_mem (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') {s : G}
    (hsS : s ∈ (S : Subgroup G)) (hsK : conjSub s K = K) : conjSub s R = R := by
  rcases h.perm_R hsS with h1 | h1
  · exact h1
  · exfalso
    have hR'K : R' ≤ K := by
      rw [← h1, ← hsK]
      exact conjSub_mono h.hRsyl.1
    have := h.hΩ.eq_of_le_of_le h.hK' h.hK h.hR'syl.2.1
      (by have := h.hqR'.eight_le; omega) h.hR'syl.1 hR'K
    exact h.hs.hne this

theorem commutes_R_of_nuG_eq_one (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {s : G}
    (hsS : s ∈ (S : Subgroup G)) (hsN : s ∈ Subgroup.normalizer (K : Set G))
    (hν : nuG hp hq e s = 1) : ∀ r ∈ R, s * r = r * s := by
  intro r hr
  have hsR : conjSub s R = R := conjSub_R_of_mem h hsS (mem_normalizer_iff_conjSub_eq.mp hsN)
  have h1 : ⁅s, r⁆ ∈ oddCoreOf K := (nuG_eq_one_iff hp hq e hsN).mp hν r (h.hRsyl.1 hr)
  have h2 : ⁅s, r⁆ ∈ R := by
    have h3 : s * r * s⁻¹ ∈ R := by
      have := conj_mem_conjSub (n := s) hr
      rwa [hsR] at this
    rw [commutatorElement_def]
    exact R.mul_mem h3 (R.inv_mem hr)
  have h4 : ⁅s, r⁆ = 1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h1
    (h.hRsyl.2.1.to_le (Subgroup.zpowers_le.mpr h2))
  exact commutatorElement_eq_one_iff_mul_comm.mp h4

end Main

end CFSG.ClassicalInvolution.Asc77.C25H
