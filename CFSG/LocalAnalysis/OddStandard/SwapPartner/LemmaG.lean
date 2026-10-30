module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.LemmaGSylow
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.LemmaGPair
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.LemmaGSelfNorm
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.LemmaGAut

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G}

private theorem tau0_apply_nine : τ₀ 9 = 8 := by
  simpa [τ₀] using Equiv.swap_apply_right (8 : Fin 10) 9

private theorem tau0_comm_apply_eight {σ : Perm (Fin 10)} (hc : σ * τ₀ = τ₀ * σ) :
    σ 8 = 8 ∨ σ 8 = 9 := by
  by_contra h
  push Not at h
  obtain ⟨h8, h9⟩ := h
  have hkey : σ 9 = σ 8 := by
    have h := congrArg (fun f : Perm (Fin 10) => f 8) hc
    simp only [Equiv.Perm.mul_apply] at h
    rw [τ₀_apply_eight] at h
    have hτ : τ₀ (σ 8) = σ 8 := by
      simpa only [τ₀] using Equiv.swap_apply_of_ne_of_ne h8 h9
    rwa [hτ] at h
  exact absurd (σ.injective hkey) (by decide)

private theorem exists_liftS8_or_tau0_mul_of_comm {σ : Perm (Fin 10)}
    (hc : σ * τ₀ = τ₀ * σ) :
    (∃ ρ : Perm (Fin 8), liftS8 ρ = σ) ∨ (∃ ρ : Perm (Fin 8), τ₀ * liftS8 ρ = σ) := by
  rcases tau0_comm_apply_eight hc with h8 | h8
  · left
    have h9 : σ 9 = 9 := by
      have h := congrArg (fun f : Perm (Fin 10) => f 8) hc
      simp only [Equiv.Perm.mul_apply] at h
      rw [τ₀_apply_eight, h8, τ₀_apply_eight] at h
      exact h
    exact mem_stab2_iff_exists_liftS8.1 (mem_stab2.2 ⟨h8, h9⟩)
  · right
    have h9 : σ 9 = 8 := by
      have h := congrArg (fun f : Perm (Fin 10) => f 8) hc
      simp only [Equiv.Perm.mul_apply] at h
      rw [τ₀_apply_eight, h8, tau0_apply_nine] at h
      exact h
    have hstab : τ₀ * σ ∈ stab2 8 9 := by
      rw [mem_stab2]
      refine ⟨?_, ?_⟩
      · show (τ₀ * σ) 8 = 8
        rw [Equiv.Perm.mul_apply, h8, tau0_apply_nine]
      · show (τ₀ * σ) 9 = 9
        rw [Equiv.Perm.mul_apply, h9, τ₀_apply_eight]
    obtain ⟨ρ, hρ⟩ := mem_stab2_iff_exists_liftS8.1 hstab
    refine ⟨ρ, ?_⟩
    rw [hρ, ← mul_assoc, τ₀_mul_self, one_mul]

theorem exists_gElt_normalizer_Tgrp [Finite G] (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (hP2 : ¬ IsConj z (z * ι τ₀)) {Q : Subgroup (Perm (Fin 10))} (hQ : GoodQ Q) :
    ∃ g : G, GElt z ι g ∧ g ∈ normalizer ((Tgrp z ι Q : Subgroup G) : Set G) := by
  classical
  obtain ⟨g₀, hg₀N, hz₀⟩ := exists_normalizer_Tgrp_swap hC hx hQ
  obtain ⟨hx₀, _hζ₀⟩ := swap_ζ_of_normalizer_Tgrp hC hx hP2 hQ hg₀N hz₀
  obtain ⟨σ, hσ⟩ := exists_conj_action_of_swap hC hz₀ hx₀
  have key : ∀ p : Perm (Fin 8), liftS8 p ∈ Q → liftS8 (σ * p * σ⁻¹) ∈ Q := by
    intro p hp
    have hpT : ι (liftS8 p) ∈ Tgrp z ι Q :=
      map_le_Tgrp Q (Subgroup.mem_map_of_mem ι hp)
    have hconjT : g₀ * ι (liftS8 p) * g₀⁻¹ ∈ Tgrp z ι Q :=
      (Subgroup.mem_set_normalizer_iff.mp hg₀N (ι (liftS8 p))).mp hpT
    obtain ⟨e, heE, hee⟩ := hσ p
    have heT : e ∈ Tgrp z ι Q := Egrp_le_Tgrp hC hQ heE
    have hmem : e * ι (liftS8 (σ * p * σ⁻¹)) ∈ Tgrp z ι Q := hee ▸ hconjT
    have h1 : e⁻¹ * (e * ι (liftS8 (σ * p * σ⁻¹))) ∈ Tgrp z ι Q :=
      (Tgrp z ι Q).mul_mem ((Tgrp z ι Q).inv_mem heT) hmem
    have h2 : e⁻¹ * (e * ι (liftS8 (σ * p * σ⁻¹))) = ι (liftS8 (σ * p * σ⁻¹)) := by
      group
    have hιT : ι (liftS8 (σ * p * σ⁻¹)) ∈ Tgrp z ι Q := by
      rwa [h2] at h1
    obtain ⟨i, q', hq'Q, hi⟩ := (mem_Tgrp_iff hC).mp hιT
    fin_cases i
    · have hq : liftS8 (σ * p * σ⁻¹) = q' := hC.inj (by simpa using hi)
      rwa [hq]
    · exfalso
      have hz : z = ι (liftS8 (σ * p * σ⁻¹) * q'⁻¹) := by
        have h1 : ι (liftS8 (σ * p * σ⁻¹)) = z * ι q' := by simpa using hi
        calc z = (z * ι q') * (ι q')⁻¹ := by group
          _ = ι (liftS8 (σ * p * σ⁻¹)) * (ι q')⁻¹ := by rw [← h1]
          _ = ι (liftS8 (σ * p * σ⁻¹) * q'⁻¹) := by simp only [map_mul, map_inv]
      exact hC.ne_z _ hz.symm
  have hσQ : liftS8 σ ∈ Q := by
    apply liftS8_mem_of_normalizes hQ
    intro q hq
    have hqcomm : q * τ₀ = τ₀ * q := (hQ.τ₀_comm q hq).symm
    rcases exists_liftS8_or_tau0_mul_of_comm hqcomm with ⟨p, hp⟩ | ⟨p, hp⟩
    · have hpQ : liftS8 p ∈ Q := by rw [hp]; exact hq
      have hk := key p hpQ
      rw [← hp]
      simpa only [map_mul, map_inv] using hk
    · have hpQ : liftS8 p ∈ Q := by
        have hp' : liftS8 p = τ₀ * q := by
          rw [← hp, ← mul_assoc, τ₀_mul_self, one_mul]
        rw [hp']
        exact Q.mul_mem hQ.τ₀_mem hq
      have hk := key p hpQ
      have hq_eq : q = τ₀ * liftS8 p := hp.symm
      rw [hq_eq]
      have hthis : liftS8 σ * (τ₀ * liftS8 p) * (liftS8 σ)⁻¹ =
          τ₀ * liftS8 (σ * p * σ⁻¹) := by
        calc liftS8 σ * (τ₀ * liftS8 p) * (liftS8 σ)⁻¹
            = (liftS8 σ * τ₀) * liftS8 p * (liftS8 σ)⁻¹ := by group
          _ = (τ₀ * liftS8 σ) * liftS8 p * (liftS8 σ)⁻¹ := by rw [liftS8_mul_τ₀ σ]
          _ = τ₀ * (liftS8 σ * liftS8 p * (liftS8 σ)⁻¹) := by group
          _ = τ₀ * liftS8 (σ * p * σ⁻¹) := by rw [map_mul, map_mul, map_inv]
      rw [hthis]
      exact Q.mul_mem hQ.τ₀_mem hk
  refine ⟨(ι (liftS8 σ))⁻¹ * g₀, gElt_of_conj_action hC hz₀ hx₀ hσ, ?_⟩
  have hιT : ι (liftS8 σ) ∈ Tgrp z ι Q :=
    map_le_Tgrp Q (Subgroup.mem_map_of_mem ι hσQ)
  let N : Subgroup G := normalizer ((Tgrp z ι Q : Subgroup G) : Set G)
  have hιN : ι (liftS8 σ) ∈ N := Subgroup.le_normalizer hιT
  exact N.mul_mem (N.inv_mem hιN) hg₀N

theorem exists_gElt [Finite G] (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (hP2 : ¬ IsConj z (z * ι τ₀)) : ∃ g : G, GElt z ι g := by
  obtain ⟨Q, hQ⟩ := exists_goodQ
  obtain ⟨g, hg, -⟩ := exists_gElt_normalizer_Tgrp hC hx hP2 hQ
  exact ⟨g, hg⟩

theorem exists_gElt_sq_one_normalizer_Tgrp [Finite G] (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (hP2 : ¬ IsConj z (z * ι τ₀)) {Q : Subgroup (Perm (Fin 10))} (hQ : GoodQ Q) :
    ∃ g : G, GElt z ι g ∧ g * g = 1 ∧ g ∈ normalizer ((Tgrp z ι Q : Subgroup G) : Set G) := by
  obtain ⟨g, hg, hgN⟩ := exists_gElt_normalizer_Tgrp hC hx hP2 hQ
  rcases GElt.sq_cases hC hg with ⟨hsq, -⟩ | ⟨-, hzgsq⟩
  · exact ⟨g, hg, hsq, hgN⟩
  · have hx1E : ι τ₀ ∈ Egrp z ι := Subgroup.mem_sup_right (Subgroup.mem_zpowers (ι τ₀))
    have hzg : z * g = g * ι τ₀ := by
      rw [← hg.conj_x₁]; group
    have hgzg : GElt z ι (z * g) := by
      rw [hzg]
      exact GElt.mul_mem_Egrp hC hg hx1E
    let N : Subgroup G := normalizer ((Tgrp z ι Q : Subgroup G) : Set G)
    have hzgN : z * g ∈ N := N.mul_mem (Subgroup.le_normalizer (z_mem_Tgrp Q)) hgN
    exact ⟨z * g, hgzg, hzgsq, hzgN⟩

theorem exists_gElt_sq_one [Finite G] (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (hP2 : ¬ IsConj z (z * ι τ₀)) : ∃ g : G, GElt z ι g ∧ g * g = 1 := by
  obtain ⟨Q, hQ⟩ := exists_goodQ
  obtain ⟨g, hg, hsq, -⟩ := exists_gElt_sq_one_normalizer_Tgrp hC hx hP2 hQ
  exact ⟨g, hg, hsq⟩

end CFSG.OddStandard.AltStdSec.SwapPartner
