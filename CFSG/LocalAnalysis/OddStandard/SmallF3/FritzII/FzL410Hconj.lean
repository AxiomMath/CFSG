module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Set
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.CtxCommute

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private lemma fz410hc_L_le_H {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}
    (h : Ctx t L S x₁ x₂ lam rho tau) : L ≤ invCent t := by
  intro l hl
  rw [invCent, Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp h.hyp.mem_centralizer l hl

private lemma fz410hc_P_le_H {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}
    (h : Ctx t L S x₁ x₂ lam rho tau) : twoCore t ≤ invCent t := by
  rw [← h.hyp.centralizer_eq]
  exact inf_le_right

private lemma fz410hc_P_comm_L {t : G} {L : Subgroup G} (h : Hyp G t L)
    {p l : G} (hp : p ∈ twoCore t) (hl : l ∈ L) : p * l = l * p := by
  have hp' : p ∈ Subgroup.centralizer (L : Set G) := by
    have hmem : p ∈ Subgroup.centralizer (L : Set G) ⊓ invCent t := by
      rw [h.centralizer_eq]
      exact hp
    exact (Subgroup.mem_inf.mp hmem).1
  exact (Subgroup.mem_centralizer_iff.mp hp' l hl).symm

theorem fz410_comm_le_L {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}
    (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2) :
    ∀ a ∈ invCent t, ∀ b ∈ invCent t, a * b * a⁻¹ * b⁻¹ ∈ L := by
  have hLle : L ≤ invCent t := fz410hc_L_le_H h
  have hPle : twoCore t ≤ invCent t := fz410hc_P_le_H h
  have hFle : twoCore t ⊔ L ≤ invCent t := sup_le hPle hLle
  have hmul := Subgroup.relIndex_mul_relIndex (H := L) (K := twoCore t ⊔ L)
    (L := invCent t) le_sup_right hFle
  rw [h.relIndex_two] at hmul
  have hcardK : Nat.card (twoCore t ⊔ L : Subgroup G) =
      Nat.card (twoCore t) * Nat.card L :=
    card_sup_of_commute (fun a ha b hb => fz410hc_P_comm_L h.hyp ha hb) h.hyp.twoCore_inf
  have hrel : L.relIndex (twoCore t ⊔ L) = 2 := by
    have hlag := Subgroup.relIndex_mul_card (H := L) (K := twoCore t ⊔ L)
    rw [inf_eq_left.mpr le_sup_right] at hlag
    rw [hcardK, hK] at hlag
    have hpos : 0 < Nat.card L := by
      haveI : Nonempty ↥L := ⟨⟨1, L.one_mem⟩⟩
      exact Nat.card_pos
    exact Nat.mul_right_cancel hpos hlag
  rw [hrel] at hmul
  haveI : (L.subgroupOf (invCent t)).Normal := h.hyp.normal
  have hLidx : L.relIndex (invCent t) = 4 := by omega
  have hcard4 : Nat.card (↥(invCent t) ⧸ L.subgroupOf (invCent t)) = 4 := hLidx
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsMulCommutative (↥(invCent t) ⧸ L.subgroupOf (invCent t)) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hcard4]; norm_num)
  have hcomm : _root_.commutator ↥(invCent t) ≤ L.subgroupOf (invCent t) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have h2 : ⁅invCent t, invCent t⁆ ≤ L := by
    rw [← Subgroup.map_subtype_commutator (invCent t)]
    calc (_root_.commutator ↥(invCent t)).map (invCent t).subtype
        ≤ (L.subgroupOf (invCent t)).map (invCent t).subtype := Subgroup.map_mono hcomm
      _ = L := Subgroup.map_subgroupOf_eq_of_le hLle
  intro a ha b hb
  exact Subgroup.commutator_le.mp h2 a ha b hb

theorem fz410_E_le_L {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}
    (h : Ctx t L S x₁ x₂ lam rho tau) : baseGrp x₁ x₂ ≤ L := by
  have h1 : baseGrp x₁ x₂ ≤ wreathGrp x₁ x₂ lam := by
    rw [baseGrp, wreathGrp]
    exact Subgroup.closure_mono (by
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
      tauto)
  exact h1.trans (by rw [← h.inf_eq]; exact inf_le_right)

namespace Fz410Set

variable {t : G} {L S T : Subgroup G}
  {x₁ x₂ lam rho tau s : G} {Z E W Q R P : Subgroup G}
  (D : Fz410Set t L S T x₁ x₂ lam rho tau s Z E W Q R P)

include D

theorem Hconj (e : G) (he : e ∈ E) :
    ∃ h ∈ invCent t, h * (t * s) * h⁻¹ = e * (t * s) := by
  have hLle : L ≤ invCent t := fz410hc_L_le_H D.ctx
  have hPle : twoCore t ≤ invCent t := fz410hc_P_le_H D.ctx
  have heL : e ∈ L := by
    have h1 : e ∈ baseGrp x₁ x₂ := by rw [← D.hE]; exact he
    exact fz410_E_le_L D.ctx h1
  have heH : e ∈ invCent t := hLle heL
  have htH : t ∈ invCent t := hPle D.ctx.hyp.mem_twoCore
  have htauH : tau ∈ invCent t := D.ctx.le_invCent D.ctx.tau_mem
  have hsH : s ∈ invCent t := by
    rcases D.s_cases with rfl | rfl
    · exact htauH
    · exact (invCent t).mul_mem htH htauH
  have htsH : t * s ∈ invCent t := (invCent t).mul_mem htH hsH
  have hs_notin_K : s ∉ twoCore t ⊔ L := by
    rcases D.s_cases with rfl | rfl
    · intro hmem
      exact D.ctx.tau_not_mem hmem
    · intro hmem
      have htK : t ∈ twoCore t ⊔ L := Subgroup.mem_sup_left D.ctx.hyp.mem_twoCore
      have h2 : t⁻¹ * (t * tau) ∈ twoCore t ⊔ L :=
        (twoCore t ⊔ L).mul_mem ((twoCore t ⊔ L).inv_mem htK) hmem
      exact D.ctx.tau_not_mem (by simpa using h2)
  have hγH : e * (t * s) ∈ invCent t := (invCent t).mul_mem heH htsH
  have hγ_notin_K : e * (t * s) ∉ twoCore t ⊔ L := by
    intro hmem
    have heL' : e ∈ twoCore t ⊔ L := Subgroup.mem_sup_right heL
    have htK : t ∈ twoCore t ⊔ L := Subgroup.mem_sup_left D.ctx.hyp.mem_twoCore
    have hetK : e * t ∈ twoCore t ⊔ L := (twoCore t ⊔ L).mul_mem heL' htK
    have h2 : (e * t)⁻¹ * (e * (t * s)) ∈ twoCore t ⊔ L :=
      (twoCore t ⊔ L).mul_mem ((twoCore t ⊔ L).inv_mem hetK) hmem
    have h2' : s ∈ twoCore t ⊔ L := by
      rwa [show (e * t)⁻¹ * (e * (t * s)) = s from by group] at h2
    exact hs_notin_K h2'
  have hγsq : (e * (t * s)) ^ 2 ∈ twoCore t := by
    rw [D.ets_sq e he]
    exact one_mem _
  have hts_notin_K : t * s ∉ twoCore t ⊔ L := by
    intro hmem
    have htK : t ∈ twoCore t ⊔ L := Subgroup.mem_sup_left D.ctx.hyp.mem_twoCore
    have h2 : t⁻¹ * (t * s) ∈ twoCore t ⊔ L :=
      (twoCore t ⊔ L).mul_mem ((twoCore t ⊔ L).inv_mem htK) hmem
    exact hs_notin_K (by simpa using h2)
  have hts_sq : (t * s) ^ 2 ∈ twoCore t := by
    have h1 : (1 * (t * s)) ^ 2 = 1 := D.ets_sq 1 (E.one_mem)
    rw [show (1 : G) * (t * s) = t * s from one_mul _] at h1
    rw [h1]
    exact one_mem _
  obtain ⟨h₁, hh₁, p₁, hp₁, hconj₁⟩ :=
    D.ctx.invol_outer (e * (t * s)) hγH hγ_notin_K hγsq
  obtain ⟨h₂, hh₂, p₂, hp₂, hconj₂⟩ :=
    D.ctx.invol_outer (t * s) htsH hts_notin_K hts_sq
  have hc₁ : h₁ * (e * (t * s)) * h₁⁻¹ * (e * (t * s))⁻¹ ∈ L :=
    fz410_comm_le_L D.ctx D.card_two h₁ hh₁ (e * (t * s)) hγH
  have hc₂ : h₂ * (t * s) * h₂⁻¹ * (t * s)⁻¹ ∈ L :=
    fz410_comm_le_L D.ctx D.card_two h₂ hh₂ (t * s) htsH
  have hp₁L : p₁ * tau * (t * s)⁻¹ ∈ L := by
    have heq : p₁ * tau * (t * s)⁻¹ =
        (h₁ * (e * (t * s)) * h₁⁻¹ * (e * (t * s))⁻¹) * e := by
      rw [← hconj₁]
      group
    rw [heq]
    exact L.mul_mem hc₁ heL
  have hp₂L : p₂ * tau * (t * s)⁻¹ ∈ L := by
    rw [← hconj₂]
    exact hc₂
  have hpp'L : p₁ * p₂⁻¹ ∈ L := by
    have heq : p₁ * p₂⁻¹ =
        (p₁ * tau * (t * s)⁻¹) * (p₂ * tau * (t * s)⁻¹)⁻¹ := by group
    rw [heq]
    exact L.mul_mem hp₁L (L.inv_mem hp₂L)
  have hpp'P : p₁ * p₂⁻¹ ∈ twoCore t :=
    (twoCore t).mul_mem hp₁ ((twoCore t).inv_mem hp₂)
  have hpp'1 : p₁ * p₂⁻¹ = 1 := by
    have hbot : p₁ * p₂⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← D.ctx.hyp.twoCore_inf]
      exact ⟨hpp'P, hpp'L⟩
    exact Subgroup.mem_bot.mp hbot
  have hpp : p₁ = p₂ := by
    calc p₁ = (p₁ * p₂⁻¹) * p₂ := by group
      _ = 1 * p₂ := by rw [hpp'1]
      _ = p₂ := one_mul p₂
  refine ⟨h₁⁻¹ * h₂, (invCent t).mul_mem ((invCent t).inv_mem hh₁) hh₂, ?_⟩
  calc (h₁⁻¹ * h₂) * (t * s) * (h₁⁻¹ * h₂)⁻¹
      = h₁⁻¹ * (h₂ * (t * s) * h₂⁻¹) * h₁ := by group
    _ = h₁⁻¹ * (p₂ * tau) * h₁ := by rw [hconj₂]
    _ = h₁⁻¹ * (p₁ * tau) * h₁ := by rw [hpp]
    _ = h₁⁻¹ * (h₁ * (e * (t * s)) * h₁⁻¹) * h₁ := by rw [← hconj₁]
    _ = e * (t * s) := by group

end Fz410Set

end CFSG.OddStandard.SmallF3.FritzII
