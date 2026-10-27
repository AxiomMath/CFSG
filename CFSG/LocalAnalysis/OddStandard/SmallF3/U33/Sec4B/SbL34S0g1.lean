module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutAmbient
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutHS29

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open scoped Pointwise
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


section Aux

variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau)
include hc

theorem x₂_mem_L : x₂ ∈ L := by
  have h : x₂ ∈ S ⊓ L := by rw [hc.inf_eq]; exact subset_closure (by simp)
  exact h.2

theorem t_comm_x₂ : t * x₂ = x₂ * t :=
  (mem_centralizer_iff.mp hc.hyp.mem_centralizer x₂ (x₂_mem_L hc)).symm

theorem x₁_ne_one : x₁ ≠ 1 := by
  intro h1
  have h4 := hc.wreath.ord_x₁
  rw [h1, orderOf_one] at h4
  exact absurd h4 (by norm_num)

theorem x₁_ne_x₂ : x₁ ≠ x₂ := by
  intro hEq
  have hmem : x₁ ∈ (⊥ : Subgroup G) := by
    rw [← hc.wreath.inf_eq_bot]
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_zpowers x₁, by rw [hEq]; exact Subgroup.mem_zpowers x₂⟩
  exact x₁_ne_one hc (by simpa using hmem)

theorem tlam_conj_x₁ : (t * lam) * x₁ * (t * lam)⁻¹ = x₂ := by
  calc (t * lam) * x₁ * (t * lam)⁻¹ = t * (lam * x₁ * lam⁻¹) * t⁻¹ := by group
    _ = t * x₂ * t⁻¹ := by rw [hc.wreath.conj_x₁]
    _ = x₂ := by rw [t_comm_x₂ hc, mul_assoc, mul_inv_cancel, mul_one]

theorem tlam_conj_rho : (t * lam) * rho * (t * lam)⁻¹ = rho⁻¹ := by
  have htr : t * rho⁻¹ = rho⁻¹ * t := by
    have h : rho * t = t * rho := hc.rho_comm_t
    calc t * rho⁻¹ = rho⁻¹ * (rho * t) * rho⁻¹ := by group
      _ = rho⁻¹ * (t * rho) * rho⁻¹ := by rw [h]
      _ = rho⁻¹ * t := by group
  calc (t * lam) * rho * (t * lam)⁻¹ = t * (lam * rho * lam⁻¹) * t⁻¹ := by group
    _ = t * rho⁻¹ * t⁻¹ := by rw [hc.lam_rho]
    _ = rho⁻¹ := by rw [htr, mul_assoc, mul_inv_cancel, mul_one]

theorem orderOf_tlam : orderOf (t * lam) = 2 := by
  apply orderOf_eq_prime (by simpa [pow_two] using q_mul_self hc)
  intro h1
  have h3 := tlam_conj_x₁ hc
  rw [h1, one_mul, inv_one, mul_one] at h3
  exact x₁_ne_x₂ hc h3

theorem card_CQ_tl_of (hnab : ∃ a ∈ ctxQ t tau x₁ x₂ rho, ∃ b ∈ ctxQ t tau x₁ x₂ rho,
      a * b ≠ b * a) :
    Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * lam} : Set G)) = 8 := by
  set Q : Subgroup G := ctxQ t tau x₁ x₂ rho with hQ
  have hρ : rho ∈ normalizer (Q : Set G) :=
    Subgroup.mem_normalizer_fintype (fun a ha => hc.normal_Q.2 rho hc.rho_mem_M a ha)
  have htM : t ∈ ctxM t tau x₁ x₂ := hc.O_le_M hc.t_mem_O
  have hlamM : lam ∈ ctxM t tau x₁ x₂ := hc.lam_mem_M
  have hx : t * lam ∈ normalizer (Q : Set G) :=
    Subgroup.mem_normalizer_fintype
      (fun a ha => hc.normal_Q.2 (t * lam) (mul_mem htM hlamM) a ha)
  have hx₁Q : x₁ ∈ Q := hc.base_le_Q (Subgroup.subset_closure (by simp))
  have hfρ : ∃ h ∈ Q, rho * h ≠ h * rho := by
    refine ⟨x₁, hx₁Q, fun hconj => x₁_ne_one hc ?_⟩
    have hmem : x₁ ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) :=
      ⟨hx₁Q, Subgroup.mem_centralizer_singleton_iff.mpr hconj.symm⟩
    rw [hc.CQ_rho] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hfx : ∃ h ∈ Q, (t * lam) * h ≠ h * (t * lam) := by
    refine ⟨x₁, hx₁Q, fun hconj => ?_⟩
    have h1 : (t * lam) * x₁ * (t * lam)⁻¹ = x₁ := by
      rw [hconj, mul_assoc, mul_inv_cancel, mul_one]
    exact x₁_ne_x₂ hc (h1.symm.trans (tlam_conj_x₁ hc))
  have hs : Outside.Sigma3Rel (Outside.conjAut Q rho hρ) (Outside.conjAut Q (t * lam) hx) :=
    Outside.sigma3Rel_conjAut Q hρ hx hc.ord_rho (orderOf_tlam hc) (tlam_conj_rho hc) hfρ hfx
  have hfpf : ∀ g : ↥Q, Outside.conjAut Q rho hρ g = g → g = 1 := by
    intro g hg
    have h1 : rho * (g : G) * rho⁻¹ = (g : G) := by
      have := congrArg (fun x : ↥Q => (x : G)) hg
      simpa [Outside.conjAut_coe] using this
    have h2' : rho * (g : G) = (g : G) * rho := (mul_inv_eq_iff_eq_mul).mp h1
    have hmem : (g : G) ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) :=
      ⟨g.2, Subgroup.mem_centralizer_singleton_iff.mpr h2'.symm⟩
    rw [hc.CQ_rho] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  have hnab' : ∃ a b : ↥Q, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun hc' => hab (congrArg Subtype.val hc')⟩
  have hcard : Nat.card ↥Q = 64 := by rw [hQ, hc.card_Q]; norm_num
  obtain ⟨-, hfix⟩ := Outside.HS29 hcard hnab' hs hfpf
  have hcard_fix : Nat.card ↥(Outside.fixSub (Outside.conjAut Q (t * lam) hx)) = 8 := by
    rcases hfix with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · calc Nat.card ↥(Outside.fixSub (Outside.conjAut Q (t * lam) hx))
          = Nat.card (DihedralGroup 4) := Nat.card_congr e.toEquiv
        _ = 8 := by rw [DihedralGroup.nat_card]
    · calc Nat.card ↥(Outside.fixSub (Outside.conjAut Q (t * lam) hx))
          = Nat.card (QuaternionGroup 2) := Nat.card_congr e.toEquiv
        _ = 8 := by rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hgoal : Nat.card ↥((Outside.fixSub (Outside.conjAut Q (t * lam) hx)).map Q.subtype) = 8 := by
    rw [Subgroup.card_map_of_injective Q.subtype_injective, hcard_fix]
  rw [Outside.map_fixSub_conjAut Q hx] at hgoal
  exact hgoal

end Aux

section Main

variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau) (hs : IsSylSL34 (ctxQ t tau x₁ x₂ rho))
include hc hs

theorem card_CQ_tl :
    Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * lam} : Set G)) = 8 :=
  card_CQ_tl_of hc (Q_nonab hc hs)

end Main

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
