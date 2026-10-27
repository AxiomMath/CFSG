module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AQ14A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AQ14F

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

section Q14G

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem q14_cent_Q_rho (h : L41GPh10 t L S x₁ x₂ lam rho) :
    l41Q t x₁ x₂ rho ⊓ centralizer ({rho} : Set G) = zpowers t := by
  have hρt : rho * t * rho⁻¹ = t :=
    n4_K_fix_t h.toCtx0 (Subgroup.subset_closure (by simp))
  refine q14_eq_zpowers_of_cent (P := l41Q t x₁ x₂ rho ⊓ centralizer ({rho} : Set G))
    ((q14_Q_isPGroup t x₁ x₂ rho).to_le inf_le_left)
    (Subgroup.mem_inf.mpr ⟨q14_t_mem_Q h.toL41GPh8, ?_⟩)
    (t_ne_one h.hyp) (t_mul_self h.hyp) ?_
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hrt : rho * t = t * rho := by
      calc rho * t = rho * t * rho⁻¹ * rho := by group
        _ = t * rho := by rw [hρt]
    exact hrt.symm
  · intro x hxP hxt
    obtain ⟨hxQ, hxcent⟩ := Subgroup.mem_inf.mp hxP
    have hxt' : x ∈ invCent t := by
      show x ∈ centralizer ({t} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hxt
    have hxW : x ∈ ctxW t x₁ x₂ := by
      rw [← q14_cent_Q_t h]
      exact Subgroup.mem_inf.mpr ⟨hxQ, hxt'⟩
    have hxWcent : x ∈ ctxW t x₁ x₂ ⊓ centralizer ({rho} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hxW, hxcent⟩
    rw [h.toCtx0.cent_rho, h.p2] at hxWcent
    exact hxWcent

theorem q14_cent_Qbar_rho (h : L41GPh10 t L S x₁ x₂ lam rho) :
    {q | q ∈ l41Q t x₁ x₂ rho ∧ ⁅q, rho⁆ ∈ l41Y t x₁ x₂ rho} =
      ((zpowers t ⊔ l41Y t x₁ x₂ rho : Subgroup G) : Set G) := by
  have hρ3 : rho ^ 3 = 1 := by
    rw [← h.ord_rho]
    exact pow_orderOf_eq_one rho
  have hρM : rho ∈ l41M t x₁ x₂ rho := q14_rho_mem_M h.toL41GPh8
  have hN : ∀ n ∈ l41Y t x₁ x₂ rho, rho * n * rho⁻¹ ∈ l41Y t x₁ x₂ rho :=
    fun n hn => (m13_normal_Y h).2 rho hρM n hn
  have hcardY : ¬ 3 ∣ Nat.card (l41Y t x₁ x₂ rho) := by
    rw [m11_card_Y h]
    norm_num
  ext q
  rw [Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨hqQ, hqcomm⟩
    have hw : rho * q * rho⁻¹ * q⁻¹ ∈ l41Y t x₁ x₂ rho := by
      have h1 : (q * rho * q⁻¹ * rho⁻¹)⁻¹ ∈ l41Y t x₁ x₂ rho :=
        Subgroup.inv_mem _ hqcomm
      have h2 : (q * rho * q⁻¹ * rho⁻¹)⁻¹ = rho * q * rho⁻¹ * q⁻¹ := by group
      rwa [h2] at h1
    obtain ⟨x, hxq, hxfix⟩ :=
      q14_exists_fixed_coset (w := q) (N := l41Y t x₁ x₂ rho) hρ3 hN hcardY hw
    have hxQ : x ∈ l41Q t x₁ x₂ rho := by
      have hxeq : x = (x * q⁻¹) * q := by group
      rw [hxeq]
      exact Subgroup.mul_mem _ (q14_Y_le_Q h hxq) hqQ
    have hxcent : x ∈ centralizer ({rho} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * rho = (rho * x * rho⁻¹) * rho := by rw [hxfix]
        _ = rho * x := by group
    have hxzp : x ∈ zpowers t := by
      have hxP : x ∈ l41Q t x₁ x₂ rho ⊓ centralizer ({rho} : Set G) :=
        Subgroup.mem_inf.mpr ⟨hxQ, hxcent⟩
      rwa [q14_cent_Q_rho h] at hxP
    have hqmem : q ∈ l41Y t x₁ x₂ rho ⊔ zpowers t := by
      have hqeq : q = (x * q⁻¹)⁻¹ * x := by group
      rw [hqeq]
      exact Subgroup.mul_mem_sup (Subgroup.inv_mem _ hxq) hxzp
    rw [sup_comm]
    exact hqmem
  · intro hq
    let S : Subgroup G :=
      { carrier := {q | q ∈ l41Q t x₁ x₂ rho ∧ ⁅q, rho⁆ ∈ l41Y t x₁ x₂ rho}
        mul_mem' := by
          rintro a b ⟨haQ, ha⟩ ⟨hbQ, hb⟩
          refine ⟨Subgroup.mul_mem _ haQ hbQ, ?_⟩
          have haM : a ∈ l41M t x₁ x₂ rho := q14_Q_le_M t x₁ x₂ rho haQ
          rw [commutatorElement_mul_left_eq_conj_mul]
          exact Subgroup.mul_mem _ ((m13_normal_Y h).2 a haM ⁅b, rho⁆ hb) ha
        one_mem' := ⟨(l41Q t x₁ x₂ rho).one_mem, by simp⟩
        inv_mem' := by
          rintro a ⟨haQ, ha⟩
          refine ⟨Subgroup.inv_mem _ haQ, ?_⟩
          have haM : a ∈ l41M t x₁ x₂ rho := q14_Q_le_M t x₁ x₂ rho haQ
          have hra : ⁅rho, a⁆ ∈ l41Y t x₁ x₂ rho := by
            have hinv : ⁅a, rho⁆⁻¹ ∈ l41Y t x₁ x₂ rho := Subgroup.inv_mem _ ha
            rwa [commutatorElement_inv] at hinv
          rw [commutatorElement_inv_left]
          simpa [mul_assoc] using
            (m13_normal_Y h).2 a⁻¹ (Subgroup.inv_mem _ haM) ⁅rho, a⁆ hra }
    have hSsup : zpowers t ⊔ l41Y t x₁ x₂ rho ≤ S := by
      refine sup_le ?_ ?_
      · intro a ha
        refine ⟨Subgroup.zpowers_le.mpr (q14_t_mem_Q h.toL41GPh8) ha, ?_⟩
        have ha_cent : a ∈ centralizer ({rho} : Set G) := by
          have haP : a ∈ l41Q t x₁ x₂ rho ⊓ centralizer ({rho} : Set G) := by
            rw [q14_cent_Q_rho h]
            exact ha
          exact (Subgroup.mem_inf.mp haP).2
        rw [Commute.commutator_eq (Subgroup.mem_centralizer_singleton_iff.mp ha_cent)]
        exact (l41Y t x₁ x₂ rho).one_mem
      · intro y hy
        refine ⟨q14_Y_le_Q h hy, ?_⟩
        have h2 : rho * y⁻¹ * rho⁻¹ ∈ l41Y t x₁ x₂ rho := by
          have hconj : rho * y * rho⁻¹ ∈ l41Y t x₁ x₂ rho :=
            (m13_normal_Y h).2 rho hρM y hy
          have h3 : (rho * y * rho⁻¹)⁻¹ ∈ l41Y t x₁ x₂ rho := Subgroup.inv_mem _ hconj
          have h4 : (rho * y * rho⁻¹)⁻¹ = rho * y⁻¹ * rho⁻¹ := by group
          rwa [h4] at h3
        rw [commutatorElement_def]
        simpa [mul_assoc] using Subgroup.mul_mem _ hy h2
    exact hSsup hq

theorem q14_quot_Q (h : L41GPh10 t L S x₁ x₂ lam rho) :
    Sec4SectionIso (l41Q t x₁ x₂ rho) (l41F t x₁ x₂ rho)
      (CFSG.GH74.GLS.Bg.TwoGroups.E2 2) := by
  haveI : ((l41F t x₁ x₂ rho).subgroupOf (l41Q t x₁ x₂ rho)).Normal :=
    q14_normal_FQ t x₁ x₂ rho
  let X := ↥(l41Q t x₁ x₂ rho) ⧸ (l41F t x₁ x₂ rho).subgroupOf (l41Q t x₁ x₂ rho)
  have hcardX : Nat.card X = 4 := by
    change Nat.card (↥(l41Q t x₁ x₂ rho) ⧸
      (l41F t x₁ x₂ rho).subgroupOf (l41Q t x₁ x₂ rho)) = 4
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((l41F t x₁ x₂ rho).subgroupOf (l41Q t x₁ x₂ rho))
    have hF : Nat.card ((l41F t x₁ x₂ rho).subgroupOf (l41Q t x₁ x₂ rho)) = 128 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (q14_F_le_Q h.toL41GPh8)).toEquiv,
        m13_card_F h.toL41GPh8]
      norm_num
    rw [q14_card_Q h, hF] at hcard
    omega
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hcardX]; norm_num)
  have hρQ : rho ∈ normalizer ((l41Q t x₁ x₂ rho : Subgroup G) : Set G) :=
    q14_mem_normalizer_Q (q14_rho_mem_M h.toL41GPh8)
  have hρF : rho ∈ normalizer ((l41F t x₁ x₂ rho : Subgroup G) : Set G) :=
    q14_mem_normalizer_F (q14_rho_mem_M h.toL41GPh8)
  have hρ3 : rho ^ 3 = 1 := by
    rw [← h.ord_rho]
    exact pow_orderOf_eq_one rho
  let α : MulAut X := quotConj (l41Q t x₁ x₂ rho) (l41F t x₁ x₂ rho) rho hρQ hρF
  have hα : α ^ 3 = 1 := quotConj_pow_three hρQ hρF hρ3
  have hfix : ∀ x : X, α x = x → x = 1 := by
    intro x hx
    obtain ⟨q, hxq⟩ := QuotientGroup.mk_surjective x
    have hαx : α (QuotientGroup.mk q) = QuotientGroup.mk q := by
      rw [hxq]
      exact hx
    have hqF : rho * (q : G) * rho⁻¹ * (q : G)⁻¹ ∈ l41F t x₁ x₂ rho :=
      (quotConj_fix_iff hρQ hρF q).mp hαx
    have hNF : ∀ n ∈ l41F t x₁ x₂ rho, rho * n * rho⁻¹ ∈ l41F t x₁ x₂ rho :=
      fun n hn => q14_conj_F (q14_rho_mem_M h.toL41GPh8) hn
    have hcardF : ¬ 3 ∣ Nat.card (l41F t x₁ x₂ rho) := by
      rw [m13_card_F h.toL41GPh8]
      norm_num
    obtain ⟨x₀, hx₀qF, hx₀fix⟩ := q14_exists_fixed_coset (w := (q : G))
      (N := l41F t x₁ x₂ rho) hρ3 hNF hcardF hqF
    have hx₀Q : x₀ ∈ l41Q t x₁ x₂ rho := by
      have hx0eq : x₀ = (x₀ * (q : G)⁻¹) * q := by group
      rw [hx0eq]
      exact Subgroup.mul_mem _ (q14_F_le_Q h.toL41GPh8 hx₀qF) q.2
    have hx₀cent : x₀ ∈ centralizer ({rho} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x₀ * rho = (rho * x₀ * rho⁻¹) * rho := by rw [hx₀fix]
        _ = rho * x₀ := by group
    have hx₀zp : x₀ ∈ zpowers t := by
      have hxP : x₀ ∈ l41Q t x₁ x₂ rho ⊓ centralizer ({rho} : Set G) :=
        Subgroup.mem_inf.mpr ⟨hx₀Q, hx₀cent⟩
      rwa [q14_cent_Q_rho h] at hxP
    have hx₀F : x₀ ∈ l41F t x₁ x₂ rho := by
      show x₀ ∈ l41R t x₁ x₂ rho ⊔ zpowers t
      exact Subgroup.mem_sup_right hx₀zp
    have hqF' : (q : G) ∈ l41F t x₁ x₂ rho := by
      have hqeq : (q : G) = (x₀ * (q : G)⁻¹)⁻¹ * x₀ := by group
      rw [hqeq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hx₀qF) hx₀F
    have hqsub : q ∈ (l41F t x₁ x₂ rho).subgroupOf (l41Q t x₁ x₂ rho) := by
      rw [Subgroup.mem_subgroupOf]
      exact hqF'
    have hone : (QuotientGroup.mk q : X) = 1 := (QuotientGroup.eq_one_iff q).mpr hqsub
    rw [← hxq, hone]
  obtain ⟨e⟩ := q14_quot_E4 hcardX α hα hfix
  exact q14_sectionIso_of_equiv e

theorem l41_q_of (h : L41GPh13 t L S x₁ x₂ lam rho) : L41QFacts t x₁ x₂ lam rho where
  F_lt_Q := q14_F_lt_Q h.toL41GPh10
  quot_Q := q14_quot_Q h.toL41GPh10
  M_eq := q14_M_eq h.toL41GPh10
  cent_Q_rho := q14_cent_Q_rho h.toL41GPh10
  cent_Qbar_t := q14_cent_Qbar_t h.toL41GPh10
  cent_Qbar_rho := q14_cent_Qbar_rho h.toL41GPh10
  orbit_t := q14_orbit_t h.toL41GPh10

end Q14G

end CFSG.OddStandard.SmallF3.HarrisU33.S4A

namespace CFSG.OddStandard.SmallF3.HarrisU33

theorem l41_q_holds : L41QStmt :=
  fun h => S4A.l41_q_of h.toG

end CFSG.OddStandard.SmallF3.HarrisU33
