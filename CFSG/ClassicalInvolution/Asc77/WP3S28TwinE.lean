module

public import CFSG.ClassicalInvolution.Asc77.WP3S28TwinD
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofPSU

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.S28

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank Matrix Module
open scoped MatrixGroups commutatorElement

section SU4

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem mul_involutions_scalar_su (hp : p ≠ 2) {hn : 2 ≤ 4} {L₁ L₂ : Subgroup (Su K p f 4)}
    {i₁ i₂ : Su K p f 4} (hK : Nat.card K = (p ^ f) ^ 2)
    (h₁ : IsLongRootSU2 K p f hn L₁ i₁) (h₂ : IsLongRootSU2 K p f hn L₂ i₂)
    (hne : L₁ ≠ L₂) (hc : Commutes L₁ L₂) :
    i₁ * i₂ ∈ Subgroup.center (Su K p f 4) := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) (p := p) hp
  obtain ⟨le12, le21, hbot⟩ := le_of_commutes_su hK hp (by omega) h₁ h₂ hne hc
  have hdim : finrank K ↥(minusSpaceSU i₁ ⊔ minusSpaceSU i₂) = 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (minusSpaceSU i₁) (minusSpaceSU i₂)
    rw [hbot, finrank_bot, h₁.finrank_minusSpaceSU h2, h₂.finrank_minusSpaceSU h2] at h
    omega
  have htop : minusSpaceSU i₁ ⊔ minusSpaceSU i₂ = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hdim, Module.finrank_fin_fun])
  have hscal : suMat (i₁ * i₂) = -1 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top : v ∈ _)
    have e1a := mem_minusSpaceSU.mp ha
    have e2a := mem_fixSpaceSU.mp (le12 ha)
    have e2b := mem_minusSpaceSU.mp hb
    have e1b := mem_fixSpaceSU.mp (le21 hb)
    simp only [suMat_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_add, e1a, e2a, e2b, e1b,
      Matrix.mulVec_neg, Matrix.neg_mulVec, Matrix.one_mulVec]
  rw [Subgroup.mem_center_iff]
  intro g
  apply suMat_injective (σ := unitaryInvolution K p f)
  rw [suMat_mul g (i₁ * i₂), suMat_mul (i₁ * i₂) g, hscal, mul_neg_one, neg_one_mul]

end SU4

section Model

variable {p f : ℕ} [Fact p.Prime]


theorem twinProductCentral_psu4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .PSU 4 p f) : TwinProductCentral p f .PSU 4 := by
  intro R hR R' hR' hne hc _ r hrR hrc hr1 r' hr'R hr'c hr'1
  have hf : 1 ≤ f := hadm.2.1
  have : NeZero (2 * f) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p f hf
  obtain ⟨e, he⟩ := psu_model_equiv hp2 hadm
  obtain ⟨i, hi⟩ := (he R).mp hR
  obtain ⟨i', hi'⟩ := (he R').mp hR'
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  obtain ⟨eR⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSU)
    trivial hadm (by decide) (by decide) hR
  obtain ⟨eR'⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSU)
    trivial hadm (by decide) (by decide) hR'
  obtain ⟨ord, -⟩ := fund_central_involution hodd eR hrR hrc hr1
  obtain ⟨ord', -⟩ := fund_central_involution hodd eR' hr'R hr'c hr'1
  have hri : e r = i :=
    hi.eq_of_orderOf_eq_two hK hp2 (Subgroup.mem_map_of_mem _ hrR)
      (by rw [MulEquiv.orderOf_eq]; exact ord)
  have hr'i' : e r' = i' :=
    hi'.eq_of_orderOf_eq_two hK hp2 (Subgroup.mem_map_of_mem _ hr'R)
      (by rw [MulEquiv.orderOf_eq]; exact ord')
  have hcen := mul_involutions_scalar_su hp2 hK hi hi'
    (fun h => hne (Subgroup.map_injective e.injective h)) ((commutes_map_equiv e).mpr hc)
  refine mem_center_of_equiv e ?_
  rw [map_mul, hri, hr'i']
  exact hcen

end Model

end CFSG.ClassicalInvolution.Asc77.S28
