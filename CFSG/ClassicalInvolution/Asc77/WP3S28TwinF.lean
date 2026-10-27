module

public import CFSG.ClassicalInvolution.Asc77.WP3S28TwinD
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofPSp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.S28

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.Assembly.LowTwoRank Matrix Module
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups commutatorElement

section Sp4

variable {F : Type} [Field F]

theorem mul_involutions_scalar_sp (h2 : (2 : F) ≠ 0) {P₀ P₁ : Submodule F (Fin 2 ⊕ Fin 2 → F)}
    (h₀ : IsHyperbolicPlane P₀) (h₁ : IsHyperbolicPlane P₁) {i₀ i₁ : StatedSp 2 F}
    (hi₀ : IsLongRootSp2 (planeGroup P₀) i₀) (hm₀ : minusSpace i₀ = P₀)
    (hi₁ : IsLongRootSp2 (planeGroup P₁) i₁) (hm₁ : minusSpace i₁ = P₁)
    (horth : ∀ u ∈ P₀, ∀ v ∈ P₁, form u v = 0) :
    i₀ * i₁ ∈ Subgroup.center (StatedSp 2 F) := by
  have hd₀ := isHyperbolicPlane_iff.mp h₀
  have hd₁ := isHyperbolicPlane_iff.mp h₁
  have hinf : P₀ ⊓ P₁ = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    exact hd₁.2 v hv.2 fun u hu => horth v hv.1 u hu
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq P₀ P₁
  rw [hinf, finrank_bot, hd₀.1, hd₁.1] at hsum
  have hV : Module.finrank F (Fin 2 ⊕ Fin 2 → F) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have htop : P₀ ⊔ P₁ = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hV]; omega)
  have hfix₀ : ∀ v ∈ P₁, v ∈ fixSpace i₀ := fun v hv =>
    (hi₀.mem_fixSpace_iff h2).2 fun u hu => by
      rw [form_antisymm, horth u (hm₀ ▸ hu) v hv, neg_zero]
  have hfix₁ : ∀ v ∈ P₀, v ∈ fixSpace i₁ := fun v hv =>
    (hi₁.mem_fixSpace_iff h2).2 fun u hu => horth v hv u (hm₁ ▸ hu)
  have hscal : mat 2 F (i₀ * i₁) = -1 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top : v ∈ _)
    have e1a := mem_minusSpace.mp (hm₀ ▸ ha)
    have e2a := mem_fixSpace.mp (hfix₁ a ha)
    have e2b := mem_minusSpace.mp (hm₁ ▸ hb)
    have e1b := mem_fixSpace.mp (hfix₀ b hb)
    simp only [map_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_add, e1a, e2a, e2b, e1b,
      Matrix.mulVec_neg, Matrix.neg_mulVec, Matrix.one_mulVec]
  rw [Subgroup.mem_center_iff]
  intro g
  apply mat_injective (n := 2) (F := F)
  rw [map_mul (mat 2 F) g (i₀ * i₁), map_mul (mat 2 F) (i₀ * i₁) g, hscal, mul_neg_one,
    neg_one_mul]

end Sp4

section Model

variable {p f : ℕ} [Fact p.Prime]


theorem twinProductCentral_psp2 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .PSp 2 p f) : TwinProductCentral p f .PSp 2 := by
  intro R hR R' hR' hne hc _ r hrR hrc hr1 r' hr'R hr'c hr'1
  have e : fundamentalSubgroups .PSp (modelUniv .PSp 2 p f Fact.out).D =
      planeGroupSet (GaloisField p f) 2 := fundamentalSubgroups_psp_eq hadm
  have h2 : (2 : GaloisField p f) ≠ 0 := ModelFacts.two_ne_zero_galoisField f hp2
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  obtain ⟨eR⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSp)
    trivial hadm (by decide) (by decide) hR
  obtain ⟨eR'⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSp)
    trivial hadm (by decide) (by decide) hR'
  obtain ⟨ord, -⟩ := fund_central_involution hodd eR hrR hrc hr1
  obtain ⟨ord', -⟩ := fund_central_involution hodd eR' hr'R hr'c hr'1
  have hRP : R ∈ planeGroupSet (GaloisField p f) 2 := e ▸ hR
  have hR'P : R' ∈ planeGroupSet (GaloisField p f) 2 := e ▸ hR'
  obtain ⟨P₀, hP₀, rfl⟩ := hRP
  obtain ⟨P₁, hP₁, rfl⟩ := hR'P
  obtain ⟨i₀, hi₀, hm₀⟩ := exists_inv_planeGroup h2 hP₀
  obtain ⟨i₁, hi₁, hm₁⟩ := exists_inv_planeGroup h2 hP₁
  have hri : r = i₀ := hi₀.eq_of_orderOf_eq_two h2 hrR ord
  have hr'i' : r' = i₁ := hi₁.eq_of_orderOf_eq_two h2 hr'R ord'
  have hne' : P₀ ≠ P₁ := fun h => hne (by rw [h])
  have horth := (commutes_planeGroup_iff h2 hP₀ hP₁ hne').mp hc
  rw [hri, hr'i']
  exact mul_involutions_scalar_sp h2 hP₀ hP₁ hi₀ hm₀ hi₁ hm₁ horth

end Model

end CFSG.ClassicalInvolution.Asc77.S28
