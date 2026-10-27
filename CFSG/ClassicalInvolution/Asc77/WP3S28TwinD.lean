module

public import CFSG.ClassicalInvolution.Asc77.WP3S28TwinB
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofPSL
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpin
public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.S28

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank
  Matrix Module
open scoped MatrixGroups commutatorElement

section Generic

theorem mem_center_of_map_commutes {X Y : Type*} [Group X] [Group Y] (π : X →* Y)
    (hker : π.ker ≤ Subgroup.center X) (hperf : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤)
    {u : X} (hu : ∀ g : X, π u * π g = π g * π u) : u ∈ Subgroup.center X := by
  have h : ∀ ℓ ∈ (⊤ : Subgroup X), ⁅u, ℓ⁆ ∈ Subgroup.center X := by
    intro ℓ _
    apply hker
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hu ℓ)
  have key := commutes_of_commutators_mem_center hperf h
  rw [Subgroup.mem_center_iff]
  intro g
  exact (key g trivial).symm

theorem fund_central_involution {X : Type*} [Group X] {F : Type*} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) {R : Subgroup X} (e : R ≃* SL(2, F)) {r : X} (hrR : r ∈ R)
    (hrc : ∀ s ∈ R, r * s = s * r) (hr1 : r ≠ 1) :
    orderOf r = 2 ∧ ∀ t ∈ R, orderOf t = 2 → t = r := by
  have hcen : e ⟨r, hrR⟩ ∈ Subgroup.center SL(2, F) := by
    refine (mem_center_iff_of_equiv_sl2 e ⟨r, hrR⟩).mp (Subgroup.mem_center_iff.mpr fun g => ?_)
    exact Subtype.ext (hrc g g.2).symm
  have hne : e ⟨r, hrR⟩ ≠ 1 := by
    intro h
    apply hr1
    have := e.injective (h.trans (map_one e).symm)
    exact congrArg Subtype.val this
  have hneg : e ⟨r, hrR⟩ = -1 := ((mem_center_sl2_iff _).mp hcen).resolve_left hne
  have hsymm : (⟨r, hrR⟩ : R) = e.symm (-1) := by rw [← hneg]; simp
  refine ⟨?_, fun t ht hord => ?_⟩
  · have h1 : orderOf (⟨r, hrR⟩ : R) = 2 := by
      rw [hsymm, MulEquiv.orderOf_eq]
      exact sl2_orderOf_neg_one hodd
    rwa [Subgroup.orderOf_mk] at h1
  · have h1 : (⟨t, ht⟩ : R) = e.symm (-1) :=
      (orderOf_eq_two_iff_of_equiv_sl2 hodd e _).mp (by rwa [Subgroup.orderOf_mk])
    exact congrArg Subtype.val (h1.trans hsymm.symm)

theorem mem_center_of_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {x : X}
    (h : e x ∈ Subgroup.center Y) : x ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff] at h ⊢
  intro g
  apply e.injective
  rw [map_mul, map_mul]
  exact h (e g)

end Generic

section SL4

variable {F : Type} [Field F]

theorem mul_involutions_scalar (h2 : (2 : F) ≠ 0) {hn : 2 ≤ 4} {L₁ L₂ : Subgroup SL(4, F)}
    {i₁ i₂ : SL(4, F)} (h₁ : IsLongRootSL2 hn L₁ i₁) (h₂ : IsLongRootSL2 hn L₂ i₂)
    (hne : L₁ ≠ L₂) (hc : Commutes L₁ L₂) :
    i₁ * i₂ ∈ Subgroup.center SL(4, F) := by
  obtain ⟨le12, le21, hbot⟩ := le_of_commutes h2 (by omega) h₁ h₂ hne hc
  have hdim : finrank F ↥(minusSpace i₁ ⊔ minusSpace i₂) = 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (minusSpace i₁) (minusSpace i₂)
    rw [hbot, finrank_bot, h₁.finrank_minusSpace h2, h₂.finrank_minusSpace h2] at h
    omega
  have htop : minusSpace i₁ ⊔ minusSpace i₂ = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hdim, Module.finrank_fin_fun])
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by norm_num, ?_⟩
  rw [Matrix.ext_iff_mulVec]
  intro v
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top : v ∈ _)
  have e1a := mem_minusSpace.mp ha
  have e2a := mem_fixSpace.mp (le12 ha)
  have e2b := mem_minusSpace.mp hb
  have e1b := mem_fixSpace.mp (le21 hb)
  simp only [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_add,
    e1a, e2a, e2b, e1b, Matrix.mulVec_neg]
  simp [Matrix.scalar_apply]

end SL4

section Model

variable {p f : ℕ} [Fact p.Prime]


theorem twinProductCentral_psl4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .PSL 4 p f) : TwinProductCentral p f .PSL 4 := by
  intro R hR R' hR' hne hc _ r hrR hrc hr1 r' hr'R hr'c hr'1
  have e : fundamentalSubgroups .PSL (modelUniv .PSL 4 p f Fact.out).D =
      longRootSet (K := GaloisField p f) (by omega : 2 ≤ 4) :=
    fundamentalSubgroups_psl_eq (p := p) (f := f) (m := 3) (by omega)
  have hRL : R ∈ longRootSet (K := GaloisField p f) (by omega : 2 ≤ 4) := e ▸ hR
  have hR'L : R' ∈ longRootSet (K := GaloisField p f) (by omega : 2 ≤ 4) := e ▸ hR'
  obtain ⟨i, hi⟩ := hRL
  obtain ⟨i', hi'⟩ := hR'L
  have h2 : (2 : GaloisField p f) ≠ 0 := ModelFacts.two_ne_zero_galoisField f hp2
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  obtain ⟨eR⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSL)
    trivial hadm (by decide) (by decide) hR
  obtain ⟨eR'⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSL)
    trivial hadm (by decide) (by decide) hR'
  have hci := hi.isClassicalSL2 h2
  have hci' := hi'.isClassicalSL2 h2
  have hri : r = i :=
    ((fund_central_involution hodd eR hrR hrc hr1).2 i hci.mem hci.orderOf_eq_two).symm
  have hr'i' : r' = i' :=
    ((fund_central_involution hodd eR' hr'R hr'c hr'1).2 i' hci'.mem hci'.orderOf_eq_two).symm
  rw [hri, hr'i']
  exact mul_involutions_scalar h2 hi hi' hne hc

end Model

end CFSG.ClassicalInvolution.Asc77.S28
