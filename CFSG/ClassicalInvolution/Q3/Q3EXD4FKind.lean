module

public import CFSG.ClassicalInvolution.Q3.Q3EXD4FPair

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.Assembly.LowTwoRank

local notation "𝔽₃" => GaloisField 3 1


theorem transport_plus_four (Pr : ∀ (X : Type) [Group X], Set (Subgroup X) → Prop)
    (h : Pr (spinGroup (quadPlus 4 𝔽₃)) (fundD4 𝔽₃)) {c : CompData}
    (hk : c = CompData.model .POmegaPlus 4) : Pr c.G c.fund := by
  subst hk
  have hn3 : 3 ≤ 4 := by norm_num
  have hM : modelUniv .POmegaPlus 4 3 1 Fact.out =
      ⟨spinGroup (quadPlus 4 (GaloisField 3 1)), plusDatum 4 (GaloisField 3 1) hn3⟩ :=
    (rfl : modelUniv .POmegaPlus 4 3 1 Fact.out =
      ModelFacts.modelUniv .POmegaPlus 4 3 1 Fact.out).trans (ModelFacts.modelUniv_POmegaPlus hn3)
  have key : ∀ M : LieUniversal, M =
      ⟨spinGroup (quadPlus 4 (GaloisField 3 1)), plusDatum 4 (GaloisField 3 1) hn3⟩ →
      Pr M.K (fundamentalSubgroups .POmegaPlus M.D) := by
    intro M hM
    subst hM
    exact h
  exact key _ hM

theorem fund_pair_mul_central_of_kind {c : CompData} (hk : c = CompData.model .POmegaPlus 4)
    {R₁ R₂ : Subgroup c.G} (hR₁ : R₁ ∈ c.fund) (hR₂ : R₂ ∈ c.fund)
    (hc : ∀ a ∈ R₁, ∀ b ∈ R₂, a * b = b * a) {c₁ c₂ : c.G} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂)
    (hz₁ : ∀ r ∈ R₁, c₁ * r = r * c₁) (hz₂ : ∀ r ∈ R₂, c₂ * r = r * c₂) (h₁ : c₁ ≠ 1)
    (h₂ : c₂ ≠ 1) : c₁ * c₂ ∈ Subgroup.center c.G :=
  transport_plus_four (fun X _ S => ∀ R₁ R₂ : Subgroup X, R₁ ∈ S → R₂ ∈ S →
    (∀ a ∈ R₁, ∀ b ∈ R₂, a * b = b * a) → ∀ c₁ c₂ : X, c₁ ∈ R₁ → c₂ ∈ R₂ →
    (∀ r ∈ R₁, c₁ * r = r * c₁) → (∀ r ∈ R₂, c₂ * r = r * c₂) → c₁ ≠ 1 → c₂ ≠ 1 →
    c₁ * c₂ ∈ Subgroup.center X)
    (fun _ _ h1 h2 hc _ _ hc₁ hc₂ hz₁ hz₂ h₁ h₂ =>
      D4Facts3.of_gf3.fund_pair_mul_central h1 h2 hc hc₁ hc₂ hz₁ hz₂ h₁ h₂) hk R₁ R₂ hR₁ hR₂ hc
    c₁ c₂ hc₁ hc₂ hz₁ hz₂ h₁ h₂

@[expose] def CliquePartnerS {X : Type} [Group X] (S : Set (Subgroup X))
    (R₂ R₃ R₄ : Subgroup X) (c : X) : Prop :=
  ∃ Ra Rb : Subgroup X, (Ra = R₂ ∨ Ra = R₃ ∨ Ra = R₄) ∧ (Rb = R₂ ∨ Rb = R₃ ∨ Rb = R₄) ∧
    Ra ≠ Rb ∧ ∃ ua ∈ Ra, ∃ ub ∈ Rb, ∃ P ∈ S, ∃ x ∈ P,
      (∀ r ∈ P, r * (ua * ub) = (ua * ub) * r) ∧
      (∀ ca ∈ Ra, (∀ r ∈ Ra, ca * r = r * ca) → ca ≠ 1 → ua * ua = ca) ∧
      (∀ cb ∈ Rb, (∀ r ∈ Rb, cb * r = r * cb) → cb ≠ 1 → ub * ub = cb) ∧
      (¬ ∀ r ∈ Ra, ua * r = r * ua) ∧ (¬ ∀ r ∈ Rb, ub * r = r * ub) ∧
      ua * ub ∉ Subgroup.center X ∧
      (x * c * x⁻¹ * c⁻¹) ^ 4 = 1 ∧ x * c * x⁻¹ * c⁻¹ ∉ Subgroup.center X

theorem exists_clique_partner_of_kind {c : CompData} (hk : c = CompData.model .POmegaPlus 4)
    {R₁ R₂ R₃ R₄ : Subgroup c.G} (h₁ : R₁ ∈ c.fund) (h₂ : R₂ ∈ c.fund) (h₃ : R₃ ∈ c.fund)
    (h₄ : R₄ ∈ c.fund) (h12 : R₁ ≠ R₂) (h13 : R₁ ≠ R₃) (h14 : R₁ ≠ R₄) (h23 : R₂ ≠ R₃)
    (h24 : R₂ ≠ R₄) (h34 : R₃ ≠ R₄) (c12 : Commutes R₁ R₂) (c13 : Commutes R₁ R₃)
    (c14 : Commutes R₁ R₄) {z : c.G} (hz : z ∈ R₁) (hzc : ∀ r ∈ R₁, z * r = r * z) (hz1 : z ≠ 1) :
    CliquePartnerS c.fund R₂ R₃ R₄ z :=
  transport_plus_four (fun X _ S => ∀ R₁ R₂ R₃ R₄ : Subgroup X, R₁ ∈ S → R₂ ∈ S → R₃ ∈ S →
    R₄ ∈ S → R₁ ≠ R₂ → R₁ ≠ R₃ → R₁ ≠ R₄ → R₂ ≠ R₃ → R₂ ≠ R₄ → R₃ ≠ R₄ → Commutes R₁ R₂ →
    Commutes R₁ R₃ → Commutes R₁ R₄ → ∀ z : X, z ∈ R₁ → (∀ r ∈ R₁, z * r = r * z) → z ≠ 1 →
    CliquePartnerS S R₂ R₃ R₄ z)
    (fun _ _ _ _ h₁ h₂ h₃ h₄ h12 h13 h14 h23 h24 h34 c12 c13 c14 _ hz hzc hz1 =>
      exists_clique_partner3 D4Facts3.of_gf3 h₁ h₂ h₃ h₄ h12 h13 h14 h23 h24 h34 c12 c13 c14 hz
        hzc hz1) hk R₁ R₂ R₃ R₄ h₁ h₂ h₃ h₄ h12 h13 h14 h23 h24 h34 c12 c13 c14 z hz hzc hz1

theorem exists_nodes_of_kind {c : CompData} (hk : c = CompData.model .POmegaPlus 4) :
    ∃ (R : Fin 4 → Subgroup c.G) (z : Fin 4 → c.G),
      (∀ k, R k ∈ c.fund) ∧ (∀ k, z k ∈ R k) ∧ (∀ k, ∀ r ∈ R k, z k * r = r * z k) ∧
      (∀ k, z k ≠ 1) ∧
      (∀ k, ∀ z' ∈ R k, (∀ r ∈ R k, z' * r = r * z') → z' ≠ 1 → z' = z k) ∧
      (∀ j k, z j * z k = z k * z j) ∧ (⨆ k, R k) = ⊤ :=
  transport_plus_four (fun X _ S => ∃ (R : Fin 4 → Subgroup X) (z : Fin 4 → X),
      (∀ k, R k ∈ S) ∧ (∀ k, z k ∈ R k) ∧ (∀ k, ∀ r ∈ R k, z k * r = r * z k) ∧
      (∀ k, z k ≠ 1) ∧
      (∀ k, ∀ z' ∈ R k, (∀ r ∈ R k, z' * r = r * z') → z' ≠ 1 → z' = z k) ∧
      (∀ j k, z j * z k = z k * z j) ∧ (⨆ k, R k) = ⊤) D4Facts3.of_gf3.exists_nodes hk

theorem top_le_iSup_fund_of_kind {c : CompData} (hk : c = CompData.model .POmegaPlus 4) :
    (⊤ : Subgroup c.G) ≤ ⨆ R ∈ c.fund, R :=
  transport_plus_four (fun X _ S => (⊤ : Subgroup X) ≤ ⨆ R ∈ S, R) (by
    have h1 := D4Facts3.of_gf3.gen 1
    rw [← h1]
    exact iSup_le fun k => le_iSup₂_of_le _
      ⟨1, Pi.single k 1, Or.inl (D4Facts3.of_gf3.long k), rfl⟩ le_rfl) hk

theorem generate_of_comm_of_kind {c : CompData} (hk : c = CompData.model .POmegaPlus 4)
    {R R' : Subgroup c.G} (hR : R ∈ c.fund) (hR' : R' ∈ c.fund) (hne : R' ≠ R)
    (hnc : ¬ Commutes R R') {z z' : c.G} (hz : z ∈ R) (hzz : ∀ r ∈ R, z * r = r * z)
    (hz1 : z ≠ 1) (hz' : z' ∈ R') (hzz' : ∀ r ∈ R', z' * r = r * z') (hz1' : z' ≠ 1)
    (hcomm : z * z' * z⁻¹ * z'⁻¹ ∈ Subgroup.center c.G) :
    (⨆ S ∈ {S : Subgroup c.G | S ∈ c.fund ∧ (S = R ∨ Commutes S R ∨ S = R' ∨ Commutes S R')},
      S) = ⊤ :=
  transport_plus_four (fun X _ S => ∀ R R' : Subgroup X, R ∈ S → R' ∈ S → R' ≠ R →
    ¬ Commutes R R' → ∀ z z' : X, z ∈ R → (∀ r ∈ R, z * r = r * z) → z ≠ 1 → z' ∈ R' →
    (∀ r ∈ R', z' * r = r * z') → z' ≠ 1 → z * z' * z⁻¹ * z'⁻¹ ∈ Subgroup.center X →
    (⨆ T ∈ {T : Subgroup X | T ∈ S ∧ (T = R ∨ Commutes T R ∨ T = R' ∨ Commutes T R')}, T) = ⊤)
    (fun _ _ hR hR' hne hnc _ _ hz hzz hz1 hz' hzz' hz1' hcomm =>
      D4Facts3.of_gf3.generate_of_comm hR hR' hne hnc hz hzz hz1 hz' hzz' hz1' hcomm) hk R R' hR
    hR' hne hnc z z' hz hzz hz1 hz' hzz' hz1' hcomm

end CFSG.ClassicalInvolution.Q3.Q3W.EX
