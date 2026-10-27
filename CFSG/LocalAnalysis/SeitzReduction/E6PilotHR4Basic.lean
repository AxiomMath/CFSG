module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR4Basic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneOddDerivation
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6InnerBasic
public import CFSG.LieType.Ree.LargeReeA1Pair
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneEInner
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

theorem commutatorElement_mul_mul_eq_mul_of_commute {a a' b b' : G} (h1 : Commute a b)
    (h2 : Commute a b') (h3 : Commute a' b) (h4 : Commute a' b') :
    ⁅a * b, a' * b'⁆ = ⁅a, a'⁆ * ⁅b, b'⁆ := by
  have hd : Commute (b * b' * b⁻¹) a⁻¹ :=
    ((h1.mul_right h2).mul_right h1.inv_right).inv_left.symm
  have hc : Commute (b * b' * b⁻¹ * b'⁻¹) a'⁻¹ :=
    (((h3.mul_right h4).mul_right h3.inv_right).mul_right h4.inv_right).inv_left.symm
  simp only [commutatorElement_def]
  calc a * b * (a' * b') * (a * b)⁻¹ * (a' * b')⁻¹
      = a * (b * a') * b' * b⁻¹ * a⁻¹ * b'⁻¹ * a'⁻¹ := by group
    _ = a * (a' * b) * b' * b⁻¹ * a⁻¹ * b'⁻¹ * a'⁻¹ := by rw [h3.eq]
    _ = a * a' * ((b * b' * b⁻¹) * a⁻¹) * b'⁻¹ * a'⁻¹ := by group
    _ = a * a' * (a⁻¹ * (b * b' * b⁻¹)) * b'⁻¹ * a'⁻¹ := by rw [hd.eq]
    _ = a * a' * a⁻¹ * ((b * b' * b⁻¹ * b'⁻¹) * a'⁻¹) := by group
    _ = a * a' * a⁻¹ * (a'⁻¹ * (b * b' * b⁻¹ * b'⁻¹)) := by rw [hc.eq]
    _ = a * a' * a⁻¹ * a'⁻¹ * (b * b' * b⁻¹ * b'⁻¹) := by group

theorem commutator_closure_eq_self_of_subset {S : Set G}
    (h : S ⊆ (⁅closure S, closure S⁆ : Subgroup G)) : ⁅closure S, closure S⁆ = closure S :=
  le_antisymm (Subgroup.commutator_le_self _) ((closure_le _).2 h)

theorem coe_commutatorElement_subgroup {H : Subgroup G} (u v : H) :
    ((⁅u, v⁆ : H) : G) = ⁅(u : G), (v : G)⁆ :=
  map_commutatorElement H.subtype u v

end Group

@[expose] def a2Roots : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  [(![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ), (![0, 0, 1, 0, 0, 0] : Fin 6 → ℤ),
    (![1, 0, 1, 0, 0, 0] : Fin 6 → ℤ), (![-1, 0, 0, 0, 0, 0] : Fin 6 → ℤ),
    (![0, 0, -1, 0, 0, 0] : Fin 6 → ℤ), (![-1, 0, -1, 0, 0, 0] : Fin 6 → ℤ)]

@[expose] def a2Root : Fin TwistTag.E6.tag.rank → ℤ :=
  (![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ)

local notation "ρ" => permLattice TwistTag.E6.perm

theorem a2Root_mem : a2Root ∈ a2Roots := List.mem_cons_self

theorem perm_perm_a2Roots {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : β ∈ a2Roots) :
    ρ (ρ β) = β := by
  revert β
  decide

theorem a2Roots_split {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : β ∈ a2Roots) :
    ∃ β₁ ∈ a2Roots, ∃ β₂ ∈ a2Roots, β₁ + β₂ = β ∧ β₁ ≠ β₂ ∧ β₁ ≠ -β₂ ∧ ρ β₁ ≠ ρ β₂ ∧
      ρ β₁ ≠ -ρ β₂ := by
  revert β
  decide


theorem a2Roots_isRoot {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : β ∈ a2Roots) :
    IsRoot TwistTag.E6.tag β ∧ IsRoot TwistTag.E6.tag (ρ β) := by
  have h : ∀ β ∈ a2Roots, β ∈ rootFinset TwistTag.E6.tag ∧ ρ β ∈ rootFinset TwistTag.E6.tag := by
    decide +kernel
  exact ⟨mem_rootFinset.1 (h β hβ).1, mem_rootFinset.1 (h β hβ).2⟩


theorem a2Roots_perp {β γ : Fin TwistTag.E6.tag.rank → ℤ} (hβ : β ∈ a2Roots)
    (hγ : γ ∈ a2Roots) : β ≠ -ρ γ ∧ ¬IsRoot TwistTag.E6.tag (β + ρ γ) := by
  have h : ∀ β ∈ a2Roots, ∀ γ ∈ a2Roots,
      β ≠ -ρ γ ∧ oddDerivNotRootB TwistTag.E6.tag (β + ρ γ) = true := by
    decide +kernel
  exact ⟨(h β hβ γ hγ).1, not_isRoot_of_oddDerivNotRootB (h β hβ γ hγ).2⟩

theorem a2Roots_perp_highRoot {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : β ∈ a2Roots) :
    (β ≠ -e6HighestRoot ∧ ¬IsRoot TwistTag.E6.tag (β + e6HighestRoot)) ∧
      (ρ β ≠ -e6HighestRoot ∧ ¬IsRoot TwistTag.E6.tag (ρ β + e6HighestRoot)) := by
  have h : ∀ β ∈ a2Roots, (β ≠ -e6HighestRoot ∧
      oddDerivNotRootB TwistTag.E6.tag (β + e6HighestRoot) = true) ∧
      (ρ β ≠ -e6HighestRoot ∧ oddDerivNotRootB TwistTag.E6.tag (ρ β + e6HighestRoot) = true) := by
    decide +kernel
  exact ⟨⟨(h β hβ).1.1, not_isRoot_of_oddDerivNotRootB (h β hβ).1.2⟩,
    ⟨(h β hβ).2.1, not_isRoot_of_oddDerivNotRootB (h β hβ).2.2⟩⟩

variable {K : Type} [Field K]

@[expose] noncomputable def a2Gen (φ : K →+* K) (β : Fin TwistTag.E6.tag.rank → ℤ) (c : K) :
    adjointGroup TwistTag.E6.tag K :=
  ⟨pinnedX TwistTag.E6.tag K β c * pinnedX TwistTag.E6.tag K (ρ β) (φ c),
    mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _)⟩

theorem coe_a2Gen (φ : K →+* K) (β : Fin TwistTag.E6.tag.rank → ℤ) (c : K) :
    (a2Gen φ β c : ModGL TwistTag.E6.tag K) =
      pinnedX TwistTag.E6.tag K β c * pinnedX TwistTag.E6.tag K (ρ β) (φ c) :=
  rfl

@[expose] noncomputable def a2Pair (φ : K →+* K) (D : Set K) :
    Subgroup (adjointGroup TwistTag.E6.tag K) :=
  closure {x | ∃ β ∈ a2Roots, ∃ c ∈ D, x = a2Gen φ β c}

theorem a2Gen_mem_a2Pair (φ : K →+* K) {D : Set K} {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : β ∈ a2Roots) {c : K} (hc : c ∈ D) : a2Gen φ β c ∈ a2Pair φ D :=
  subset_closure ⟨β, hβ, c, hc, rfl⟩


theorem entrywise_a2Gen (σ : K →+* K) (β : Fin TwistTag.E6.tag.rank → ℤ) (c : K) :
    Units.map (entrywiseHom σ) (a2Gen (RingHom.id K) β c : ModGL TwistTag.E6.tag K) =
      a2Gen (RingHom.id K) β (σ c) := by
  rw [coe_a2Gen, coe_a2Gen, map_mul, RingHom.id_apply, RingHom.id_apply]
  congr 1 <;> exact Units.ext (entrywise_pinnedX σ _ _)

section Commute

variable {R : Type*} [CommRing R]

theorem commute_a2Roots {β γ : Fin TwistTag.E6.tag.rank → ℤ} (hβ : β ∈ a2Roots)
    (hγ : γ ∈ a2Roots) (c d : R) :
    Commute (pinnedX TwistTag.E6.tag R β c) (pinnedX TwistTag.E6.tag R (ρ γ) d) :=
  commute_pinnedX_of_oddDeriv (a2Roots_isRoot hβ).1 (a2Roots_isRoot hγ).2
    (a2Roots_perp hβ hγ).1 (a2Roots_perp hβ hγ).2 c d

theorem commute_a2Roots_highRoot {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : β ∈ a2Roots)
    (c d : R) :
    Commute (pinnedX TwistTag.E6.tag R β c) (pinnedX TwistTag.E6.tag R e6HighestRoot d) ∧
      Commute (pinnedX TwistTag.E6.tag R (ρ β) c)
        (pinnedX TwistTag.E6.tag R e6HighestRoot d) :=
  ⟨commute_pinnedX_of_oddDeriv (a2Roots_isRoot hβ).1 isRoot_e6HighestRoot
      (a2Roots_perp_highRoot hβ).1.1 (a2Roots_perp_highRoot hβ).1.2 c d,
    commute_pinnedX_of_oddDeriv (a2Roots_isRoot hβ).2 isRoot_e6HighestRoot
      (a2Roots_perp_highRoot hβ).2.1 (a2Roots_perp_highRoot hβ).2.2 c d⟩

end Commute

variable [CharP K 2]

theorem commutator_a2Pair (φ : K →+* K) {D : Set K} (hD : (1 : K) ∈ D) :
    ⁅a2Pair φ D, a2Pair φ D⁆ = a2Pair φ D := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hlac : oddDerivLacedCheck TwistTag.E6.tag = true :=
    oddDerivLacedCheck_of_simplyLaced (Or.inr (Or.inl rfl))
  refine commutator_closure_eq_self_of_subset ?_
  rintro _ ⟨β, hβ, c, hc, rfl⟩
  obtain ⟨β₁, h₁, β₂, h₂, hsum, hne, hne', hρne, hρne'⟩ := a2Roots_split hβ
  have key : ⁅a2Gen φ β₁ c, a2Gen φ β₂ 1⁆ = a2Gen φ β c := by
    apply Subtype.ext
    rw [coe_commutatorElement_subgroup, coe_a2Gen, coe_a2Gen,
      coe_a2Gen, commutatorElement_mul_mul_eq_mul_of_commute (commute_a2Roots h₁ h₁ _ _)
        (commute_a2Roots h₁ h₂ _ _) (commute_a2Roots h₂ h₁ _ _) (commute_a2Roots h₂ h₂ _ _)]
    have hr : IsRoot TwistTag.E6.tag (β₁ + β₂) := hsum ▸ (a2Roots_isRoot hβ).1
    have hρr : IsRoot TwistTag.E6.tag (ρ β₁ + ρ β₂) := by
      rw [← permLattice_add, hsum]
      exact (a2Roots_isRoot hβ).2
    rw [commutatorElement_pinnedX_of_oddDerivLaced h2 hlac (a2Roots_isRoot h₁).1
        (a2Roots_isRoot h₂).1 hne hne' hr,
      commutatorElement_pinnedX_of_oddDerivLaced h2 hlac (a2Roots_isRoot h₁).2
        (a2Roots_isRoot h₂).2 hρne hρne' hρr, ← permLattice_add, hsum, map_one, mul_one,
      mul_one]
  rw [← key]
  exact commutator_mem_commutator (a2Gen_mem_a2Pair φ h₁ hc) (a2Gen_mem_a2Pair φ h₂ hD)

theorem twistHom_a2Gen (σ : K →+* K) (hσσ : ∀ c, σ (σ c) = c) {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : β ∈ a2Roots) (c : K) :
    twistHom TwistTag.E6 K σ (a2Gen σ β c : ModGL TwistTag.E6.tag K) = a2Gen σ β c := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [coe_a2Gen, map_mul, twistHom_pinnedX_eq_of_charTwo h2 σ (a2Roots_isRoot hβ).1,
    twistHom_pinnedX_eq_of_charTwo h2 σ (a2Roots_isRoot hβ).2]
  change _ = pinnedX TwistTag.E6.tag K β c * pinnedX TwistTag.E6.tag K (ρ β) (σ c)
  rw [perm_perm_a2Roots hβ, hσσ]
  exact (commute_a2Roots hβ hβ c (σ c)).eq.symm

omit [CharP K 2] in
theorem commute_a2Gen_pinnedX_highRoot (φ : K →+* K) {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : β ∈ a2Roots) (c d : K) :
    Commute (a2Gen φ β c : ModGL TwistTag.E6.tag K)
      (pinnedX TwistTag.E6.tag K e6HighestRoot d) := by
  rw [coe_a2Gen]
  exact ((commute_a2Roots_highRoot hβ c d).1).mul_left (commute_a2Roots_highRoot hβ (φ c) d).2

omit [CharP K 2] in
theorem a2Gen_add (φ : K →+* K) {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : β ∈ a2Roots)
    (a b : K) : a2Gen φ β (a + b) = a2Gen φ β a * a2Gen φ β b := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_a2Gen, coe_a2Gen, coe_a2Gen, map_add, pinnedX_add, pinnedX_add]
  have hc := (commute_a2Roots hβ hβ b (φ a)).eq
  calc pinnedX TwistTag.E6.tag K β a * pinnedX TwistTag.E6.tag K β b *
        (pinnedX TwistTag.E6.tag K (ρ β) (φ a) * pinnedX TwistTag.E6.tag K (ρ β) (φ b)) =
      pinnedX TwistTag.E6.tag K β a * (pinnedX TwistTag.E6.tag K β b *
        pinnedX TwistTag.E6.tag K (ρ β) (φ a)) * pinnedX TwistTag.E6.tag K (ρ β) (φ b) := by
        group
    _ = _ := by rw [hc]; group

theorem inv_pinnedX_mul_pinnedX_eq_a2Gen (φ : K →+* K) {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : β ∈ a2Roots) (c : K) :
    (pinnedX TwistTag.E6.tag K (ρ β) (φ c))⁻¹ * pinnedX TwistTag.E6.tag K β c =
      a2Gen φ β c := by
  rw [coe_a2Gen, pinnedX_neg, CharTwo.neg_eq]
  exact (commute_a2Roots hβ hβ c (φ c)).eq.symm

omit
  [CharP K 2] in
theorem a2Gen_ne_one (φ : K →+* K) {c : K} (hc : c ≠ 0) : a2Gen φ a2Root c ≠ 1 := by
  intro h
  have h' : pinnedX TwistTag.E6.tag K a2Root c * pinnedX TwistTag.E6.tag K (ρ a2Root) (φ c) =
      pinnedX TwistTag.E6.tag K a2Root 0 * pinnedX TwistTag.E6.tag K (ρ a2Root) 0 := by
    rw [pinnedX_zero, pinnedX_zero, mul_one, ← coe_a2Gen, h, OneMemClass.coe_one]
  have hpos : (IsRoot TwistTag.E6.tag a2Root ∧ 0 < height a2Root) ∧
      IsRoot TwistTag.E6.tag (ρ a2Root) ∧ 0 < height (ρ a2Root) :=
    ⟨⟨(a2Roots_isRoot a2Root_mem).1, by decide⟩, ⟨(a2Roots_isRoot a2Root_mem).2, by decide⟩⟩
  exact hc (CFSG.LieType.Ree.pinnedX_mul_pinnedX_inj (Or.inl hpos) (by decide) h').1

end CFSG.SeitzReduction.E6Pilot
