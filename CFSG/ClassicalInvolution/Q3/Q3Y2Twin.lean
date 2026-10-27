module

public import CFSG.ClassicalInvolution.Q3.Q3YComp
public import CFSG.ClassicalInvolution.Q3.Q3YModel
public import CFSG.ClassicalInvolution.ModelFacts.TG3Common
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralMain
public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2Main
public import CFSG.ClassicalInvolution.ModelFacts.CF3A
public import CFSG.LieType.HighestRoot.ModelCenter
public import CFSG.ClassicalInvolution.Q3.Q3TEdge
public import CFSG.ClassicalInvolution.Q3.Q3YLie
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Y2

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

@[expose] def TwinStrong3 {G : Type} [Group G] (𝓕 : Set (Subgroup G)) : Prop :=
  ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕, ∀ (e₁ : R₁ ≃* SL(2, GaloisField 3 1)) (e₂ : R₂ ≃* SL(2, GaloisField 3 1)),
    R₁ ≠ R₂ → (∀ a ∈ R₁, ∀ b ∈ R₂, a * b = b * a) →
      sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∈ Subgroup.center G → sl2Inv e₂ * (sl2Inv e₁)⁻¹ ≠ 1 →
      ∀ r₁ ∈ R₁, ∀ r₂ ∈ R₂, r₁ * r₁ = sl2Inv e₁ → r₂ * r₂ = sl2Inv e₂ →
        (⊤ : Subgroup G) ≤ Subgroup.centralizer ({sl2Inv e₁} : Set G) ⊔
          Subgroup.centralizer ({r₁ * r₂} : Set G) ⊔
          Subgroup.centralizer ({sl2Inv e₁ * (r₁ * r₂)} : Set G)

@[expose] def ModelTwinGen3 : Prop :=
  ∀ (t : StatedLieTag) (n : ℕ), IsFundTag t → StatedLieAdmissible t n 3 1 → t ≠ .G2 →
    t ≠ .trialityD4 → TwinStrong3 (fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D)

theorem eq_one_of_map_central {X : Type} [Group X] {c : CompData} (ψ : c.G →* X)
    (hker : ψ.ker ≤ Subgroup.center c.G) {t : StatedLieTag} {n : ℕ} (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (hc : c = CompData.model t n) {R : Subgroup c.G}
    (hR : R ∈ c.fund) {x : c.G} (hx : x ∈ R) (hxc : ∀ y : X, ψ x * y = y * ψ x) : x = 1 := by
  subst hc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : ¬ (t = .PSL ∧ n = 2) := by
    rintro ⟨rfl, rfl⟩
    exact hadm.2.2.2.2 rfl
  refine ModelFacts.fundNoncentral_generic 3 t n 1 hfund hadm hne R hR x hx fun y => hker ?_
  have h := hxc (ψ y)
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, h]
  group

theorem model_twin_component {X : Type} [Group X] {c : CompData} (ψ : c.G →* X)
    (hker : ψ.ker ≤ Subgroup.center c.G) {t : StatedLieTag} {n : ℕ} (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (hc : c = CompData.model t n) (hTwin : ModelTwinGen3)
    {R₂ R₃ : Subgroup c.G} (hR₂ : R₂ ∈ c.fund) (hR₃ : R₃ ∈ c.fund)
    (h24₂ : Nat.card (R₂.map ψ) = 24) (h24₃ : Nat.card (R₃.map ψ) = 24)
    (hne : R₂.map ψ ≠ R₃.map ψ) (hcomm : ∀ a ∈ R₂.map ψ, ∀ b ∈ R₃.map ψ, a * b = b * a)
    {ζ₁ ζ₂ θ₁ θ₂ θ₃ : X} (hζ₁c : ∀ x : X, ζ₁ * x = x * ζ₁) (hζ₁ : ζ₁ ≠ 1) (hζ₂ : ζ₂ ≠ 1)
    (hζ₂sq : ζ₂ * ζ₂ = 1)
    (hζ₃ : ζ₁ * ζ₂ ≠ 1) (hζ₁sq : ζ₁ * ζ₁ = 1) (hζ₂K : ζ₂ ∈ R₂.map ψ)
    (hζ₃K : ζ₁ * ζ₂ ∈ R₃.map ψ) (hθ₂K : θ₂ ∈ R₂.map ψ) (hθ₃K : θ₃ ∈ R₃.map ψ)
    (hθ₂ : θ₂ * θ₂ = ζ₂) (hθ₃ : θ₃ * θ₃ = ζ₁ * ζ₂) (hθ₁ : ∀ q ∈ ψ.range, θ₁ * q = q * θ₁)
    (hθ₁ζ : ζ₂ * θ₁ = θ₁ * ζ₂) :
    ψ.range ≤ Subgroup.centralizer ({ζ₂} : Set X) ⊔
      Subgroup.centralizer ({θ₁ * θ₂ * θ₃} : Set X) ⊔
      Subgroup.centralizer ({ζ₂ * (θ₁ * θ₂ * θ₃)} : Set X) := by
  subst hc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hq : CFSG.Open.IsQuasisimple (CompData.model t n).G :=
    ModelFacts.isQuasisimple_modelUniv t n 3 1 Nat.prime_three hfund hadm
  have hfin : Finite (CompData.model t n).G :=
    ModelFacts.finite_modelUniv hp2 Nat.prime_three hfund hadm
  have hcentral : ∀ κ : (CompData.model t n).G, ψ κ = ζ₁ → κ ∈ Subgroup.center _ := by
    intro κ hκ
    refine ModelFacts.mem_center_of_commutators_mem_center hq fun y => hker ?_
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hκ,
      hζ₁c (ψ y)]
    group
  obtain ⟨ρ₂, hρ₂, hρ₂ψ⟩ := hζ₂K
  obtain ⟨ρ₃, hρ₃, hρ₃ψ⟩ := hζ₃K
  have hζ₂i' : ζ₂⁻¹ = ζ₂ := inv_eq_of_mul_eq_one_right hζ₂sq
  have hκ : ψ (ρ₃ * ρ₂⁻¹) = ζ₁ := by
    rw [map_mul, map_inv, hρ₃ψ, hρ₂ψ, hζ₂i', mul_assoc, hζ₂sq, mul_one]
  have hκc := hcentral _ hκ
  have hG2 : t ≠ .G2 := by
    rintro rfl
    have hbot := Q3Y.center_modelUniv_eq_bot_of_tag (Or.inl rfl) hadm
    rw [hbot, Subgroup.mem_bot] at hκc
    exact hζ₁ (hκ ▸ (hκc ▸ map_one ψ))
  have hD4 : t ≠ .trialityD4 := by
    rintro rfl
    have hbot := Q3Y.center_modelUniv_eq_bot_of_tag (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hadm
    rw [hbot, Subgroup.mem_bot] at hκc
    exact hζ₁ (hκ ▸ (hκc ▸ map_one ψ))
  obtain ⟨e₂⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund hadm hG2
    hD4 hR₂
  obtain ⟨e₃⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund hadm hG2
    hD4 hR₃
  obtain ⟨u₂, hinj₂⟩ := ModelFacts.TG3.uniqueInvolution_map3 ψ e₂ h24₂
  obtain ⟨u₃, hinj₃⟩ := ModelFacts.TG3.uniqueInvolution_map3 ψ e₃ h24₃
  have hζ₂i : ζ₂ = ψ (sl2Inv e₂) :=
    ((u₂.unique ζ₂ ⟨ρ₂, hρ₂, hρ₂ψ⟩ hζ₂sq).resolve_left hζ₂)
  have hζ₃sq : (ζ₁ * ζ₂) * (ζ₁ * ζ₂) = 1 := by
    have h1 : ζ₂ * ζ₁ = ζ₁ * ζ₂ := (hζ₁c ζ₂).symm
    calc (ζ₁ * ζ₂) * (ζ₁ * ζ₂) = ζ₁ * (ζ₂ * ζ₁) * ζ₂ := by group
      _ = ζ₁ * (ζ₁ * ζ₂) * ζ₂ := by rw [h1]
      _ = (ζ₁ * ζ₁) * (ζ₂ * ζ₂) := by group
      _ = 1 := by rw [hζ₁sq, hζ₂sq, one_mul]
  have hζ₃i : ζ₁ * ζ₂ = ψ (sl2Inv e₃) :=
    ((u₃.unique (ζ₁ * ζ₂) ⟨ρ₃, hρ₃, hρ₃ψ⟩ hζ₃sq).resolve_left hζ₃)
  have hcψ : ψ (sl2Inv e₃ * (sl2Inv e₂)⁻¹) = ζ₁ := by
    rw [map_mul, map_inv, ← hζ₃i, ← hζ₂i, hζ₂i', mul_assoc, hζ₂sq, mul_one]
  have hcc := hcentral _ hcψ
  have hc1 : sl2Inv e₃ * (sl2Inv e₂)⁻¹ ≠ 1 := fun h => hζ₁ (hcψ ▸ (h ▸ map_one ψ))
  have hRne : R₂ ≠ R₃ := fun h => hne (by rw [h])
  obtain ⟨τ₂, hτ₂, hτ₂ψ⟩ := hθ₂K
  obtain ⟨τ₃, hτ₃, hτ₃ψ⟩ := hθ₃K
  have hτ₂sq : τ₂ * τ₂ = sl2Inv e₂ := by
    refine hinj₂ _ (R₂.mul_mem hτ₂ hτ₂) _ (sl2Inv_mem e₂) ?_
    rw [map_mul, hτ₂ψ, hθ₂, hζ₂i]
  have hτ₃sq : τ₃ * τ₃ = sl2Inv e₃ := by
    refine hinj₃ _ (R₃.mul_mem hτ₃ hτ₃) _ (sl2Inv_mem e₃) ?_
    rw [map_mul, hτ₃ψ, hθ₃, hζ₃i]
  have hk3 : ∀ x ∈ ψ.ker, x ^ 3 = 1 → x = 1 := fun x hx hx3 =>
    CFSG.ComponentClassification.RankTwoOddLie.modelCenterPPrime t n 3 1 Nat.prime_three hp2
      hfund hadm x (hker hx) hx3
  have hcommM : ∀ a ∈ R₂, ∀ b ∈ R₃, a * b = b * a := fun a ha b hb =>
    (ModelFacts.commute_of_map_commute_of_gen3 ψ hker hk3 (ModelFacts.gen3_of_equiv_sl2 e₂)
      (fun a' ha' => hcomm _ (Subgroup.mem_map_of_mem ψ ha') _ (Subgroup.mem_map_of_mem ψ hb))) a ha
  have hgen := hTwin t n hfund hadm hG2 hD4 R₂ hR₂ R₃ hR₃ e₂ e₃ hRne hcommM hcc hc1 τ₂ hτ₂ τ₃
    hτ₃ hτ₂sq hτ₃sq
  have h1 : (Subgroup.centralizer ({sl2Inv e₂} : Set _)).map ψ ≤
      Subgroup.centralizer ({ζ₂} : Set X) := by
    rintro _ ⟨m, hm, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hζ₂i, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp hm]
  have h2 : (Subgroup.centralizer ({τ₂ * τ₃} : Set _)).map ψ ≤
      Subgroup.centralizer ({θ₁ * θ₂ * θ₃} : Set X) := by
    rintro _ ⟨m, hm, rfl⟩
    have hm' : ψ m * (θ₂ * θ₃) = (θ₂ * θ₃) * ψ m := by
      have := congrArg ψ (Subgroup.mem_centralizer_singleton_iff.mp hm)
      simpa only [map_mul, hτ₂ψ, hτ₃ψ] using this
    have hθm : θ₁ * ψ m = ψ m * θ₁ := hθ₁ _ ⟨m, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    symm
    calc (θ₁ * θ₂ * θ₃) * ψ m = θ₁ * ((θ₂ * θ₃) * ψ m) := by group
      _ = θ₁ * (ψ m * (θ₂ * θ₃)) := by rw [hm']
      _ = (θ₁ * ψ m) * (θ₂ * θ₃) := by group
      _ = (ψ m * θ₁) * (θ₂ * θ₃) := by rw [hθm]
      _ = ψ m * (θ₁ * θ₂ * θ₃) := by group
  have h3 : (Subgroup.centralizer ({sl2Inv e₂ * (τ₂ * τ₃)} : Set _)).map ψ ≤
      Subgroup.centralizer ({ζ₂ * (θ₁ * θ₂ * θ₃)} : Set X) := by
    rintro _ ⟨m, hm, rfl⟩
    have hm' : ψ m * (ζ₂ * (θ₂ * θ₃)) = (ζ₂ * (θ₂ * θ₃)) * ψ m := by
      have := congrArg ψ (Subgroup.mem_centralizer_singleton_iff.mp hm)
      simpa only [map_mul, hτ₂ψ, hτ₃ψ, ← hζ₂i] using this
    have hθm : θ₁ * ψ m = ψ m * θ₁ := hθ₁ _ ⟨m, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    symm
    calc (ζ₂ * (θ₁ * θ₂ * θ₃)) * ψ m = (ζ₂ * θ₁) * (θ₂ * θ₃) * ψ m := by group
      _ = (θ₁ * ζ₂) * (θ₂ * θ₃) * ψ m := by rw [hθ₁ζ]
      _ = θ₁ * ((ζ₂ * (θ₂ * θ₃)) * ψ m) := by group
      _ = θ₁ * (ψ m * (ζ₂ * (θ₂ * θ₃))) := by rw [hm']
      _ = (θ₁ * ψ m) * (ζ₂ * (θ₂ * θ₃)) := by group
      _ = (ψ m * θ₁) * (ζ₂ * (θ₂ * θ₃)) := by rw [hθm]
      _ = ψ m * (θ₁ * ζ₂ * (θ₂ * θ₃)) := by group
      _ = ψ m * (ζ₂ * θ₁ * (θ₂ * θ₃)) := by rw [hθ₁ζ]
      _ = ψ m * (ζ₂ * (θ₁ * θ₂ * θ₃)) := by group
  calc ψ.range = (⊤ : Subgroup _).map ψ := MonoidHom.range_eq_map ψ
    _ ≤ (Subgroup.centralizer ({sl2Inv e₂} : Set _) ⊔
        Subgroup.centralizer ({τ₂ * τ₃} : Set _) ⊔
        Subgroup.centralizer ({sl2Inv e₂ * (τ₂ * τ₃)} : Set _)).map ψ := Subgroup.map_mono hgen
    _ ≤ _ := by
      rw [Subgroup.map_sup, Subgroup.map_sup]
      exact sup_le_sup (sup_le_sup h1 h2) h3

end CFSG.ClassicalInvolution.Q3.Q3Y2
