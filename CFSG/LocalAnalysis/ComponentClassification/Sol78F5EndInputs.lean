module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneInputs
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F514Basic

public section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.Foote5 CFSG.Goldschmidt CFSG.Goldschmidt75 CFSG.ABGLocalTools

@[expose] def EndPointedMaximalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L₀ L Q S T : Subgroup G) (z t s : G) (𝕊 : Type) [Group 𝕊]
    [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊) (Lin : Subgroup (MulAut 𝕊)),
    Hyp L₀ L Q S T z t s ε Lin → FooteMinimal G → ∀ W : Subgroup G, W ≠ ⊥ → Odd (Nat.card W) →
    (∀ B₁ B₂ : Subgroup G, B₁ ≤ S ⊓ L → B₂ ≤ conjugate (S ⊓ L) s → B₁ ≠ ⊥ → B₂ ≠ ⊥ →
      W ∈ NSet (B₁ ⊔ B₂) ∧ ∀ X ∈ NSet (B₁ ⊔ B₂), X ≤ W) →
    (∀ t₁ ∈ S ⊓ L, orderOf t₁ = 2 → ∀ t₂ ∈ conjugate (S ⊓ L) s, orderOf t₂ = 2 →
      ⁅oddCent t₁, zpowers t₂⁆ ≤ W ∧ ⁅oddCent t₂, zpowers t₁⁆ ≤ W) →
    ∀ hzN : z ∈ normalizer (W : Set G),
      FootePointedMaximal (⟨z, hzN⟩ : normalizer (W : Set G))
        (L.subgroupOf (normalizer (W : Set G)))

@[expose] def EndOddLieInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → Blueprint.OddLieType X →
    ∀ (z t : X) (K P D : Subgroup X), IsTwoComponentAt z K →
      (∀ K₂ : Subgroup X, IsTwoComponentAt z K₂ → K₂ = K) →
      IsSimpleGroup (K ⧸ pPrimeCore 2 K) → FooteFamilyType K →
      IsEmpty (X ≃* K ⧸ pPrimeCore 2 K) → IsSylowOf 2 P K → t ∈ P → orderOf t = 2 →
      z * t = t * z → z ∈ D → D ≤ centralizer ({z} : Set X) ⊓ coreActionKernel K →
      P ≤ centralizer (D : Set X) → AschbacherTheorem3.IsDihedralTwoGroup D → 8 ≤ Nat.card D →
      Group.IsSolvable ↥(centralizer ({z} : Set X) ⊓ centralizer (K : Set X)) →
      (∀ b ∈ D, orderOf b = 2 → ∃ Y : Subgroup X, IsTwoComponentAt b Y ∧ P ≤ Y ∧
        Nonempty (Y ⧸ pPrimeCore 2 Y ≃* K ⧸ pPrimeCore 2 K)) →
      ¬ Group.IsSolvable ↥(centralizer ({z * t} : Set X))

@[expose] def EndOddLieInputFor (T : Finset Assembly.LowTwoRank.StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X →
    ∀ (τ : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ), τ ∈ T → p.Prime → p ≠ 2 →
      Assembly.LowTwoRank.StatedLieAdmissible τ n p f → Blueprint.LieModel X τ n p f →
    ∀ (z t : X) (K P D : Subgroup X), IsTwoComponentAt z K →
      (∀ K₂ : Subgroup X, IsTwoComponentAt z K₂ → K₂ = K) →
      IsSimpleGroup (K ⧸ pPrimeCore 2 K) → FooteFamilyType K →
      IsEmpty (X ≃* K ⧸ pPrimeCore 2 K) → IsSylowOf 2 P K → t ∈ P → orderOf t = 2 →
      z * t = t * z → z ∈ D → D ≤ centralizer ({z} : Set X) ⊓ coreActionKernel K →
      P ≤ centralizer (D : Set X) → AschbacherTheorem3.IsDihedralTwoGroup D → 8 ≤ Nat.card D →
      Group.IsSolvable ↥(centralizer ({z} : Set X) ⊓ centralizer (K : Set X)) →
      (∀ b ∈ D, orderOf b = 2 → ∃ Y : Subgroup X, IsTwoComponentAt b Y ∧ P ≤ Y ∧
        Nonempty (Y ⧸ pPrimeCore 2 Y ≃* K ⧸ pPrimeCore 2 K)) →
      ¬ Group.IsSolvable ↥(centralizer ({z * t} : Set X))

theorem endOddLieInput_of_for (hE : EndOddLieInputFor Burgoyne.oddExceptionalTags)
    (hL : EndOddLieInputFor {.PSL, .PSU}) (hS : EndOddLieInputFor {.PSp})
    (hO : EndOddLieInputFor {.POmegaOdd, .POmegaPlus, .POmegaMinus}) : EndOddLieInput := by
  intro X _ _ hX hodd
  obtain ⟨τ, n, p, f, hp, hp2, hadm, hmod⟩ := hodd
  have key : ∀ T : Finset Assembly.LowTwoRank.StatedLieTag, EndOddLieInputFor T → τ ∈ T →
      EndOddLieInputFor {τ} := fun T hT hτ X' _ _ hX' τ' n' p' f' hτ' =>
    hT X' hX' τ' n' p' f' (by rw [Finset.mem_singleton] at hτ'; exact hτ' ▸ hτ)
  have hτ : EndOddLieInputFor {τ} := by
    cases τ with
    | PSL => exact key _ hL (by decide)
    | PSU => exact key _ hL (by decide)
    | PSp => exact key _ hS (by decide)
    | POmegaOdd => exact key _ hO (by decide)
    | POmegaPlus => exact key _ hO (by decide)
    | POmegaMinus => exact key _ hO (by decide)
    | G2 => exact key _ hE (by decide)
    | F4 => exact key _ hE (by decide)
    | E6 => exact key _ hE (by decide)
    | E7 => exact key _ hE (by decide)
    | E8 => exact key _ hE (by decide)
    | twistedE6 => exact key _ hE (by decide)
    | trialityD4 => exact key _ hE (by decide)
    | twistedG2 => exact key _ hE (by decide)
    | twistedB2 => exact absurd hadm.2.2.2.1 hp2
    | twistedF4 => exact absurd hadm.2.2.2.1 hp2
    | Tits => exact absurd hadm.2.2.2.1 hp2
  exact hτ X hX τ n p f (Finset.mem_singleton_self τ) hp hp2 hadm hmod

end CFSG.ComponentClassification.Sol78.F514
