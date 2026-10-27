module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeTransfer
import CFSG.LocalAnalysis.GLTheoremA.PComp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm

open CFSG.Open CFSG.AGLEmbedding
open scoped commutatorElement

variable {A : Type} [Group A]

@[expose] def WCent (P : Subgroup A) (b : A) : Prop :=
  ∀ w (hw : w ∈ P), QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩ ∈ wSup (↥P ⧸ CFSG.pCore 2 ↥P) →
    b * w * b⁻¹ * w⁻¹ ∈ pCoreOf 2 P

@[expose] def PairComm (p : ℕ) (Y P : Subgroup A) : Prop :=
  ∀ b₁ b₂ : A, (∃ k : ℕ, b₁ ^ p ^ k = 1) → (∃ k : ℕ, b₂ ^ p ^ k = 1) →
    (∃ k : ℕ, ⁅b₁, b₂⁆ ^ p ^ k = 1) →
    b₁ ∈ Subgroup.normalizer (Y : Set A) → b₂ ∈ Subgroup.normalizer (Y : Set A) →
    b₁ ∈ Subgroup.normalizer (P : Set A) → b₂ ∈ Subgroup.normalizer (P : Set A) →
    WCent P b₁ → WCent P b₂ → ∀ y ∈ Y, ⁅b₁, b₂⁆ * y = y * ⁅b₁, b₂⁆

@[expose] def ParabCommOn (𝔉 : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Y P : Subgroup A) (p : ℕ), p.Prime → p ≠ 2 →
    Open.IsQuasisimple ↥Y → pCoreOf 2 Y = ⊥ → 𝔉 (↥Y ⧸ Subgroup.center ↥Y) →
    IsParabolicTwo Y P → P ≠ Y → (∃ x ∈ P, ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 P) →
    PairComm p Y P ∨ 4 ≤ Open.pRank p Y

theorem pCore_eq_bot_of_pCoreOf {Y : Subgroup A} (h2 : pCoreOf 2 Y = ⊥) :
    CFSG.pCore 2 ↥Y = ⊥ := by
  rw [pCoreOf, Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective] at h2
  exact h2

theorem wSup_eq_top {Q : Type} [Group Q] (hQ : Open.IsQuasisimple Q) : wSup Q = ⊤ := by
  refine eq_top_iff.2 (le_iSup₂_of_le (⊤ : Subgroup Q) ?_ le_rfl)
  exact ⟨IsSubnormal.refl _, Or.inl
    (CFSG.LocalAnalysis.GLTheoremA.isComponentOf_top_of_isQuasisimple hQ)⟩

theorem centralizes_of_wCent_self {Y : Subgroup A} (hY : Open.IsQuasisimple ↥Y)
    (h2 : pCoreOf 2 Y = ⊥) {b : A} (hb : WCent Y b) : ∀ y ∈ Y, b * y = y * b := by
  intro y hy
  have hc := pCore_eq_bot_of_pCoreOf h2
  have hQ : Open.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    Open.IsQuasisimple.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientBot (G := ↥Y))) hY
  have h1 := hb y hy (by rw [wSup_eq_top hQ]; exact Subgroup.mem_top _)
  rw [h2, Subgroup.mem_bot] at h1
  calc b * y = b * y * b⁻¹ * y⁻¹ * (y * b) := by group
    _ = y * b := by rw [h1, one_mul]

theorem commutator_le_centralizer_of_pairComm {p : ℕ} {Y P B : Subgroup A}
    (h : PairComm p Y P) (hB : IsPGroup p ↥B) (hBY : B ≤ Subgroup.normalizer (Y : Set A))
    (hBP : B ≤ Subgroup.normalizer (P : Set A)) (hW : ∀ b ∈ B, WCent P b) :
    ∀ c ∈ ⁅B, B⁆, ∀ y ∈ Y, c * y = y * c := by
  have hpow : ∀ b ∈ B, ∃ k : ℕ, b ^ p ^ k = 1 := fun b hb => by
    obtain ⟨k, hk⟩ := hB ⟨b, hb⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hle : ⁅B, B⁆ ≤ Subgroup.centralizer (Y : Set A) := by
    rw [Subgroup.commutator_le]
    intro b₁ h₁ b₂ h₂
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hc : ⁅b₁, b₂⁆ ∈ B := B.commutator_le_self (Subgroup.commutator_mem_commutator h₁ h₂)
    exact (h b₁ b₂ (hpow b₁ h₁) (hpow b₂ h₂) (hpow _ hc) (hBY h₁) (hBY h₂) (hBP h₁) (hBP h₂)
      (hW b₁ h₁) (hW b₂ h₂) y hy).symm
  intro c hc y hy
  exact (Subgroup.mem_centralizer_iff.mp (hle hc) y hy).symm

@[expose] def ParabCommGroupOn (𝔉 : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Y P B : Subgroup A) (p : ℕ), p.Prime → p ≠ 2 →
    Open.IsQuasisimple ↥Y → pCoreOf 2 Y = ⊥ → 𝔉 (↥Y ⧸ Subgroup.center ↥Y) →
    IsParabolicTwo Y P → P ≠ Y → (∃ x ∈ P, ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 P) →
    IsPGroup p ↥B → B ≤ Subgroup.normalizer (Y : Set A) → B ≤ Subgroup.normalizer (P : Set A) →
    (∀ b ∈ B, WCent P b) → (∀ c ∈ ⁅B, B⁆, ∀ y ∈ Y, c * y = y * c) ∨ 4 ≤ Open.pRank p Y

theorem ParabCommOn.group {𝔉 : ∀ (X : Type) [Group X], Prop} (h : ParabCommOn 𝔉) :
    ParabCommGroupOn 𝔉 :=
  fun A _ _ Y P B p hp hp2 hY h2 hF hpar hne hna hB hBY hBP hW =>
    (h A Y P p hp hp2 hY h2 hF hpar hne hna).imp
      (fun hc => commutator_le_centralizer_of_pairComm hc hB hBY hBP hW) id

theorem parabCommGroupOn_or {𝔉₁ 𝔉₂ : ∀ (X : Type) [Group X], Prop} (h₁ : ParabCommGroupOn 𝔉₁)
    (h₂ : ParabCommGroupOn 𝔉₂) : ParabCommGroupOn fun X _ => 𝔉₁ X ∨ 𝔉₂ X :=
  fun A _ _ Y P B p hp hp2 hY h2 hF =>
    hF.elim (h₁ A Y P B p hp hp2 hY h2) (h₂ A Y P B p hp hp2 hY h2)

theorem ParabCommGroupOn.mono {𝔉₁ 𝔉₂ : ∀ (X : Type) [Group X], Prop}
    (h : ParabCommGroupOn 𝔉₂) (himp : ∀ (X : Type) [Group X], 𝔉₁ X → 𝔉₂ X) :
    ParabCommGroupOn 𝔉₁ :=
  fun A _ _ Y P B p hp hp2 hY h2 hF => h A Y P B p hp hp2 hY h2 (himp _ hF)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm
