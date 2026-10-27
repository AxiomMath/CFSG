module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdSplit

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

@[expose] def L34SuzEvenStandardExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G], L34BaseSetting G → ∀ A : Subgroup G, IsStandardSubgroup A →
    Blueprint.NativeSporadic.IsSporadic (↥A ⧸ center ↥A) .Suz → Even (Nat.card (center ↥A)) →
      False

@[expose] def L34SuzOddStandardExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G], L34BaseSetting G → ∀ A : Subgroup G, IsStandardSubgroup A →
    Blueprint.NativeSporadic.IsSporadic (↥A ⧸ center ↥A) .Suz → Odd (Nat.card (center ↥A)) →
      False

private theorem isSporadic_center_of_fusionZStar {J : Type} [Group J]
    (hperf : commutator J = ⊤) (hO : pPrimeCore 2 J ≤ center J)
    (hτ : Blueprint.NativeSporadic.IsSporadic (J ⧸ Open.fusionZStar J) .Suz) :
    Blueprint.NativeSporadic.IsSporadic (J ⧸ center J) .Suz := by
  have heq := GrS5.fusionZStar_eq_center_of_le hperf hO
  obtain ⟨e⟩ := hτ
  exact ⟨(QuotientGroup.quotientMulEquivOfEq heq.symm).trans e⟩

theorem l34SuzStandardExclusion_of_even_odd (hE : L34SuzEvenStandardExclusion)
    (hO : L34SuzOddStandardExclusion) : L34SuzStandardExclusion := by
  intro G _ _ hG b J _ hJb hJp hτ hst hodd
  have hq : IsQuasisimple J := hst.1
  have hO' : pPrimeCore 2 ↥J ≤ center ↥J := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hodd ⟨x, hx, rfl⟩
    rwa [← Subtype.ext hyx]
  have hτ' : Blueprint.NativeSporadic.IsSporadic (↥J ⧸ center ↥J) .Suz :=
    isSporadic_center_of_fusionZStar hq.1.commutator_eq_top hO' hτ
  rcases Nat.even_or_odd (Nat.card (center ↥J)) with he | ho
  · exact hE G hG J hst hτ' he
  · exact hO G hG J hst hτ' ho

end CFSG.ComponentClassification.GrSLit.L34Sec5S
