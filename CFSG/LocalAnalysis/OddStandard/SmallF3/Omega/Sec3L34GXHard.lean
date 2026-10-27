module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXC6Core
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXOne

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

@[expose] def Asc82CoreKGAHard : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], L34GStarQuotient Y → ¬ L34GC6 Y →
    ∀ (y : Y) (B : Subgroup Y), orderOf y = 2 → Sl23PocketIn ⊤ y B →
    ∀ σ : MulAut Y, σ * σ = 1 → σ ≠ 1 → (∀ b ∈ B, σ b = b) → σ ≠ MulAut.conj y →
      ∃ J : Subgroup Y, IsComponentIn J (L34GFix σ) ∧ InFStar J ∧ B ≤ J

@[expose] def Asc82CoreKGBHard : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], L34GStarQuotient Y → ¬ L34GC6 Y →
    ∀ σ : MulAut Y, σ * σ = 1 → σ ≠ 1 → ∀ J : Subgroup Y, IsComponentIn J (L34GFix σ) →
      ∀ b ∈ J, IsI4PlusIn J b → IsI4PlusIn ⊤ b

theorem l34g_coreKG_of_hard (hA : Asc82CoreKGAHard) (hB : Asc82CoreKGBHard) :
    Asc82CoreKGA ∧ Asc82CoreKGB := by
  refine ⟨?_, ?_⟩
  · intro Y _ _ hY y B hy hBp σ hσ hfix hne
    by_cases h1 : σ = 1
    · subst h1
      exact l34g_coreKGA_one hY B
    · by_cases hC : L34GC6 Y
      · exact absurd (l34g_kgA_of_c6 hC hy hBp hσ hfix) (by rintro (h | h) <;> contradiction)
      · exact hA Y hY hC y B hy hBp σ hσ h1 hfix hne
  · intro Y _ _ hY σ hσ J hJ b hb hI
    by_cases h1 : σ = 1
    · subst h1
      exact l34g_coreKGB_one hY hJ hb hI
    · by_cases hC : L34GC6 Y
      · exact l34g_kgB_of_c6 hC hσ h1 hJ hb hI
      · exact hB Y hY hC σ hσ h1 J hJ b hb hI

end CFSG.OddStandard.SmallF3.Omega
