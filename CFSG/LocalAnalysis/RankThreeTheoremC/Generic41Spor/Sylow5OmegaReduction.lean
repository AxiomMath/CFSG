module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.FiveDiagSylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5OmegaBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5Omega

open CFSG.Open
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint (LieModel)

@[expose] def DefCharCase : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n 5 f →
    LieModel K t n 5 f → ∀ S : Sylow 5 K, Nat.card S = 5 ^ 5 → IsMulCommutative (S : Subgroup K)

@[expose] def ClassicalCase : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (t : StatedLieTag) (n ℓ f : ℕ),
    StatedClassicalModel K t n ℓ f → ℓ ≠ 5 → ¬ FiveDiagType K →
      ∀ S : Sylow 5 K, Nat.card S = 5 ^ 5 → IsMulCommutative (S : Subgroup K)

@[expose] def ExceptionalCase : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (t : StatedLieTag) (ℓ f : ℕ),
    (t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .twistedE6 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨
      t = .twistedG2 ∨ t = .twistedF4 ∨ t = .Tits) →
    LieModel K t 0 ℓ f → ℓ ≠ 5 →
      ∀ S : Sylow 5 K, Nat.card S = 5 ^ 5 → IsMulCommutative (S : Subgroup K)

@[expose] def E8Case : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (ℓ f : ℕ), LieModel K .E8 0 ℓ f → ℓ ≠ 5 →
    ∀ S : Sylow 5 K, Nat.card S = 5 ^ 5 → ¬ IsMulCommutative (omega5 (S : Subgroup K))

theorem sylow5OmegaLie_of_cases (hDef : DefCharCase) (hCl : ClassicalCase)
    (hExc : ExceptionalCase) (hE8 : E8Case) : Sylow5OmegaLie := by
  intro K _ _ hs hnab hcat ⟨t, n, ℓ, f, hadm, hmodel⟩ S hS hΩ
  have hΩ' : IsMulCommutative (omega5 (S : Subgroup K)) := hΩ
  by_cases hℓ : ℓ = 5
  · subst hℓ
    exact hDef K t n f hadm hmodel S hS
  · by_cases hdiag : FiveDiagType K
    · rcases fiveDiagSylow K hs hnab hcat hdiag S with h6 | ⟨-, hexp⟩
      · rw [hS] at h6
        exact absurd h6 (by norm_num)
      · exact isMulCommutative_of_exponent_five hexp hΩ'
    · rcases hmodel with ⟨ht, hm⟩ | ⟨hn, ht, hm⟩ | ⟨hn, ht, hm⟩ | ⟨hn, ht, hm⟩
      · exact hCl K t n ℓ f hm hℓ hdiag S hS
      · subst hn
        have ht' : t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨
            t = .trialityD4 := by
          simpa [CFSG.Blueprint.chevalleyExceptionalTags] using ht
        by_cases h8 : t = .E8
        · subst h8
          exact absurd hΩ' (hE8 K ℓ f (Or.inr (Or.inl ⟨rfl, ht, hm⟩)) hℓ S hS)
        · refine hExc K t ℓ f ?_ (Or.inr (Or.inl ⟨rfl, ht, hm⟩)) hℓ S hS
          rcases ht' with h | h | h | h | h | h | h <;> first | exact absurd h h8 | simp [h]
      · subst hn
        have ht' : t = .twistedG2 ∨ t = .twistedF4 ∨ t = .Tits := by
          simpa [CFSG.Blueprint.reeTitsTags] using ht
        refine hExc K t ℓ f ?_ (Or.inr (Or.inr (Or.inl ⟨rfl, ht, hm⟩))) hℓ S hS
        rcases ht' with h | h | h <;> simp [h]
      · subst hn
        subst ht
        exact hExc K _ ℓ f (by simp) (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hm⟩))) hℓ S hS

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5Omega
