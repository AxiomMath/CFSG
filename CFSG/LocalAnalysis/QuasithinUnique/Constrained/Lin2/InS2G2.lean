module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2G1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2F6

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

namespace S2Ok

variable {D₁ D₂ : Subgroup G} (O : S2Ok T M H S L D n t M₀ x₀ q W D₁ D₂)
include O

theorem M₀_eq_T (hle : T ⊓ Subgroup.normalizer (thompsonJ S : Set G) ≤ M₀) : M₀ = T := by
  have hB := O.base
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  obtain ⟨y, hy, hyM⟩ := exists_mem_inf_normalizer_of_ne (p := 2) hB.T_isPGroup hB.hMT hne
  apply hyM
  apply hle
  refine ⟨hy.1, ?_⟩
  have h1 := GammaExtra.normalizer_le_normalizer_thompsonJ M₀ hy.2
  rwa [O.thompsonJ_M₀] at h1

theorem X_le_normalizer_R₁ :
    conjR L t ⊔ s2S₁ M₀ S L ≤ Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G) :=
  sup_le O.L₂_le_normalizer_R₁ S₁_le_normalizer_R₁

theorem R₁_le_X : thompsonJ S ⊓ L ≤ conjR L t ⊔ s2S₁ M₀ S L :=
  R₁_le_R1.trans (O.base.R1_le_S₁.trans le_sup_right)

theorem isGamma_X : IsGamma M (conjR L t ⊔ s2S₁ M₀ S L) :=
  O.witnessPair₀.isGamma_of_le (sup_le_sup_left O.base.R1_le_S₁ _)
    (O.pCore_ne_bot_of O.X_le_normalizer_R₁ O.R₁_le_X)

theorem X_gamma2 (hT : M₀ = T) :
    twoPart (conjR L t ⊔ s2S₁ M₀ S L) = Nat.card S ∧ IsGamma2 M (conjR L t ⊔ s2S₁ M₀ S L) := by
  have hB := O.base
  have hcard : Nat.card T = 2 * Nat.card S := by
    rw [← hT]
    exact GammaExtra.card_eq_two_mul_of_relIndex_eq_two hB.hSM hB.h2
  have h1 := hB.cs.gamma0.isGamma2_of_card_eq_two_mul hB.cs.setting hB.cs.sylow_inf hcard
  have hS₁ : Nat.card S ≤ twoPart (conjR L t ⊔ s2S₁ M₀ S L) := by
    rw [← hB.card_S₁ O.hT₁ O.hT₂ O.hD O.hC O.hDx]
    exact card_le_twoPart le_sup_right hB.S₁_isPGroup
  exact h1.2 _ O.isGamma_X hS₁

theorem S₁_sylow_X (hT : M₀ = T) :
    IsSylowTwoOf (s2S₁ M₀ S L) (conjR L t ⊔ s2S₁ M₀ S L) :=
  isSylowTwoOf_of_card_eq le_sup_right O.base.S₁_isPGroup
    (by rw [O.base.card_S₁ O.hT₁ O.hT₂ O.hD O.hC O.hDx, (O.X_gamma2 hT).1])

theorem S₁_le_M : s2S₁ M₀ S L ≤ M := O.base.S₁_le_T.trans O.base.cs.setting.le

theorem S₁_sylow_X_inf_M (hT : M₀ = T) :
    IsSylowTwoOf (s2S₁ M₀ S L) ((conjR L t ⊔ s2S₁ M₀ S L) ⊓ M) := by
  have hB := O.base
  refine isSylowTwoOf_of_card_eq (le_inf le_sup_right O.S₁_le_M) hB.S₁_isPGroup ?_
  apply le_antisymm
  · exact card_le_twoPart (le_inf le_sup_right O.S₁_le_M) hB.S₁_isPGroup
  · calc twoPart ((conjR L t ⊔ s2S₁ M₀ S L) ⊓ M) ≤ twoPart (conjR L t ⊔ s2S₁ M₀ S L) :=
          twoPart_mono inf_le_left
      _ = Nat.card S := (O.X_gamma2 hT).1
      _ = Nat.card (s2S₁ M₀ S L) := (hB.card_S₁ O.hT₁ O.hT₂ O.hD O.hC O.hDx).symm

theorem isGamma0_X (hT : M₀ = T) : IsGamma0 M (conjR L t ⊔ s2S₁ M₀ S L) :=
  Or.inr (O.X_gamma2 hT).2

end S2Ok

end CFSG.QuasithinUnique.Lin2
