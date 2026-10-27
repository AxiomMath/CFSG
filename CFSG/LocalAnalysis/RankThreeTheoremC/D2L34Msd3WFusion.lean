module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WEscape
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Lift

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

section Same

variable {G : Type} [Group G] [Finite G] [D2Amb3 G]

theorem false_of_same_side_pair3_of_good {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hR9 : Nat.card R = 9)
    (hrk : D2NormRankTwo G M) (hOnly : D2OnlyL34At P M) {N : Subgroup G} (hN : IsTwoLocal N)
    (hNM : ¬ N ≤ M)
    {V : Subgroup G} (hU : IsElemAbelian 2 V) (hMN : M ≤ Subgroup.normalizer (V : Set G))
    {I : Finset (Subgroup (MulAut (IntMod V hU)))} (hI : S3Family I)
    {L₁ L₂ : Subgroup (MulAut (IntMod V hU))} (h₁ : L₁ ∈ I) (h₂ : L₂ ∈ I) (hne : L₁ ≠ L₂)
    {x₁ x₂ : G} (hx₁M : x₁ ∈ M) (hx₂M : x₂ ∈ M) (hx₁N : x₁ ∈ N) (hx₂N : x₂ ∈ N)
    (hcomm : x₁ * x₂ = x₂ * x₁) (ho₁ : x₁ ^ 3 = 1) (ho₂ : x₂ ^ 3 = 1)
    (hL₁ : actM hU hMN ⟨x₁, hx₁M⟩ ∈ L₁) (hL₂ : actM hU hMN ⟨x₂, hx₂M⟩ ∈ L₂)
    (h₁1 : actM hU hMN ⟨x₁, hx₁M⟩ ≠ 1) (h₂1 : actM hU hMN ⟨x₂, hx₂M⟩ ≠ 1)
    (hgood : HasGoodE9 M (Subgroup.closure {x₁, x₂})) : False :=
  false_of_same_side_pair3_of_conj hU hMN hI h₁ h₂ hne hx₁M hx₂M hx₁N hx₂N hcomm ho₁ ho₂ hL₁ hL₂
    h₁1 h₂1 fun X hX hXN hXM hXp hXc => by
      subst hX
      exact D2L34BetaConf3.exists_conj_eq_of_good hc hR9 hrk hOnly hN hNM hXN hXM hXp hXc hgood

end Same

section Two

variable {G : Type} [Group G] [Finite G] [D2Amb3 G] {V M : Subgroup G} {hU : IsElemAbelian 2 V}
  {hMN : M ≤ Subgroup.normalizer (V : Set G)}

theorem false_of_two_factors_in_normalizer3_of_good {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K₀) (hR9 : Nat.card R = 9)
    (hrk : D2NormRankTwo G M) (hOnly : D2OnlyL34At P M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) {X : Subgroup G}
    (hX1 : X ≠ ⊥) (hXp : IsPGroup 2 X)
    (hNX : ¬ Subgroup.normalizer (X : Set G) ≤ M) {K : Subgroup G} (hKM : K ≤ M)
    (hKN : K ≤ Subgroup.normalizer (X : Set G))
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M))
    {I : Finset (Subgroup (MulAut (IntMod V hU)))} (hI : S3Family I)
    (hcard : ∀ L ∈ I, Nat.card L = 6) {L₁ L₂ : Subgroup (MulAut (IntMod V hU))} (h₁ : L₁ ∈ I)
    (h₂ : L₂ ∈ I) (hne : L₁ ≠ L₂) (hL₁ : L₁ ≤ autI hU K) (hL₂ : L₂ ≤ autI hU K)
    (hgood : ∀ x₁ x₂ : G, x₁ ∈ K → x₂ ∈ K → x₁ * x₂ = x₂ * x₁ → x₁ ^ 3 = 1 → x₂ ^ 3 = 1 →
      ∀ (hx₁M : x₁ ∈ M) (hx₂M : x₂ ∈ M), actM hU hMN ⟨x₁, hx₁M⟩ ∈ L₁ →
        actM hU hMN ⟨x₂, hx₂M⟩ ∈ L₂ → actM hU hMN ⟨x₁, hx₁M⟩ ≠ 1 → actM hU hMN ⟨x₂, hx₂M⟩ ≠ 1 →
        HasGoodE9 M (Subgroup.closure {x₁, x₂})) : False := by
  have hN : IsTwoLocal (Subgroup.normalizer (X : Set G)) := ⟨X, hX1, hXp, rfl⟩
  exact false_of_two_factors_of_pair hMN hKM hC3 hI hcard h₁ h₂ hne hL₁ hL₂
    fun x₁ x₂ hx₁ hx₂ hcomm hx₁3 hx₂3 hx₁M hx₂M he₁ he₂ hn₁ hn₂ =>
      false_of_same_side_pair3_of_good hc hR9 hrk hOnly hN hNX hU hMN hI h₁ h₂ hne hx₁M hx₂M
        (hKN hx₁) (hKN hx₂) hcomm hx₁3 hx₂3 he₁ he₂ hn₁ hn₂
        (hgood x₁ x₂ hx₁ hx₂ hcomm hx₁3 hx₂3 hx₁M hx₂M he₁ he₂ hn₁ hn₂)

end Two

end CFSG.LocalAnalysis.RankThreeTheoremC
