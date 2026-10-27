module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamilies

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem IsGamma0.of_isWitnessPair_of_twoPart_le (h : UniqueSetting G T M) {H K U : Subgroup G}
    (hH : IsGamma0 M H) (hp : IsWitnessPair M U K) (hle : twoPart H ≤ twoPart K) :
    twoPart K = twoPart H ∧ IsGamma0 M K ∧ (IsGamma2 M H → IsGamma2 M K) ∧
      (IsGammaU M H → IsGammaU M K) := by
  have hKΓ : IsGamma M K := hp.isGamma
  obtain ⟨S₁, hS₁⟩ := exists_isSylowTwoOf (K ⊓ M)
  obtain ⟨hS₁K, hS₁c, -⟩ := IsGamma.sylow_properties h hKΓ hS₁
  have hpair' : IsWitnessPair M S₁ K := ⟨hS₁c, hS₁K.le, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2⟩
  have hcard : Nat.card S₁ = twoPart K := hS₁K.card_eq
  have hcase2 : IsGamma2 M H → twoPart K = twoPart H ∧ IsGamma2 M K := by
    intro h2
    have h1 : twoPart K ≤ twoPart H := h2.2 K hKΓ
    have heq : twoPart K = twoPart H := le_antisymm h1 hle
    exact ⟨heq, hKΓ, fun K' hK' => (h2.2 K' hK').trans heq.ge⟩
  have hcaseU : IsGammaU M H → twoPart K = twoPart H ∧ IsGammaU M K := by
    intro hU
    obtain ⟨-, U₀, HU₀, hpair₀, hHU₀H, hmax₀⟩ := hU.1
    have hU₀H : Nat.card U₀ ≤ twoPart H :=
      CFSG.QuasithinUnique.card_le_twoPart (hpair₀.2.1.trans hHU₀H) hpair₀.1.2.2.1
    have h1 : Nat.card S₁ ≤ Nat.card U₀ := hmax₀ S₁ ⟨K, hpair'⟩
    have heqS : Nat.card S₁ = Nat.card U₀ := by
      refine le_antisymm h1 ?_
      calc Nat.card U₀ ≤ twoPart H := hU₀H
        _ ≤ twoPart K := hle
        _ = Nat.card S₁ := hcard.symm
    have heq : twoPart K = twoPart H := by
      refine le_antisymm ?_ hle
      calc twoPart K = Nat.card S₁ := hcard.symm
        _ ≤ Nat.card U₀ := h1
        _ ≤ twoPart H := hU₀H
    have htop : IsGammaTop M K :=
      ⟨hp.2.2.1, S₁, K, hpair', le_rfl, fun V hV => (hmax₀ V hV).trans heqS.ge⟩
    exact ⟨heq, htop, fun K' hK' => (hU.2 K' hK').trans heq.ge⟩
  rcases hH with hU | h2
  · obtain ⟨heq, hK⟩ := hcaseU hU
    exact ⟨heq, Or.inl hK, fun h2 => (hcase2 h2).2, fun hU' => (hcaseU hU').2⟩
  · obtain ⟨heq, hK⟩ := hcase2 h2
    exact ⟨heq, Or.inr hK, fun h2' => (hcase2 h2').2, fun hU => (hcaseU hU).2⟩

end CFSG.QuasithinUnique
