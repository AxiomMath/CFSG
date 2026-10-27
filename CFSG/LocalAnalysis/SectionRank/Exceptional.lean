module

public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.LieType.Chevalley.RootWitness
public import CFSG.Blueprint.Catalog
public import CFSG.LieType.BorelTits.TitsClause

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.BorelTits

theorem charP_of_natCard_eq_pow {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    (h : Nat.card K = p ^ f) : CharP K p := by
  have := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, h])

theorem four_mul_le_pRank_adjointQuotient
    {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K] {p f : ℕ}
    [hp : Fact p.Prime] (hK : Nat.card K = p ^ f) :
    4 * f ≤ pRank p (⊤ : Subgroup (AdjointQuotient τ K)) := by
  have : CharP K p := charP_of_natCard_eq_pow hK
  have hc := Holds.coprime_card_center (holds_adjointGroup_tag τ K p)
  rw [pRank_quotient_eq _ fun h => by
    have := Nat.Coprime.coprime_dvd_left h hc
    exact hp.out.one_lt.ne' ((Nat.coprime_self p).1 this)]
  exact four_mul_le_pRank hτ hK

theorem not_mulEquiv_adjointQuotient
    {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hG : pRank p (⊤ : Subgroup G) ≤ 2) (A : Subgroup G) [A.Normal]
    (hAZ : A ≤ Subgroup.center G) {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (e : G ⧸ A ≃* AdjointQuotient τ K) : False := by
  have h1 := pRank_quotient_le_three hp2 hG A hAZ
  rw [pRank_top_eq_of_mulEquiv hp.out.one_lt e] at h1
  have h2 := four_mul_le_pRank_adjointQuotient hτ hK
  omega

end CFSG.SectionRank
