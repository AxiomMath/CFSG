module

public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
public import CFSG.LocalAnalysis.SectionRank.Exceptional
public import CFSG.LieType.Ree.SmallReeRank

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.BorelTits

theorem smallReeModel_rank
    {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : ReeTitsModel S .twistedG2 p f) : p = 3 ∧ 3 ≤ f ∧ 2 * f ≤ pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨hadm, a, hf, hmodel⟩ := h
  obtain ⟨-, -, -, hp, -, h3⟩ := hadm
  subst hp hf
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 3 := charP_of_natCard_eq_pow hK
  have : CharP K ReeTag.G2.prime := ‹CharP K 3›
  have ha : 1 ≤ a := by omega
  have := Finite.of_equiv _ e.toEquiv
  obtain ⟨T, hT⟩ := exists_sylow_reeFixed .G2 K a
  have hTle : (T : Subgroup (reeFixed .G2 K a)) ≤ commutator (reeFixed .G2 K a) := by
    intro x hx
    rw [hT] at hx
    obtain ⟨y, hy, hyx⟩ := reeFixed_U_le_derived .G2 K a ha hK x hx x.2
    rwa [Subtype.ext hyx] at hy
  refine ⟨rfl, h3, ?_⟩
  rw [(pRank_top_eq_of_mulEquiv (by norm_num) e).trans
    (pRank_derivedCentralQuotient_eq (p := 3) _
      ((MulEquiv.subgroupCongr (reeFixedGroup_eq_map_reeFixed .G2 K a)).trans
        ((reeFixed .G2 K a).equivMapOfInjective _ Subtype.val_injective).symm)
      (holds_reeFixed .G2 K a) T hTle)]
  exact two_mul_le_pRank_commutator_reeFixed_G2 ha hK

theorem smallRee_central_cover_rank_exclusion
    {G : Type} [Group G] [Finite G] (A : Subgroup G)
    [A.Normal] (hAZ : A ≤ Subgroup.center G) {p f : ℕ}
    (h : ReeTitsModel (G ⧸ A) .twistedG2 p f) :
    p = 3 ∧ (∃ E : Subgroup (G ⧸ A), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ (2 * f)) ∧
      ¬ ∀ r : ℕ, r.Prime → r ≠ 2 → pRank r (⊤ : Subgroup G) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hp, h3, hrank⟩ := smallReeModel_rank h
  refine ⟨hp, ?_, fun hSQT => ?_⟩
  · obtain ⟨E, -, hE, hcard⟩ := exists_isElemAbelian_card_of_le_pRank hrank
    exact ⟨E, hE, hcard⟩
  · have h1 := pRank_quotient_le_three (by norm_num) (hSQT 3 Nat.prime_three (by norm_num)) A hAZ
    omega

end CFSG.SectionRank
