module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Local.RegularTauOneSylowBetaFixedPoints
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerEmbeddingSylows
import CFSG.FeitThompson.Foundations.PGroupNontrivialCenter

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson CFSG.FeitThompson
  Pointwise

universe u

variable {G : Type u} [Group G] {q : ℕ}

theorem ne_bot_of_normalizer_le_of_isCoatom {L Q : Subgroup G} (hL : IsCoatom L)
    (hNQL : normalizer (Q : Set G) ≤ L) : Q ≠ ⊥ := by
  intro hbot
  refine hL.1 (top_le_iff.1 ?_)
  rw [← Subgroup.normalizer_eq_top (H := (⊥ : Subgroup G))]
  exact hbot ▸ hNQL

theorem isSylowSubgroupOf_of_inf_of_normalizer_le [Finite G] (hq : q.Prime) {M L Q : Subgroup G}
    (hQ : IsSylowSubgroupOf q Q (M ⊓ L)) (hNQL : normalizer (Q : Set G) ≤ L) :
    IsSylowSubgroupOf q Q M := by
  have hQpg : IsPGroup q ↥Q := IsPGroup.of_card hQ.2
  obtain ⟨T, hQT, hT⟩ := exists_isSylowSubgroupOf_ge hq (hQ.1.trans inf_le_left) hQpg
  have hTpg : IsPGroup q ↥T := IsPGroup.of_card hT.2
  have hinf : T ⊓ normalizer (Q : Set G) = Q :=
    eq_of_isSylowSubgroupOf_of_isPGroup hq hQ (le_inf hQT Subgroup.le_normalizer)
      (le_inf (inf_le_left.trans hT.1) (inf_le_right.trans hNQL)) (hTpg.to_le inf_le_left)
  have hTQ : T = Q := eq_of_inf_normalizer_le hq hQT hTpg hinf.le
  exact ⟨hTQ ▸ hT.1, hTQ ▸ hT.2⟩

theorem eq_bot_of_isPGroup_of_le_normalizer_of_inf_centralizer_eq_bot [Finite G] (hq : q.Prime)
    {P Q K : Subgroup G} (hQ : IsSylowSubgroupOf q Q K) (hPK : P ≤ K) (hPq : IsPGroup q ↥P)
    (hPnormQ : P ≤ normalizer (Q : Set G)) (hfix : Q ⊓ centralizer (P : Set G) = ⊥) : Q = ⊥ := by
  by_contra hQbot
  have hQpg : IsPGroup q ↥Q := IsPGroup.of_card hQ.2
  have hsup : IsPGroup q ↥(Q ⊔ P : Subgroup G) := hQpg.to_sup_of_normal_left' hPq hPnormQ
  have heq : (Q ⊔ P : Subgroup G) = Q :=
    eq_of_isSylowSubgroupOf_of_isPGroup hq hQ le_sup_left (sup_le hQ.1 hPK) hsup
  have hPQ : P ≤ Q := le_sup_right.trans heq.le
  have hcenter : (Subgroup.center ↥Q).map Q.subtype ≤ Q ⊓ centralizer (P : Set G) := by
    rintro x ⟨y, hy, rfl⟩
    refine ⟨y.2, mem_centralizer_iff.2 fun z hz => ?_⟩
    exact congrArg (Subgroup.subtype Q) ((Subgroup.mem_center_iff.1 hy) ⟨z, hPQ hz⟩)
  rw [hfix, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ Q.subtype_injective] at hcenter
  have ha : 1 ≤ (Nat.card ↥K).factorization q := by
    rcases Nat.eq_zero_or_pos ((Nat.card ↥K).factorization q) with h | h
    · exact absurd (Subgroup.card_eq_one.1 (by rw [hQ.2, h, pow_zero])) hQbot
    · exact h
  exact center_ne_bot hq hQ.2 ha hcenter

theorem ne_singleton_of_isCoatom_of_normalizer_le {M L Q : Subgroup G} (hL : IsCoatom L)
    (hnc : ∀ g : G, L ≠ conjSubgroup M g) (hNQL : normalizer (Q : Set G) ≤ L) :
    {T : Subgroup G | IsCoatom T ∧ normalizer (Q : Set G) ≤ T} ≠ {M} := by
  intro h
  have hmem : L ∈ {T : Subgroup G | IsCoatom T ∧ normalizer (Q : Set G) ≤ T} := ⟨hL, hNQL⟩
  rw [h, Set.mem_singleton_iff] at hmem
  exact hnc 1 (by rw [hmem, conjSubgroup_one])

theorem FBG_tau_one_intersection_regular_sylow
    (h₁ : Statements.FTS_beta_prime_centralizing_sylow.{u}) :
    Statements.FBG_tau_one_intersection_regular_sylow.{u} := by
  intro G _ _ hG M L hM hL hnc p hp hptau P hPML hPcard q hq Q hQ hPnormQ hfix hNQL
  have hQbot : Q ≠ ⊥ := ne_bot_of_normalizer_le_of_isCoatom hL hNQL
  have hQM : IsSylowSubgroupOf q Q M := isSylowSubgroupOf_of_inf_of_normalizer_le hq hQ hNQL
  have hqp : q ≠ p := by
    rintro rfl
    exact hQbot (eq_bot_of_isPGroup_of_le_normalizer_of_inf_centralizer_eq_bot hq hQ hPML
      (IsPGroup.of_card (n := 1) (by rw [hPcard, pow_one])) hPnormQ hfix)
  have hnotuniq := ne_singleton_of_isCoatom_of_normalizer_le (M := M) hL hnc hNQL
  obtain ⟨hαβ, -, -, hqβ, hfix₁, hfix₂⟩ :=
    FBG_regular_tau_one_sylow_beta_fixed_points h₁ G hG M hM p q (fun h => hqp h.symm) hp hq
      hptau P (hPML.trans inf_le_left) hPcard Q hQM hQbot hPnormQ hfix hnotuniq
  exact ⟨hQbot, hQM, hqp, hqβ, hαβ, hfix₁, hfix₂⟩

end

end CFSG.FeitThompson.Proofs
