module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SolvableLinearCosetNormalizerCyclic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SolvableLinearCosetNormalizerSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SolvableLinearCosetNormalizerQuotient

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open scoped Pointwise MatrixGroups

variable {G : Type*} [Group G]

theorem cyclic_sylow_quotient_of_translation_complement [Finite G]
    {N Q V A D L M : Subgroup G} {u : G} {f : ℕ}
    (hNcard : Nat.card N = 2 ^ (2 * f) * Nat.card A)
    (hlift : ∀ S : Sylow 2 N, ∃ S' : Sylow 2 G,
      (S' : Subgroup G) = (S : Subgroup N).map N.subtype)
    (hQN : Q ≤ N) (hAN : A ≤ N) (hVQ : V ≤ Q) (hVcard : Nat.card V = 2 ^ (2 * f))
    (hNV : N ≤ Subgroup.normalizer (V : Set G)) (hNQ : N ≤ Subgroup.normalizer (Q : Set G))
    (huV : u ∉ V) (hQA : Q ⊓ A = Subgroup.zpowers u) (hu : orderOf u = 2)
    (hQV : Subgroup.zpowers u ⊔ V = Q)
    (hLM : L ≤ M) (hLn : (L.subgroupOf M).Normal) {F : Type*} [Field F] {e : ℕ} (he : 1 ≤ e)
    (hF : Nat.card F = 2 ^ e) (eL : L ≃* SL(2, F))
    (hK : M ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.zpowers u)
    (hAM : A ≤ M) (hAu : A ≤ Subgroup.centralizer ({u} : Set G)) (hAD : A ≤ D)
    (hrank : CFSG.Open.twoRank D ≤ 1)
    (hLA : ∀ X : Subgroup G, X ≤ L ⊓ A → IsPGroup 2 X → X = ⊥) (P : Sylow 2 A) :
    IsCyclic ((P : Subgroup A).map A.subtype) ∧ u ∈ (P : Subgroup A).map A.subtype ∧
      ∃ S : Sylow 2 G,
        (S : Set G) = (Q : Set G) * ((P : Subgroup A).map A.subtype : Set G) ∧
        (S : Set G) = (V : Set G) * ((P : Subgroup A).map A.subtype : Set G) ∧
        V ⊓ (P : Subgroup A).map A.subtype = ⊥ ∧
        ∃ _ : (V.subgroupOf (S : Subgroup G)).Normal,
          Nonempty (↥(S : Subgroup G) ⧸ V.subgroupOf (S : Subgroup G) ≃*
            (P : Subgroup A).map A.subtype) := by
  set P' := (P : Subgroup A).map A.subtype with hP'
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
  have huA : u ∈ A := by
    have h1 : u ∈ Q ⊓ A := hQA ▸ Subgroup.mem_zpowers u
    exact h1.2
  have hPA : P' ≤ A := Subgroup.map_subtype_le _
  have hP2 : IsPGroup 2 P' := P.isPGroup'.map A.subtype
  have huP : u ∈ P' := mem_sylow_of_central_involution huA hAu hu P
  have hcyc : IsCyclic P' :=
    isCyclic_of_sl2_hull_action hLM hLn he hF eL hK (hPA.trans hAM) (hPA.trans hAu) huP
      (hLA _ (inf_le_inf_left L hPA) (hP2.to_le inf_le_right)) hP2 (hPA.trans hAD) hrank
  have hPV : P' ≤ Subgroup.normalizer (V : Set G) := (hPA.trans hAN).trans hNV
  have hVP : V ⊓ P' = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxV, hxP⟩
    have hx : x ∈ Q ⊓ A := ⟨hVQ hxV, hPA hxP⟩
    rw [hQA] at hx
    rcases eq_one_or_eq_of_mem_zpowers hu2 hx with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hxV huV
  obtain ⟨hSset, hScard, hVn, ⟨eSV⟩⟩ := sup_of_le_normalizer_of_inf_eq_bot hPV hVP
  have hSN : V ⊔ P' ≤ N := sup_le (hVQ.trans hQN) (hPA.trans hAN)
  have hP'card : Nat.card P' = 2 ^ (Nat.card A).factorization 2 := by
    rw [hP', Subgroup.card_map_of_injective A.subtype_injective]
    exact Sylow.card_eq_multiplicity P
  have hcard : Nat.card (V ⊔ P' : Subgroup G) = 2 ^ (Nat.card N).factorization 2 := by
    rw [hScard, hVcard, hNcard, hP'card, Nat.factorization_mul (by positivity) Nat.card_pos.ne',
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      pow_add]
  obtain ⟨S', hS'⟩ := exists_sylow_of_le_of_card_eq hlift hSN hcard
  have hQP : Q ⊔ P' = V ⊔ P' := by
    rw [← hQV]
    apply le_antisymm
    · exact sup_le (sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right huP)) le_sup_left)
        le_sup_right
    · exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hPQ : P' ≤ Subgroup.normalizer (Q : Set G) := (hPA.trans hAN).trans hNQ
  refine ⟨hcyc, huP, S', ?_, ?_, hVP, ?_⟩
  · show ((S' : Subgroup G) : Set G) = _
    rw [hS', ← hQP, Subgroup.coe_mul_of_right_le_normalizer_left Q P' hPQ]
  · show ((S' : Subgroup G) : Set G) = _
    rw [hS', hSset]
  · rw [hS']
    exact ⟨hVn, ⟨eSV⟩⟩

end CFSG.ProperTwoGeneratedCore.HighRankPair
