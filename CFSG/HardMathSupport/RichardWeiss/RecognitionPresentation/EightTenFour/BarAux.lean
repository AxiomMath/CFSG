module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.PreStep

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour

open CFSG CFSG.Open CFSG.AGLEmbedding
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry (mem_barM barM_mono)

variable {G : Type} [Group G]

theorem exists_minimal_subgroup [Finite G] (P : Subgroup G → Prop) (h : ∃ K, P K) :
    ∃ K, P K ∧ ∀ K', P K' → K' ≤ K → K' = K := by
  classical
  have hex : ∃ n, ∃ K, P K ∧ Nat.card K = n := by
    obtain ⟨K, hK⟩ := h
    exact ⟨_, K, hK, rfl⟩
  obtain ⟨K, hK, hKn⟩ := Nat.find_spec hex
  refine ⟨K, hK, fun K' hK' hle => ?_⟩
  have h1 : Nat.card K ≤ Nat.card K' := by
    rw [hKn]
    exact Nat.find_min' hex ⟨K', hK', rfl⟩
  exact (Subgroup.eq_of_le_of_card_ge hle h1)

theorem commutator_le_of_le {M A B : Subgroup G} (hA : A ≤ M) (hB : B ≤ M) : ⁅A, B⁆ ≤ M := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact M.mul_mem (M.mul_mem (M.mul_mem (hA ha) (hB hb)) (M.inv_mem (hA ha))) (M.inv_mem (hB hb))

theorem barM_commutator {M A B : Subgroup G} (hA : A ≤ M) (hB : B ≤ M) :
    barM M ⁅A, B⁆ = ⁅barM M A, barM M B⁆ := by
  have h : (⁅A, B⁆.subgroupOf M) = ⁅A.subgroupOf M, B.subgroupOf M⁆ := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
      Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le (commutator_le_of_le hA hB)]
  unfold barM
  rw [h, Subgroup.map_commutator]

theorem barM_sup_pCoreOf {M K : Subgroup G} (hKQ : K ≤ Subgroup.normalizer (pCoreOf 2 M : Set G)) :
    barM M (K ⊔ pCoreOf 2 M) = barM M K := by
  apply le_antisymm
  · intro x hx
    obtain ⟨m, hm, rfl⟩ := (mem_barM x).1 hx
    have : (m : G) ∈ ((K ⊔ pCoreOf 2 M : Subgroup G) : Set G) := hm
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K (pCoreOf 2 M) hKQ] at this
    obtain ⟨k, hk, q, hq, hkq⟩ := this
    have hqM : q ∈ M := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M hq
    have hkM : k ∈ M := by
      have : k = (m : G) * q⁻¹ := by rw [← hkq]; group
      rw [this]; exact M.mul_mem m.2 (M.inv_mem hqM)
    refine (mem_barM _).2 ⟨⟨k, hkM⟩, hk, ?_⟩
    have e : m = ⟨k, hkM⟩ * ⟨q, hqM⟩ := Subtype.ext hkq.symm
    have h1 : (QuotientGroup.mk (⟨q, hqM⟩ : ↥M) : ↥M ⧸ CFSG.pCore 2 ↥M) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (mem_pCore_of_coe_mem hq)
    rw [e, QuotientGroup.mk_mul, h1, mul_one]
  · exact barM_mono le_sup_left

theorem mk_mem_normalizer_barM {M S : Subgroup G} (n : ↥M)
    (hn : (n : G) ∈ Subgroup.normalizer (S : Set G)) :
    (QuotientGroup.mk n : ↥M ⧸ CFSG.pCore 2 ↥M) ∈
      Subgroup.normalizer ((barM M S : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _) := by
  have key : ∀ n' : ↥M, (n' : G) ∈ Subgroup.normalizer (S : Set G) → ∀ c ∈ barM M S,
      (QuotientGroup.mk n' : ↥M ⧸ CFSG.pCore 2 ↥M) * c * (QuotientGroup.mk n')⁻¹ ∈ barM M S := by
    intro n' hn' c hc
    obtain ⟨⟨s', hs'M⟩, hs', rfl⟩ := (mem_barM c).1 hc
    refine (mem_barM _).2 ⟨n' * ⟨s', hs'M⟩ * n'⁻¹, ?_, by simp⟩
    exact (Subgroup.mem_normalizer_iff.mp hn' s').mp hs'
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => key n hn c hc, fun hc => ?_⟩
  have hn' : ((n⁻¹ : ↥M) : G) ∈ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.coe_inv]; exact Subgroup.inv_mem _ hn
  have := key n⁻¹ hn' _ hc
  simpa [mul_assoc] using this

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour
