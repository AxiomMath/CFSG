module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Equiv

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

section Pick

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_normalizer_pPrimeCoreOf_of_mem {K : Subgroup X} {k : X} (hk : k ∈ K) :
    k ∈ normalizer (pPrimeCoreOf 2 K : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ k : X, k ∈ K → ∀ p : X, p ∈ pPrimeCoreOf 2 K → k * p * k⁻¹ ∈ pPrimeCoreOf 2 K := by
    intro k hk p ⟨w, hw, hwp⟩
    refine ⟨⟨k, hk⟩ * w * ⟨k, hk⟩⁻¹, (inferInstance : (pPrimeCore 2 ↥K).Normal).conj_mem w hw _, ?_⟩
    rw [← hwp]
    rfl
  intro p
  refine ⟨fun hp => key k hk p hp, fun hp => ?_⟩
  have := key k⁻¹ (K.inv_mem hk) _ hp
  simpa [mul_assoc] using this

omit [Finite X] in
theorem mem_zStar_of_mem_of_le_centralizer {K : Subgroup X} {t : X} (htK : t ∈ K)
    (hKt : K ≤ centralizer ({t} : Set X)) : t ∈ zStar K := by
  refine ⟨htK, Subgroup.le_normalizer htK, mem_normalizer_pPrimeCoreOf_of_mem htK, fun k hk => ?_⟩
  have h1 : k * t = t * k := Subgroup.mem_centralizer_singleton_iff.1 (hKt hk)
  have : ⁅k, t⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h1
  rw [this]
  exact (pPrimeCoreOf 2 K).one_mem

omit [Finite X] in
theorem IsSec5Pair.le_centralizer {n : ℕ} {z : X} {Z : Subgroup X} (h : IsSec5Pair X n z Z) :
    Z ≤ centralizer ({z} : Set X) :=
  (h.sylow.1.trans inf_le_left).trans (K0_le n _)

theorem exists_isSec5Pair {t : X} {L : Subgroup X} {n : ℕ} (ht : orderOf t = 2)
    (hL : IsAhatIntr X t L) (hn : IsDoubleCoverOfAlt (L ⧸ pPrimeCore 2 L) n) :
    ∃ Z : Subgroup X, IsSec5Pair X n t Z := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := K0 X n (centralizer ({t} : Set X)) with hK
  have hLK : L ≤ K := le_sSup ⟨⟨t, hL.isIntrinsicIn ht⟩, hn⟩
  have htK : t ∈ K := hLK hL.2.1
  have htA : t ∈ zStar K := mem_zStar_of_mem_of_le_centralizer htK (K0_le n _)
  set A := zStar K with hA
  let tA : ↥A := ⟨t, htA⟩
  have htA2 : orderOf tA = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  have hp : IsPGroup 2 ↥(Subgroup.zpowers tA) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, htA2, pow_one]
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  refine ⟨(Q : Subgroup ↥A).map A.subtype, ⟨ht, ?_, ?_⟩⟩
  · exact ⟨tA, hQ (Subgroup.mem_zpowers tA), rfl⟩
  · refine ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map A.subtype, ?_⟩
    show ¬ 2 ∣ (((Q : Subgroup ↥A).map A.subtype).comap A.subtype).index
    rw [Subgroup.comap_map_eq_self_of_injective A.subtype_injective]
    exact Q.not_dvd_index

end Pick

end CFSG.OddStandard.Solomon75
