module

public import CFSG.LieType.ChevTwo.Defs
import CFSG.GH74.GLS.Stage2.OddAut.BTCanon

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open CFSG.GH74.GLS.Stage2.OddAut CFSG.LieType.BorelTits
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open CFSG.AGLEmbedding (IsClassicalTwoOrG2 IsClassicalOrG2Index)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped commutatorElement

theorem chev2KDOut_of_outTwoNilp (h : Chev2OutTwoNilp) : Chev2KDOut := by
  intro S _ _ hS hna hC p hp hp2 P T hP hT hPT
  obtain ⟨N, hNn, hIN, hodd, hpow⟩ := h S hS hna hC
  have hPN : ∀ x ∈ P, x ∈ N := by
    intro x hx
    obtain ⟨m, hm⟩ := hP ⟨x, hx⟩
    have hm' : x ^ p ^ m = 1 := by simpa using congrArg Subtype.val hm
    obtain ⟨k, hk⟩ := hpow x
    have hord : orderOf x ∣ p ^ m := orderOf_dvd_of_pow_eq_one hm'
    have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
      Nat.Coprime.coprime_dvd_right hord
        (Nat.Coprime.pow k m ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)))
    obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hu]
    exact N.pow_mem hk u
  rw [Subgroup.commutator_le]
  intro t ht x hx
  have hxN := hPN x hx
  have hcN : ⁅t, x⁆ ∈ N := by
    have h1 : t * x * t⁻¹ ∈ N := hNn.conj_mem x hxN t
    exact N.mul_mem h1 (N.inv_mem hxN)
  have hcT : ⁅t, x⁆ ∈ T := by
    have h1 := (Subgroup.mem_normalizer_iff.1 (hPT hx) t⁻¹).1 (T.inv_mem ht)
    have h2 : ⁅t, x⁆ = t * (x * t⁻¹ * x⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [h2]
    exact T.mul_mem ht h1
  obtain ⟨k, hk⟩ := hT ⟨_, hcT⟩
  have hyk : (⁅t, x⁆) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  let yq : N ⧸ (inner S).subgroupOf N := QuotientGroup.mk ⟨⁅t, x⁆, hcN⟩
  have h1 : yq ^ 2 ^ k = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨⁅t, x⁆, hcN⟩ : N) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hyk)
    rw [this]; rfl
  have h2 : orderOf yq ∣ Nat.card (N ⧸ (inner S).subgroupOf N) := orderOf_dvd_natCard yq
  have h3 : Nat.card (N ⧸ (inner S).subgroupOf N) = (inner S).relIndex N := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
  rw [h3] at h2
  have h4 : orderOf yq = 1 := by
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h1)
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simpa using hj'
    · exfalso
      have h2' : 2 ∣ (inner S).relIndex N := by
        refine dvd_trans ?_ h2
        rw [hj']
        exact dvd_pow_self 2 (by omega)
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2')
  have h5 : yq = 1 := orderOf_eq_one_iff.1 h4
  have h6 := (QuotientGroup.eq_one_iff _).1 h5
  exact Subgroup.mem_subgroupOf.1 h6

theorem chevIndexTwo_iff_of_valid (i : TauCeti.LieTypeIndex) (hv : i.Valid) :
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsChevIndexTwo i ↔
      IsClassicalOrG2Index i ∨ IsExcIndexTwo i := by
  cases i <;>
    simp_all [CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsChevIndexTwo,
      IsClassicalOrG2Index, IsExcIndexTwo, TauCeti.LieTypeIndex.valid_iff,
      TauCeti.LieTypeIndex.inStandardRange_iff]

theorem isChevTwo_iff {Y : Type} [Group Y] :
    IsChevTwo Y ↔ IsClassicalTwoOrG2 Y ∨ IsChevTwoExc Y := by
  constructor
  · rintro (⟨d, hd, e⟩ | h | h)
    · rcases (chevIndexTwo_iff_of_valid d.1 d.2).1 hd with h | h
      · exact Or.inl (Or.inl ⟨d, h, e⟩)
      · exact Or.inr ⟨d, h, e⟩
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr h))
  · rintro ((⟨d, hd, e⟩ | h | h) | ⟨d, hd, e⟩)
    · exact Or.inl ⟨d, (chevIndexTwo_iff_of_valid d.1 d.2).2 (Or.inl hd), e⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl ⟨d, (chevIndexTwo_iff_of_valid d.1 d.2).2 (Or.inr hd), e⟩

end CFSG.LieType.ChevTwo
