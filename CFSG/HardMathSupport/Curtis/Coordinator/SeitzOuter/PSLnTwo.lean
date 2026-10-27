module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.PSLnFinal
public import CFSG.LieType.SeitzGeneration.OuterLinearTwo

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThree.PartOne.CTP

theorem not_exists_plane_psl2 {F : Type} [Field F] [Finite F] {ℓ f : ℕ} [Fact ℓ.Prime]
    (hF : Nat.card F = ℓ ^ f) (h7 : 7 ≤ Nat.card F) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) (A : Subgroup (CFSG.GorensteinWalter.PSL2 F)) (hA : IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) : False := by
  have hcop : Nat.Coprime p (Nat.card F) := by
    rw [hF]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Fact.out Fact.out).mpr hpℓ)
  have hAp : IsPGroup p A := fun g => by
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hA.2 g g.2
  obtain ⟨P, hP⟩ := hAp.exists_le_sylow
  have hcyc : IsCyclic (P : Subgroup (CFSG.GorensteinWalter.PSL2 F)) :=
    CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card F hF h7 p hp2 hcop P
  have : IsCyclic A := isCyclic_of_injective (Subgroup.inclusion hP) (Subgroup.inclusion_injective hP)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := A)
  have h1 : orderOf g = p ^ 2 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg]
    exact hAc
  have h2 : g ^ p = 1 := Subtype.ext (by simpa using hA.2 g g.2)
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [h1] at h3
  have h4 : p ^ 2 ≤ p := Nat.le_of_dvd (Fact.out : p.Prime).pos h3
  have h5 := (Fact.out : p.Prime).two_le
  nlinarith

theorem seven_le_card_of_valid_A_one {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) : 7 ≤ q.card := by
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hv
  obtain ⟨⟨-, h4⟩, hdup⟩ := hv
  have h4' := h4 rfl
  have hne : q.card ≠ 4 ∧ q.card ≠ 5 := by
    constructor <;> intro h <;> exact hdup (Or.inl ⟨rfl, by omega⟩)
  have hne6 : q.card ≠ 6 := by
    intro h6
    rw [TauCeti.PrimePower.card_def] at h6
    have hl : q.p ≤ 6 := h6 ▸ Nat.le_self_pow q.exponent_pos.ne' _
    have he : q.exponent ≤ 2 := by
      by_contra hlt
      have : 2 ^ 3 ≤ q.p ^ q.exponent :=
        (Nat.pow_le_pow_left q.prime_p.two_le 3).trans (Nat.pow_le_pow_right q.prime_p.pos (by omega))
      omega
    have hpr := q.prime_p
    have hep := q.exponent_pos
    generalize q.p = a at *
    generalize q.exponent = b at *
    interval_cases a <;> interval_cases b <;>
      first | (norm_num at h6; done) | exact absurd hpr (by norm_num)
  omega

theorem kFactSeitzOuterCubeRankTwoAtPrime_A_one
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) {p : ℕ} [Fact p.Prime]
    (hexc : ¬ (p = 3 ∧ q.card = 8)) : KFactSeitzOuterCubeRankTwoAtPrime ⟨.A 1 q, hv⟩ p := by
  refine kFactSeitzOuterCubeRankTwoAtPrime_of_fieldAutData_oddA fun hp2 hpd _ _ => ?_
  have hp : p.Prime := Fact.out
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hpq : p ≠ q.p := by simpa using hpd
  let e : Cat ⟨.A 1 q, hv⟩ ≃* CFSG.GorensteinWalter.PSL2 (GaloisField q.p q.exponent) :=
    CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv
  have hKq : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  have h7 : 7 ≤ Nat.card (GaloisField q.p q.exponent) := by
    rw [hKq, ← TauCeti.PrimePower.card_def]
    exact seven_le_card_of_valid_A_one hv
  refine ⟨?_, ?_⟩
  · refine FieldAutData.of_mulEquiv e hp ?_
    by_cases hchar : ringChar (GaloisField q.p q.exponent) = 2
    · refine fieldAutData_psl2_even_odd_prime hp hp2 ?_ hchar
      rintro ⟨hp3, h8⟩
      exact hexc ⟨hp3, by rw [TauCeti.PrimePower.card_def, ← hKq]; exact h8⟩
    · exact fieldAutData_psl2_odd_prime hp hp2 hchar
  · intro σ _ A _ hAa hAc
    exact (not_exists_plane_psl2 hKq h7 hp2 hpq (A.map e.toMonoidHom)
      (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hAa _)
      (by rw [Subgroup.card_map_of_injective e.injective, hAc])).elim

theorem kFactSeitzOuterCubeRankTwoAtPrime_A
    (hL4 : L4TwoPlanes) {m : ℕ} (hm : 1 ≤ m) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A m q).Valid) {p : ℕ} [Fact p.Prime]
    (hexc : ¬ (m = 2 ∧ p = 3 ∧ 3 ∣ q.card - 1))
    (h8 : m = 1 → p = 3 → q.card = 8 → KFactSeitzOuterCubeRankTwoAtPrime ⟨.A m q, hv⟩ p) :
    KFactSeitzOuterCubeRankTwoAtPrime ⟨.A m q, hv⟩ p := by
  rcases (by omega : m = 1 ∨ 2 ≤ m) with rfl | hm2
  · by_cases h : p = 3 ∧ q.card = 8
    · exact h8 rfl h.1 h.2
    · exact kFactSeitzOuterCubeRankTwoAtPrime_A_one hv h
  · exact kFactSeitzOuterCubeRankTwoAtPrime_A_ge_two hL4 hm2 hv hexc

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
