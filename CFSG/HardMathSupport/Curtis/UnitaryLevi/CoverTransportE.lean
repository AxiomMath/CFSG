module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.CoverTransport

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding
open CFSG.AGLEmbedding.UnitaryLevi


theorem exists_unitaryCover_with_iso {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (h : CompParab L J) (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hd : q.p = 2) (f : ℕ)
    (hfq : q.exponent = f)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) :
    ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      1 ≤ f ∧ 3 ≤ n ∧ (n, 2 ^ f) ≠ (3, 2) ∧ Nat.card K = (2 ^ f) ^ 2 ∧
      ∃ (ρ : StatedSU n (2 ^ f) K →* ↥L)
        (e' : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSU n (2 ^ f) K)),
        Function.Surjective ρ ∧
        (∀ g, e' (QuotientGroup.mk (ρ g)) =
          (QuotientGroup.mk g : StatedProj (StatedSU n (2 ^ f) K))) ∧
        (∀ g, ρ g ∈ Subgroup.center ↥L ↔
          ((g : GL (Fin n) K) ∈ StatedScalars (Fin n) K)) ∧
        ∃ S₀ : Sylow 2 (StatedSU n (2 ^ f) K),
          Subgroup.normalizer ((S₀ : Subgroup (StatedSU n (2 ^ f) K)) :
            Set (StatedSU n (2 ^ f) K)) ≤ (J.subgroupOf L).comap ρ ∧
          (J.subgroupOf L).comap ρ ≠ ⊤ := by
  subst hfq
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  rw [hd] at hm
  obtain ⟨⟨-, hf, hn, hq⟩, K, hF, hFfin, hcard, ⟨e'⟩⟩ := hm
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := q.exponent * 2)
      (by rw [← Nat.card_eq_fintype_card, hcard, ← pow_mul])
  refine ⟨r + 1, K, hF, hFfin, hchar, hf, hn, hq, hcard, ?_⟩
  obtain ⟨ρ, hρs, -, hρe⟩ := kFactCoverUnitary Y L h.comp h.odd (r + 1) (2 ^ q.exponent) K hcard
    hn hq e'
  refine ⟨ρ, e', hρs, hρe, fun g => ?_, ?_⟩
  · rw [← QuotientGroup.eq_one_iff, ← map_eq_one_iff e'.toMonoidHom e'.injective,
      MulEquiv.coe_toMonoidHom, hρe g, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  · obtain ⟨T, hT⟩ := h.exists_sylow_normalizer_le
    obtain ⟨S₀, hS₀⟩ := exists_sylow_normalizer_le_comap hρs T hT
    refine ⟨S₀, hS₀, fun htop => h.ne_top (le_antisymm h.parab.1 fun y hy => ?_)⟩
    obtain ⟨g, hg⟩ := hρs ⟨y, hy⟩
    have := htop ▸ Subgroup.mem_top g
    rw [Subgroup.mem_comap, hg, Subgroup.mem_subgroupOf] at this
    exact this

end CFSG.HardMathSupport.Curtis.UnitaryLevi
