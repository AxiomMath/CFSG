module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryCover
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.AGLEmbedding.ParabPrime (perfectJoin)

namespace UnitaryLevi

theorem _root_.CFSG.AGLEmbedding.CompParab.exists_sylow_normalizer_le {Y : Type} [Group Y]
    [Finite Y] {L J : Subgroup Y} (h : CompParab L J) :
    ∃ T : Sylow 2 ↥L,
      Subgroup.normalizer ((T : Subgroup ↥L) : Set ↥L) ≤ J.subgroupOf L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJL, T, ⟨hTL, hT2, hTi⟩, hNJ⟩ := h.parab
  let T' : Sylow 2 ↥L := (hT2.comap_subtype (K := L)).toSylow hTi
  refine ⟨T', fun x hx => ?_⟩
  rw [Subgroup.mem_subgroupOf]
  refine hNJ ⟨x.2, Subgroup.mem_normalizer_fintype fun t ht => ?_⟩
  have h1 : (⟨t, hTL ht⟩ : ↥L) ∈ (T' : Subgroup ↥L) := by
    simpa [T', Subgroup.mem_subgroupOf] using ht
  have h2 := (Subgroup.mem_normalizer_iff.1 hx ⟨t, hTL ht⟩).1 h1
  simpa [T', Subgroup.mem_subgroupOf] using h2

theorem exists_sylow_map_eq {G X : Type*} [Group G] [Group X] [Finite G] {ψ : G →* X}
    (hψ : Function.Surjective ψ) (T : Sylow 2 X) :
    ∃ S : Sylow 2 G, (S : Subgroup G).map ψ = (T : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective (p := 2) hψ T
  exact ⟨S, by rw [← hS, Sylow.coe_mapSurjective]⟩

theorem exists_sylow_normalizer_le_comap {G X : Type*} [Group G] [Group X] [Finite G]
    {ψ : G →* X} (hψ : Function.Surjective ψ) {J : Subgroup X} (T : Sylow 2 X)
    (hNJ : Subgroup.normalizer ((T : Subgroup X) : Set X) ≤ J) :
    ∃ S : Sylow 2 G, Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ J.comap ψ := by
  obtain ⟨S, hS⟩ := exists_sylow_map_eq hψ T
  refine ⟨S, fun x hx => ?_⟩
  rw [Subgroup.mem_comap]
  refine hNJ ?_
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [← hS]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨x * s * x⁻¹, (Subgroup.mem_normalizer_iff.1 hx s).1 hs, by simp⟩
  · rintro ⟨s, hs, hsy⟩
    refine ⟨x⁻¹ * s * x, ?_, ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.1 hx (x⁻¹ * s * x)).2
      have h2 : x * (x⁻¹ * s * x) * x⁻¹ = s := by group
      rw [h2] at h1
      exact h1 hs
    · simp [hsy, mul_assoc]


theorem exists_unitaryCover_of_index {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (h : CompParab L J) (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hd : q.p = 2)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) :
    ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      1 ≤ q.exponent ∧ 3 ≤ n ∧ (n, 2 ^ q.exponent) ≠ (3, 2) ∧
      Nat.card K = (2 ^ q.exponent) ^ 2 ∧
      ∃ ρ : StatedSU n (2 ^ q.exponent) K →* ↥L, Function.Surjective ρ ∧
        (∀ g, ρ g ∈ Subgroup.center ↥L ↔
          ((g : GL (Fin n) K) ∈ StatedScalars (Fin n) K)) ∧
        ∃ S₀ : Sylow 2 (StatedSU n (2 ^ q.exponent) K),
          Subgroup.normalizer ((S₀ : Subgroup (StatedSU n (2 ^ q.exponent) K)) :
            Set (StatedSU n (2 ^ q.exponent) K)) ≤ (J.subgroupOf L).comap ρ ∧
          (J.subgroupOf L).comap ρ ≠ ⊤ := by
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
  refine ⟨ρ, hρs, fun g => ?_, ?_⟩
  · rw [← QuotientGroup.eq_one_iff, ← map_eq_one_iff e'.toMonoidHom e'.injective,
      MulEquiv.coe_toMonoidHom, hρe g, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  · obtain ⟨T, hT⟩ := h.exists_sylow_normalizer_le
    obtain ⟨S₀, hS₀⟩ := exists_sylow_normalizer_le_comap hρs T hT
    refine ⟨S₀, hS₀, fun htop => h.ne_top (le_antisymm h.parab.1 fun y hy => ?_)⟩
    obtain ⟨g, hg⟩ := hρs ⟨y, hy⟩
    have := htop ▸ Subgroup.mem_top g
    rw [Subgroup.mem_comap, hg, Subgroup.mem_subgroupOf] at this
    exact this

theorem exists_unitaryCover {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (h : CompParab L J) (hX : IsLieOf IdxTwistedA (↥L ⧸ Subgroup.center ↥L)) :
    ∃ (f n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      1 ≤ f ∧ 3 ≤ n ∧ (n, 2 ^ f) ≠ (3, 2) ∧ Nat.card K = (2 ^ f) ^ 2 ∧
      ∃ ρ : StatedSU n (2 ^ f) K →* ↥L, Function.Surjective ρ ∧
        (∀ g, ρ g ∈ Subgroup.center ↥L ↔
          ((g : GL (Fin n) K) ∈ StatedScalars (Fin n) K)) ∧
        ∃ S₀ : Sylow 2 (StatedSU n (2 ^ f) K),
          Subgroup.normalizer ((S₀ : Subgroup (StatedSU n (2 ^ f) K)) :
            Set (StatedSU n (2 ^ f) K)) ≤ (J.subgroupOf L).comap ρ ∧
          (J.subgroupOf L).comap ρ ≠ ⊤ := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hX
  cases d with
  | twistedA r q =>
    obtain ⟨n, K, hF, hFfin, hchar, hf, hn, hq, hcard, hrest⟩ :=
      exists_unitaryCover_of_index h r q hv hd e
    exact ⟨q.exponent, n, K, hF, hFfin, hchar, hf, hn, hq, hcard, hrest⟩
  | _ => exact hd.elim

end UnitaryLevi

end CFSG.AGLEmbedding
