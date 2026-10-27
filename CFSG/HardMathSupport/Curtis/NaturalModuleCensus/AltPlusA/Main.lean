module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltPlusSplit
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltPlusA.OddCentre
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.CenterVoid
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.CenterCore
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.CoverTransport

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank


theorem exists_unitaryCoverPlus (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type} [Group Y]
    [Finite Y] {L J : Subgroup Y} (h : CompParabE L J) {p : ℕ}
    (hX : IsLieOf (IdxPlusA p) (↥L ⧸ Subgroup.center ↥L)) :
    ∃ (f n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      1 ≤ f ∧ 3 ≤ n ∧ (n, 2 ^ f) ≠ (3, 2) ∧ Nat.card K = (2 ^ f) ^ 2 ∧ p ∣ 2 ^ f + 1 ∧
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
    obtain ⟨hq2, hq, hpq⟩ := hd
    have : Group.IsPerfect ↥L := ⟨h.comp.2.2.1⟩
    have hodd := odd_card_center_of_twistedA hGA hv hq2 hq e
    have hCP : CompParab L J := ⟨h.comp, h.type, hodd, h.parab, h.ne_top, h.ne_borel⟩
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    rw [hq2] at hm
    obtain ⟨⟨-, hf, hn, hq'⟩, K, hF, hFfin, hcard, ⟨e'⟩⟩ := hm
    have : Fintype K := Fintype.ofFinite K
    have hchar : CharP K 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact charP_of_card_eq_prime_pow (f := q.exponent * 2)
        (by rw [← Nat.card_eq_fintype_card, hcard, ← pow_mul])
    have hpq' : p ∣ 2 ^ q.exponent + 1 := by
      rwa [TauCeti.PrimePower.card_def, hq2] at hpq
    refine ⟨q.exponent, r + 1, K, hF, hFfin, hchar, hf, hn, hq', hcard, hpq', ?_⟩
    obtain ⟨ρ, hρs, -, hρe⟩ := kFactCoverUnitary Y L hCP.comp hCP.odd (r + 1)
      (2 ^ q.exponent) K hcard hn hq' e'
    refine ⟨ρ, hρs, fun g => ?_, ?_⟩
    · rw [← QuotientGroup.eq_one_iff, ← map_eq_one_iff e'.toMonoidHom e'.injective,
        MulEquiv.coe_toMonoidHom, hρe g, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    · obtain ⟨T, hT⟩ := hCP.exists_sylow_normalizer_le
      obtain ⟨S₀, hS₀⟩ := UnitaryLevi.exists_sylow_normalizer_le_comap hρs T hT
      refine ⟨S₀, hS₀, fun htop => hCP.ne_top (le_antisymm hCP.parab.1 fun y hy => ?_)⟩
      obtain ⟨g, hg⟩ := hρs ⟨y, hy⟩
      have := htop ▸ Subgroup.mem_top g
      rw [Subgroup.mem_comap, hg, Subgroup.mem_subgroupOf] at this
      exact this
  | _ => exact hd.elim

theorem altPlusCellA (hGA : CFSG.Open.GriessAllModelsStatement) : AltPlusCellA := by
  intro Y _ _ L J p x hC hp _ hxL hxp _ hfix hX _
  have hp' : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp with rfl | rfl <;> norm_num
  obtain ⟨f, n, K, _, _, _, hf, hn, -, hK, hpq, ρ, hρs, hcompat, S₀, hS₀, hJtop⟩ :=
    exists_unitaryCoverPlus hGA hC hX
  obtain ⟨t, ht, htJ⟩ := UnitaryLevi.exists_lift (J := J) ρ hρs hcompat
    (u := x) (Subgroup.mem_sup_left hxL) hxp hfix
  exact UnitaryLevi.false_of_pow_mem_scalars hK hf (by omega) hp' hp2 hpq hS₀ hJtop t ht
    fun g hg => htJ g hg

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
