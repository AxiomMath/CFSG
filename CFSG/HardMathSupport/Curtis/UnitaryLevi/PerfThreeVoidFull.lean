module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PerfThreeVoid
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.CoverTransportE
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.NormalizerConj
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.OuterCore
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDefs

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding CFSG.AGLEmbedding.UnitaryLevi
  CFSG.QuasithinUnique CFSG.AGLEmbedding.LieOut CFSG.LocalAnalysis.ComponentInitial Matrix

theorem false_of_cover_two {Y : Type} [Group Y] {L J : Subgroup Y} {u : Y}
    (hnorm : u ∈ Subgroup.normalizer (L : Set Y)) (hpow : u ^ 3 = 1)
    (hfix : ∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J) {n : ℕ} (hn : 4 ≤ n)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (ρ : StatedSU n (2 ^ 1) K →* ↥L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSU n (2 ^ 1) K))
    (hρe : ∀ g, e (QuotientGroup.mk (ρ g)) =
      (QuotientGroup.mk g : StatedProj (StatedSU n (2 ^ 1) K)))
    {S₀ : Sylow 2 (StatedSU n (2 ^ 1) K)}
    (hS₀ : Subgroup.normalizer ((S₀ : Subgroup (StatedSU n (2 ^ 1) K)) :
      Set (StatedSU n (2 ^ 1) K)) ≤ (J.subgroupOf L).comap ρ)
    (hJtop : (J.subgroupOf L).comap ρ ≠ ⊤) : False := by
  obtain ⟨A, hA, hA3, hconj⟩ := exists_unitary_conj_of_normalizer hn hK ρ e hρe hnorm hpow
  obtain ⟨W, hW0, hWt, hJW⟩ := exists_isTotallyIsotropicSU_of_normalizer_le hK hS₀ hJtop
  apply hW0
  refine eq_bot_of_stable_isotropic_cube_scalar hK hn A hA hA3 hWt fun g hg w hw => hJW g ?_ w hw
  obtain ⟨g', hg'1, hg'2⟩ := hconj g
  have hgg : g' = g := by
    apply Subtype.ext
    rw [hg'1, ← hg.eq]
    group
  rw [hgg] at hg'2
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  exact hfix _ (ρ g).2 hg'2


section Main


theorem fixPerfThreeVoid_twistedA : FixPerfThreeVoid (IsLieOf IdxTwistedA) := by
  intro Y _ _ L J u h hX
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hX
  cases d with
  | twistedA r q =>
    have hd' : q.p = 2 := hd
    have hcard2 : q.card = 2 :=
      card_eq_two_of_perfect_coprime_comp h.parab h.perf ⟨.twistedA r q, hv⟩ hd' e
    have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hd']
    have he1 : q.exponent = 1 := by
      have h1 : 2 ^ q.exponent = 2 ^ 1 := by rw [← hqc, hcard2, pow_one]
      exact Nat.pow_right_injective (le_refl 2) h1
    obtain ⟨n, K, _, _, _, hf, hn, hq, hK, ρ, e', hρs, hρe, hcompat, S₀, hS₀, hJtop⟩ :=
      exists_unitaryCover_with_iso h.parab r q hv hd' 1 he1 e
    have hn4 : 4 ≤ n := by
      by_contra hlt
      exact hq (by simp [show n = 3 by omega])
    exact false_of_cover_two h.norm h.pow h.fix hn4 hK ρ e' hρe hS₀ hJtop
  | _ => exact hd.elim

end Main

end CFSG.HardMathSupport.Curtis.UnitaryLevi
