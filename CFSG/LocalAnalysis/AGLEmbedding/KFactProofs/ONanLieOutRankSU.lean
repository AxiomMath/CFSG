module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRankNode
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSU
public import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOneLast
import CFSG.LieType.Steinberg.CentralExt.SUTwo

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ}

include hF in
theorem quasiNode_su {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h4 : 4 ≤ 2 ^ f)
    (hpq : p ^ 2 ∣ 2 ^ f + 1) (i : Fin (n / 2)) : QuasiNode (rootDatum hF n) p i := by
  have hσ := unitaryInvolution_involutive hF
  have hq2 : p ^ 2 ∣ (2 ^ f) ^ 2 - 1 := by
    refine hpq.trans ⟨2 ^ f - 1, ?_⟩
    obtain ⟨a, ha⟩ : ∃ a, 2 ^ f = a + 1 := ⟨2 ^ f - 1, by omega⟩
    rw [ha]
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  by_cases hk : i.val + 1 < n / 2
  · have hF4 : 4 ≤ Nat.card F := by rw [hF]; nlinarith
    refine QuasiNode.of_equiv_sl2 hp hF4 ?_ (rankOneShortEquiv (hσ := hσ) hk)
    rw [hF]
    have := Nat.sub_dvd_pow_sub_pow ((2 ^ f) ^ 2) 1 2
    rw [one_pow] at this
    exact hq2.trans this
  · by_cases he : Even n
    · obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
      refine QuasiNode.of_equiv_sl2 (k := fixedSubfield F 2 f) hp ?_ ?_
        ((rankOneLastEvenEquiv hF he hk).trans (hypEquiv hζ0 hζ).symm)
      · rw [card_fixedSubfield hF]
        exact h4
      · rw [card_fixedSubfield hF]
        exact hq2
    · have hnq : ((3 : ℕ), 2 ^ f) ≠ (3, 2) := fun h => by
        have := (Prod.mk.inj h).2
        omega
      have hq : CFSG.Open.IsQuasisimple (SU (unitaryInvolution F 2 f) 3) := by
        obtain ⟨hperf, hsimple, -⟩ := isQuasisimple_SU hF le_rfl hnq
        exact ⟨hperf.commutator_eq_top, hsimple⟩
      refine QuasiNode.of_equiv hp (rankOneLastOddEquiv hF he hk) hq ?_ ?_
      · rw [card_SU_three hF]
        exact (Dvd.dvd.mul_left hq2 _).mul_right _
      · intro hd
        have : Fact p.Prime := ⟨hp⟩
        obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hd
        have h3 := su_three_center_pow_three hF h4 z.2
        have h3' := orderOf_dvd_of_pow_eq_one h3
        rw [Subgroup.orderOf_coe, hz] at h3'
        have := Nat.le_of_dvd (by norm_num) h3'
        omega

theorem exists_quasisimple_psu {Y : Type} [Group Y] [Finite Y] {L T J : Subgroup Y}
    (hT : IsSylowTwoOf T L) (hNJ : L ⊓ Subgroup.normalizer (T : Set Y) ≤ J) (hJL : J ≤ L)
    (hnB : ∀ T' : Subgroup Y, IsSylowTwoOf T' L → J ≠ L ⊓ Subgroup.normalizer (T' : Set Y))
    {n f p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hC : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU n 2 f) (hpq : p ^ 2 ∣ 2 ^ f + 1) :
    ∃ X : Subgroup Y, X ≤ J ∧ CFSG.Open.IsQuasisimple ↥X ∧ p ^ 2 ∣ Nat.card X := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := hC
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
  have : Finite (SU (unitaryInvolution F 2 f) n) := Finite.of_injective _ Subtype.val_injective
  have h25 : 25 ≤ p ^ 2 := by nlinarith
  have h4 : 4 ≤ 2 ^ f := by
    have : p ^ 2 ≤ 2 ^ f + 1 := Nat.le_of_dvd (Nat.succ_pos _) hpq
    omega
  exact exists_quasisimple_of_borelQuotient hT hNJ hJL hnB
    (borelQuotient_su hcard (by omega) ζ hζ e) hp (quasiNode_su hcard hp hp5 h4 hpq)

end CFSG.AGLEmbedding.LieOut
