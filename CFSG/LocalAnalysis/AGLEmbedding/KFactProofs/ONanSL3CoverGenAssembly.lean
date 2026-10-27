module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenCoverLin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenCoverUni
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3FourGen

public section

namespace CFSG.AGLEmbedding.KFactProofs.CoverThree

open CFSG CFSG.Open TauCeti CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC

@[expose] def SL3CoverGenTwoModAbFix : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K → Nat.card (Subgroup.center K) = 3 →
    ∀ d : ValidLieTypeIndex, IsLinThreeCover3 d →
      Nonempty (K ⧸ Subgroup.center K ≃* (CFSGIndex.lie d).Group) → KGenTwoModAbFix 3 K

theorem card_eq_four_iff {q : PrimePower} : q.card = 4 ↔ q.p = 2 ∧ q.exponent = 2 := by
  rw [PrimePower.card_def]
  have hp : q.p.Prime := q.prime_p
  have he : 0 < q.exponent := q.exponent_pos
  constructor
  · intro h
    have hpd : q.p ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← h]
      exact dvd_pow_self q.p he.ne'
    have hp2 : q.p = 2 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hpd)
    refine ⟨hp2, ?_⟩
    rw [hp2] at h
    have h2 : (2 : ℕ) ^ q.exponent = 2 ^ 2 := by rw [h]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    norm_num

theorem sl3CoverGenTwoModAbFix :
    SL3CoverGenTwoModAbFix := by
  intro K _ _ hK hZ3 d hd ⟨e⟩
  obtain ⟨dd, hv⟩ := d
  rcases hd with ⟨q, hq, h3⟩ | ⟨q, hq, h3⟩
  · change dd = .A 2 q at hq
    subst hq
    by_cases h4 : q.p = 2 ∧ q.exponent = 2
    · exact kGenTwoModAbFix_of_kGenTwoModAb
        (sl3FourGenTwoModAb K hK hZ3 ⟨.A 2 q, hv⟩ ⟨q, h4.1, h4.2, rfl⟩ ⟨e⟩)
    · exact kGenTwoModAbFix_linCover hK hZ3 hv h3 (fun h => h4 (card_eq_four_iff.1 h)) e
  · change dd = .twistedA 2 q at hq
    subst hq
    exact kGenTwoModAbFix_uniCover hK hZ3 hv h3 e

end CFSG.AGLEmbedding.KFactProofs.CoverThree
