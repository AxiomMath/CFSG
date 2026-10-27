module

public import CFSG.Dihedral.OriginalProjectiveExclusion
public import CFSG.Dihedral.GorensteinWalter

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem q_five_index_three_impossible [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hp : d.PureProjectiveNormalizer) (hn : d.n = 3) (hR : d.R ≠ ⊥)
    (w : CoordinateWitness (d.N ⧸ Assembly.oddCore d.N)) (hq : Nat.card w.K = 5)
    (hindex : (d.commonE.subgroupOf d.R).index = 3) : False := by
  obtain ⟨i, _, _, hi, _⟩ := hp.2.2.2.2
  rcases gorenstein_walter G hnonab d.S ⟨_, d.sylow_mulEquiv_dihedral⟩ with
    ⟨⟨e⟩⟩ | ⟨p, f, hprime, hodd, hf, ⟨e⟩⟩
  · have hsmall := d.N_card_le_seventy_two_of_aSeven_model hn hindex i hi e
    have hquot := d.quotient_card_eq_one_hundred_twenty_of_pure_coordinates hp w hq
    have hle : Nat.card (d.N ⧸ Assembly.oddCore d.N) ≤ Nat.card d.N :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (Assembly.oddCore d.N))
    omega
  · let : Fact p.Prime := hprime
    have hfpos : 1 ≤ f := by
      by_contra h
      have hfzero : f = 0 := by omega
      simp [hfzero] at hf
    have hK : IsOddPrimePower (Nat.card (GaloisField p f)) :=
      ⟨p, f, hprime.out, hodd, hfpos, GaloisField.card p f (by omega)⟩
    exact hR (d.R_eq_bot_of_psl2_model i hi (GaloisField p f) hK e)

end CFSG.DihedralBlueprint.OriginalData
