module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieCrossPSU
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LieType.OutStructure

theorem not_dvd_of_pRank_le_three_of_statedPSU {S : Type} [Group S] [Finite S] {N r f p : ℕ}
    (hcl : CFSG.Open.StatedClassicalModel S .PSU N r f) (hN : 6 ≤ N) (hp : p.Prime)
    (hp2 : p ≠ 2) (hrk : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 3) :
    ¬ p ∣ r ^ f ∧ ¬ p ∣ r ^ f + 1 := by
  have hcl' := hcl
  obtain ⟨⟨hr, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hcl'
  constructor
  · intro hdvd
    obtain rfl : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hdvd)
    obtain ⟨-, -, hrk'⟩ := CFSG.SectionRank.classical_model_rank hp2 hcl
    rcases hrk' with ⟨h, -⟩ | ⟨-, ⟨hn3, -⟩ | h4⟩ | ⟨h, -⟩ | h4
    · exact absurd h (by decide)
    · omega
    · omega
    · exact absurd h (by decide)
    · omega
  · intro hζq
    have : Fact p.Prime := ⟨hp⟩
    have hq0 : r ^ f ≠ 0 := pow_ne_zero _ hr.ne_zero
    have hpK : p ∣ Nat.card Kˣ := by
      rw [Nat.card_units, hK, show (r ^ f) ^ 2 - 1 = (r ^ f) ^ 2 - 1 ^ 2 by norm_num,
        Nat.pow_two_sub_pow_two]
      exact hζq.mul_right _
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hpK
    obtain ⟨E, hE, hEcard⟩ :=
      CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.exists_elemAbelian_four_projDiag hp
        (by omega) (Or.inl (by omega)) hζ (CFSG.Open.StatedSU N (r ^ f) K)
        (fun u hu _ hprod =>
          CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree.PSUThree.diagGL_mem hq0 u
            (fun i => orderOf_dvd_iff_pow_eq_one.mp
              ((orderOf_dvd_of_mem_zpowers (hu i)).trans (hζ ▸ hζq))) hprod)
    have h4 : 4 ≤ CFSG.Open.pRank p
        (⊤ : Subgroup (CFSG.Open.StatedProj (CFSG.Open.StatedSU N (r ^ f) K))) :=
      CFSG.SectionRank.le_pRank hp.one_lt le_top hE hEcard
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e] at hrk
    omega

end CFSG.LieType.OutStructure
