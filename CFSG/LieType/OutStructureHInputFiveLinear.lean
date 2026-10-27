module

public import CFSG.LieType.OutStructureFixRankLinear
public import CFSG.LieType.OutStructureOuterLiftLinear
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossTorus
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOneKSCenter
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LieType.OutStructure

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem not_dvd_of_pRank_le_three_of_statedPSL {S : Type} [Group S] [Finite S] {N r f p : ℕ}
    (hcl : CFSG.Open.StatedClassicalModel S .PSL N r f) (hN : 6 ≤ N) (hp : p.Prime)
    (hp2 : p ≠ 2) (hrk : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 3) :
    ¬ p ∣ r ^ f ∧ ¬ p ∣ r ^ f - 1 := by
  have hcl' := hcl
  obtain ⟨⟨hr, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hcl'
  constructor
  · intro hdvd
    obtain rfl : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hdvd)
    obtain ⟨-, -, hrk'⟩ := CFSG.SectionRank.classical_model_rank hp2 hcl
    rcases hrk' with ⟨-, ⟨hn2, -⟩ | ⟨hn3, -⟩ | h4⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h4
    · omega
    · omega
    · omega
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · omega
  · intro hdvd
    have : Fact p.Prime := ⟨hp⟩
    have hpK : p ∣ Nat.card Kˣ := by
      rwa [Nat.card_units, hK]
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hpK
    obtain ⟨E, hE, hEcard⟩ :=
      CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.exists_elemAbelian_four_projDiag hp
        (by omega) (Or.inl (by omega)) hζ (CFSG.Open.StatedSL N K) (fun u _ _ hprod => by
          rw [CFSG.Open.StatedAPI.mem_statedSL_iff,
            CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.det_diagGL, ← Units.coe_prod,
            hprod, Units.val_one])
    have h4 : 4 ≤ CFSG.Open.pRank p
        (⊤ : Subgroup (CFSG.Open.StatedProj (CFSG.Open.StatedSL N K))) :=
      CFSG.SectionRank.le_pRank hp.one_lt le_top hE hEcard
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e] at hrk
    omega

theorem hInput_linear_five
    {X : Type} [Group X] [Finite X]
    (hK : CFSG.Open.IsKGroup X) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLn : L.Normal)
    (hX2 : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2) {N r f : ℕ}
    (hcl : CFSG.Open.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL N r f) (hN : 6 ≤ N) :
    ¬ CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
        (L ⊔ Subgroup.centralizer (L : Set X)) →
      (∃ c : X, c ∈ Subgroup.centralizer (L : Set X) ∧ orderOf c = p) ∨
      ∃ x : X, orderOf x = p ∧ x ∉ L ⊔ Subgroup.centralizer (L : Set X) ∧
        ∃ E : Subgroup X, E ≤ L ∧ CFSG.Open.IsElemAbelian p E ∧
          Nat.card E = p ^ CFSG.Open.pRank p L ∧ ∀ a ∈ E, a * x = x * a := by
  have := hLn
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hLX : CFSG.Open.pRank p L ≤ CFSG.Open.pRank p (⊤ : Subgroup X) :=
    CFSG.SectionRank.pRank_mono hp.one_lt le_top
  have hZ : ¬ p ∣ Nat.card (Subgroup.center ↥L) := by
    intro hdvd
    have h3 := CFSG.LocalAnalysis.RankThreeUC.AGL81C.kFactCenterRankFive_holds
      X hK L hL p hp hp5 hdvd
    omega
  have hrkS : CFSG.Open.pRank p (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) ≤ 3 := by
    rw [CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_quotient_center_eq_of_not_dvd
      hp hZ, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
    omega
  obtain ⟨hpq, hq1⟩ := not_dvd_of_pRank_le_three_of_statedPSL hcl hN hp hp2 hrkS
  obtain ⟨-, K, _, _, hKcard, ⟨eS⟩⟩ := hcl
  let e : (↥L ⧸ Subgroup.center ↥L) ≃* projectiveSL N K :=
    eS.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj N K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL N K))
  have hdiv : ¬ p ∣ Nat.gcd N (Nat.card K - 1) := fun h =>
    hq1 (by rw [← hKcard]; exact h.trans (Nat.gcd_dvd_right _ _))
  exact hInput_linear_of_exists_of_cross hL e (by omega) hp hp2 hZ (by rwa [hKcard]) hdiv
    (fun hnot hc => exists_orderOf_eq_not_mem_of_projectiveSL hL e (by omega) hp hp2 hdiv hnot hc)

end CFSG.LieType.OutStructure
