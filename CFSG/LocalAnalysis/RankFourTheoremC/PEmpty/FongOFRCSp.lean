module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLiePSp
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCArith
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevSp
import CFSG.LieType.Steinberg.CentralExt.SymplecticPerfect

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSp StatedScalars)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.RankThreeUC.S15

theorem pRank_statedProj_Sp_formula {F : Type} [Field F] [Finite F] {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpF : ¬ p ∣ Nat.card F) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSp n F))) =
      (if Even (orderOf (Nat.card F : ZMod p)) then 2 * n else n) /
        orderOf (Nat.card F : ZMod p) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Nat.card F := (Nat.card_eq_fintype_card).symm
  have hZ : ¬ p ∣ Nat.card ((StatedScalars (Fin n ⊕ Fin n) F).subgroupOf (StatedSp n F)) := by
    intro h
    have h1 := CFSG.LieType.Steinberg.card_statedScalars_subgroupOf_statedSp_le_two n F
    have h2 := Nat.le_of_dvd Nat.card_pos h
    have h3 := hp.two_le
    omega
  refine (CFSG.SectionRank.pRank_quotient_eq _ hZ).trans ?_
  have := RankChevProof.pRank_statedSp (hp.odd_of_ne_two hp2) F (by rwa [hc]) n
  rwa [hc] at this

theorem pRank_statedProj_Sp_eq_of_pow {F F₀ : Type} [Field F] [Field F₀] [Finite F] [Finite F₀]
    {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcard : Nat.card F = Nat.card F₀ ^ p)
    (hpF : ¬ p ∣ Nat.card F) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSp n F))) =
      CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSp n F₀))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hF₀ : ¬ p ∣ Nat.card F₀ := fun h => hpF (hcard ▸ h.trans (dvd_pow_self _ hp.ne_zero))
  rw [pRank_statedProj_Sp_formula hp hp2 hpF, pRank_statedProj_Sp_formula hp hp2 hF₀, hcard,
    OFRC.orderOf_natCast_pow_prime]

theorem outerFixedRankCrossAt_PSp : OuterFixedRankCrossAt .PSp := by
  intro K _ _ n ℓ f hadm hmodel hT p hp hp5 hℓ hdivL α hαp hαin hrk
  have hcl : StatedClassicalModel K .PSp n ℓ f :=
    hmodel.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  obtain ⟨hpf, F₀, hF₀, hF₀fin, hcard, hrank⟩ := psp_pRank_fixed hcl hp (by omega) α hαp hαin
  obtain ⟨⟨hℓp, hf, hn, -⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  have hFcard' : Nat.card F = Nat.card F₀ ^ p := by
    rw [hFcard, hcard, ← pow_mul, Nat.div_mul_cancel hpf]
  have hpF : ¬ p ∣ Nat.card F := by
    rw [hFcard]
    exact OFRC.not_dvd_pow_of_ne hp hℓp hℓ
  have hK : CFSG.Open.pRank p (⊤ : Subgroup K) =
      CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSp n F))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
  have heq := pRank_statedProj_Sp_eq_of_pow (n := n) hp (by omega) hFcard' hpF
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
