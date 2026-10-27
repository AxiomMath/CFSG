module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113DetA7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Core
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ClassicalRadical
public import CFSG.Alternating.Multipliers.Main
public import CFSG.RankThree.PartTwo.KFacts.KS44Multiplier
public import CFSG.LocalAnalysis.OddStandard.ONanB2Quot
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFInputs
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.Quasithin.B113KDet

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

private theorem dk2_odd_dvd_two {n : ℕ} (hodd : Odd n) (h : n ∣ 2) : n = 1 := by
  obtain ⟨k, rfl⟩ := hodd
  have := Nat.le_of_dvd (by norm_num) h
  omega

private theorem dk2_odd_dvd_six {n : ℕ} (hodd : Odd n) (h : n ∣ 6) : n = 1 ∨ n = 3 := by
  obtain ⟨k, rfl⟩ := hodd
  have hk : k ≤ 2 := by
    have := Nat.le_of_dvd (by norm_num) h
    omega
  interval_cases k <;> first | omega | norm_num at h

private theorem dk2_nonempty_of_card_center_eq_one {H : Type} [Group H] {m : ℕ}
    (h1 : Nat.card ↥(Subgroup.center H) = 1)
    (e : (H ⧸ Subgroup.center H) ≃* alternatingGroup (Fin m)) :
    Nonempty (H ≃* alternatingGroup (Fin m)) := by
  have hbot : Subgroup.center H = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm.trans e⟩

private theorem dk2_alt_case
    (hD : CFSG.QuasithinUnique.Bridge.AsB42DichotomyNat)
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G A L : Subgroup (MulAut V)} (hO2 : pCoreOf 2 G = ⊥) (hA : IsFFStarOffender G A)
    (hL : CFSG.Open.IsComponentOf L G) (hLA : ⁅L, A⁆ = L)
    {m : ℕ} (hm : 5 ≤ m) (e : (↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin m)) :
    IsLieAltType ↥L := by
  have hLq : CFSG.IsQuasisimple ↥L := CFSG.Quasithin.B1Red.isQuasisimple_of_open hL.2.2
  have hodd : Odd (Nat.card ↥(Subgroup.center ↥L)) :=
    CFSG.QuasithinUnique.Bridge.odd_card_center_of_isComponentOf hO2 hL
  have hsch : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (alternatingGroup (Fin m))) = if m = 6 ∨ m = 7 then 6 else 2 :=
    (CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput m hm).2
  have hdvd : Nat.card ↥(Subgroup.center ↥L) ∣
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin m))) := by
    rw [← CFSG.OddStandard.ONanRec.B2.card_hopfMultiplier_congr e]
    exact CFSG.RankThree.PartTwo.KFacts.KS44.card_center_dvd_card_hopfMultiplier hLq
  rw [hsch] at hdvd
  split_ifs at hdvd with h67
  · rcases dk2_odd_dvd_six hodd hdvd with h1 | h3
    · exact Or.inr (Or.inl ⟨m, dk2_nonempty_of_card_center_eq_one h1 e⟩)
    · rcases h67 with rfl | rfl
      · exact Or.inr (Or.inr (And.intro hLq (And.intro h3 (Nonempty.intro e))))
      · exfalso
        have hlist : CFSG.Milestones.SQTKSimpleList (↥L ⧸ Subgroup.center ↥L) :=
          Or.inl ⟨7, by norm_num, by norm_num, Nonempty.intro e⟩
        have hbot := CFSG.QuasithinUnique.Bridge.B113Det.center_eq_bot_of_alt7 hD hV hA hL.1
          hLq hLA hodd hlist e
        rw [hbot, Subgroup.card_bot] at h3
        omega
  · exact Or.inr (Or.inl ⟨m, dk2_nonempty_of_card_center_eq_one (dk2_odd_dvd_two hodd hdvd) e⟩)

theorem isLieAltType_of_ffConclusion
    (hD : CFSG.QuasithinUnique.Bridge.AsB42DichotomyNat)
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G A L : Subgroup (MulAut V)} (hO2 : pCoreOf 2 G = ⊥) (hA : IsFFStarOffender G A)
    (hL : CFSG.Open.IsComponentOf L G) (hLA : ⁅L, A⁆ = L)
    (hc : CFSG.HardMathSupport.Cooperstein.Coordinator.FFConclusion (↥L ⧸ Subgroup.center ↥L)) :
    IsLieAltType ↥L := by
  have hLq : CFSG.IsQuasisimple ↥L := CFSG.Quasithin.B1Red.isQuasisimple_of_open hL.2.2
  rcases hc with hcl | ⟨m, hm, ⟨e⟩⟩
  · open CFSG.HardMathSupport.Cooperstein.StructureLie in
    rcases evenLieType_or_alt_six_or_psu_of_isClassicalTwoOrG2 hcl with h | h | h
    · exact Or.inl (And.intro hLq (Or.inl h))
    · have e6 : (↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 6) := Classical.choice h
      exact dk2_alt_case hD hV hO2 hA hL hLA (by norm_num : 5 ≤ 6) e6
    · exact Or.inl (And.intro hLq (Or.inr h))
  · exact dk2_alt_case hD hV hO2 hA hL hLA hm e

end CFSG.Quasithin.B113KDet
