module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatB.KFactsSp
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SchurFacts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem center_sp82_eq_bot {K : Type} [Group K] [Finite K]
    (hGA : CFSG.Open.GriessAllModelsStatement) (hK : CFSG.Open.IsQuasisimple K)
    (h : catalogIs (K ⧸ Subgroup.center K) S8.L84.isSp82) : Subgroup.center K = ⊥ := by
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.KFacts.lieIndex_isSp8two h
  obtain ⟨h1, h2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq Nat.prime_two (s := 1)
    (by norm_num) (hq2.trans (by norm_num))
  rcases CFSG.Models.lieModel_B 4 q hv e with hm | hm
  · rw [h1, h2] at hm
    have hdvd := CFSG.LocalAnalysis.GLTheoremA.card_center_dvd_of_table hGA hK hm (a := 1) (b := 1)
      (c := 1) (d := 1) (by decide) (by decide) (by norm_num)
    exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 (hdvd.trans (by norm_num)))
  · rw [h1, h2] at hm
    exact absurd hm.admissible.2.2.2 (by norm_num)

theorem center_alt12_eq_bot {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) (hO : GLAPPrimeCore 3 K = ⊥)
    (h : catalogIs (K ⧸ Subgroup.center K) (isAltN 12)) : Subgroup.center K = ⊥ := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact (show False from hi).elim
  | alternating m hm =>
    have hmn : m = 12 := hi
    subst hmn
    have hA : CFSG.LocalAnalysis.GLTheoremB.MovingAround.IsAltType 12 (K ⧸ Subgroup.center K) :=
      Nonempty.intro e
    rcases CFSG.LocalAnalysis.GLTheoremB.MovingAround.SchurFacts.center_eq_bot_or_of_isAltType
        Nat.prime_three (by norm_num) hK hO hA with hZ | ⟨-, h67⟩
    · exact hZ
    · omega
  | lie _ => exact (show False from hi).elim
  | sporadic _ => exact (show False from hi).elim

theorem i1431MultS_holds :
    I1431MultS := by
  intro Y _ _ hq hO hcat
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rcases hi with hSp | hAlt
  · exact center_sp82_eq_bot hGA hq ⟨i, hSp, ⟨e⟩⟩
  · exact center_alt12_eq_bot hq hO ⟨i, hAlt, ⟨e⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
