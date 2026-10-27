module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23Eq
public import CFSG.LieType.Steinberg.CentralExt.PSLMultiplier
public import CFSG.GH74.Generic.GKFCover
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23JSide

public section

namespace CFSG.ComponentClassification.GSThmB.CF23L34

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.CatFactsL4U4
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.CatFactsL4U4.OutInv

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)

include hKa in
theorem center_eq_bot_of_L316 (hN : Blueprint.LieModel ↥(NL hKa) .PSL 3 2 4) :
    center (OddBar h.K) = ⊥ := by
  obtain ⟨eN⟩ := nonempty_NL_equiv hKa
  obtain ⟨-, F, _, _, hF, ⟨eS⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hN
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 16 := by rw [Fintype.card_eq_nat_card, hF]; norm_num
  obtain ⟨-, ⟨eM⟩⟩ := LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier (k := F) (n := 3)
    le_rfl (by omega)
  have hdvd := GH74.Generic.card_center_dvd_hopfMultiplier h.isQuasisimple_K
    ((eN.symm.trans eS).trans
      (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm)
  rw [← Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
    Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_zmod,
    hcard] at hdvd
  have hodd : Odd (Nat.card (center (OddBar h.K))) := Odd.of_dvd_nat (by decide) hdvd
  rw [eq_bot_iff]
  intro c hc
  rw [mem_bot]
  have h1 : orderOf c ∣ Nat.card (center (OddBar h.K)) := by
    rw [← Subgroup.orderOf_mk c hc]
    exact orderOf_dvd_natCard _
  exact CF23Diag.eq_one_of_mem_center_of_odd hc (Odd.of_dvd_nat hodd h1)

theorem fus23ConclW_of_L316
    (hL : Blueprint.LieModel (ZStarBar h.J) .PSL 3 2 2)
    (hN : Blueprint.LieModel ↥(NL hKa) .PSL 3 2 4)
    (hcos : ∀ n ∈ NL hKa, orderOf (phi hKa (abar h) * n) = 2 →
      ∃ γ ∈ NL hKa, γ⁻¹ * phi hKa (abar h) * γ = phi hKa (abar h) * n) :
    h.Fus23ConclW := by
  have hZK := center_eq_bot_of_L316 hKa hN
  obtain ⟨-, -, -, d, -, -, -, hdD, -, hd2, hdx, hdP⟩ := exists_fixed_D h hL
  obtain ⟨hζJ, hζ2, hcomm, hζα⟩ := zeta_facts hKa hZK hdD hd2 hdP
  have hα2 : phi hKa (abar h) * phi hKa (abar h) = 1 := by
    rw [← map_mul, abar_mul_self, map_one]
  obtain ⟨γ, hγN, hγ⟩ := hcos _ (Jhat_le_NL hKa hζJ) (orderOf_mul_eq_two hα2 hζ2 hcomm hζα)
  exact fus23ConclW_of_NL hKa hZK hdD hd2 hdx hdP hγN hγ

end CFSG.ComponentClassification.GSThmB.CF23L34
