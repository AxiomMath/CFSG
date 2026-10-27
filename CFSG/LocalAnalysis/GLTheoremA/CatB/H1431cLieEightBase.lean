module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzEvenCentreD4F4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClBase
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieInn

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup LieOrderBridge)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (RkY)

theorem lieSEight_card_pSimple_dvd {S : Type} [Group S] [Finite S] (J : Subgroup S) :
    Nat.card (PSimple 3 J) ∣ Nat.card S :=
  (I1431C2.cl_card_psimple_dvd J).trans (Subgroup.card_subgroup_dvd_card J)

theorem lieSEight_not_comp_of_not_dvd (hLO : LieOrderBridge) {S : Type} [Group S] [Finite S]
    {α : MulAut S} (h : ¬ 1056706560 ∣ Nat.card S) : ¬ CompOfType S α S8.L84.isSp48 := by
  rintro ⟨J, -, hT⟩
  exact h ((lieSInn_card_sp48 hLO hT).symm ▸ lieSEight_card_pSimple_dvd J)

theorem lieSEight_false_of_card_le (hLO : LieOrderBridge) {S : Type} [Group S] [Finite S]
    {α : MulAut S} (hα : α ≠ 1) (hS : Nat.card S ≤ 1056706560) :
    ¬ CompOfType S α S8.L84.isSp48 := by
  rintro ⟨J, hJ, hT⟩
  have hcard : Nat.card (PSimple 3 J) = 1056706560 := lieSInn_card_sp48 hLO hT
  have hJ1 : 1056706560 ≤ Nat.card J := by
    rw [← hcard]
    exact Nat.le_of_dvd Nat.card_pos (I1431C2.cl_card_psimple_dvd J)
  have hJS : Nat.card J ≤ Nat.card S :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card J)
  have hJtop : J = ⊤ := Subgroup.eq_top_of_card_eq J (le_antisymm hJS (hS.trans hJ1))
  apply hα
  ext g
  have hg : g ∈ fixSubgroup α := hJ.1 (by rw [hJtop]; exact Subgroup.mem_top g)
  exact hg

theorem lieSEightNoAt_of_not_dvd (hLO : LieOrderBridge) {P : TauCeti.LieTypeIndex → Prop}
    (h : ∀ d : TauCeti.ValidLieTypeIndex, P d.1 → d.1.characteristic = 2 →
      KD264Lie.fieldSize d.1 = 8 → ¬ 1056706560 ∣ lieOrderFormula d.1) : LieSEightNoAt P := by
  rintro Y _ _ - - - d hd hc hf ⟨e⟩ α - - -
  refine lieSEight_not_comp_of_not_dvd hLO ?_
  rw [hLO d (Y ⧸ Subgroup.center Y) ⟨e⟩]
  exact h d hd hc hf

theorem lieSEight_false_of_rkY_of_four_le {Y R : Type} [Group Y] [Finite Y] [Group R] [Finite R]
    (hRk : RkY Y) (hZ : ¬ 3 ∣ Nat.card (Subgroup.center Y))
    (θ : Y ⧸ Subgroup.center Y ≃* R) (hk : 4 ≤ CFSG.Open.twoLocalPrimeRank 3 R) : False := by
  obtain ⟨E, hE, hEcard, T, hT2, hTc, hET⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.noncentralWitness_of_le_twoLocalPrimeRank θ
      Nat.prime_three hZ (by norm_num) hk
  have hT : T ≠ ⊥ := fun h => hTc (h ▸ bot_le)
  have hEZ : E ⊓ Subgroup.center Y = ⊥ := by
    have h1 : Nat.card ↥(E ⊓ Subgroup.center Y) ∣ 3 ^ 4 := by
      rw [← hEcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(E ⊓ Subgroup.center Y) ∣ Nat.card (Subgroup.center Y) :=
      Subgroup.card_dvd_of_le inf_le_right
    have hcop : Nat.Coprime (3 ^ 4) (Nat.card (Subgroup.center Y)) :=
      Nat.Coprime.pow_left 4 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hZ)
    exact Subgroup.eq_bot_of_card_eq _ (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have h3 := (hRk T hT hT2 E hET hE).2 hEZ
  rw [hEcard] at h3
  norm_num at h3

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
