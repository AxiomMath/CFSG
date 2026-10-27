module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFSporBTh
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFSporBCo2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFSporBCo3
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFSporBMcL
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFSporBJ4
public import CFSG.Sporadic.Bridge.ThSurj
public import CFSG.Sporadic.Presentation.Co2Exact
public import CFSG.Sporadic.Bridge.Co3Surj
public import CFSG.Sporadic.Presentation.McLExact
public import CFSG.Sporadic.Bridge.J4Surj
public import CFSG.RankThree.PartOne.SPOR.Outer
public import CFSG.Sporadic.Co2Schreier.FullAut
public import CFSG.RankThree.PartOne.KP.Co3Aut
public import CFSG.RankThree.PartTwo.Sec4.Item47Native
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKF

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.Blueprint

theorem kdSporB_Th
    {Z : Type} [Group Z] [Finite Z] (K : Subgroup Z) [K.Normal]
    (eK : ↥K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Th).Group)
    (hC : Subgroup.centralizer (K : Set Z) = ⊥) : OneClassE 5 Z := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  have e : ↥K ≃* NativeSporadic.Th := eK.trans b.symm
  have hOut : ¬ 5 ∣ Nat.card (Outer NativeSporadic.Th) := by
    rw [CFSG.RankThree.PartOne.SPOR.card_outer_Th_native]
    norm_num
  have hOne : OneClassE 5 NativeSporadic.Th := thFive_oneClassE
  have hp : Nat.Prime 5 := by norm_num
  exact @oneClassE_of_model 5 hp Z _ _ K _ hC NativeSporadic.Th Units.instGroup e hOut hOne

theorem kdSporB_Co2
    {Z : Type} [Group Z] [Finite Z] (K : Subgroup Z) [K.Normal]
    (eK : ↥K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Co2).Group)
    (hC : Subgroup.centralizer (K : Set Z) = ⊥) : OneClassE 5 Z := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
  have e : ↥K ≃* NativeSporadic.Co2 := eK.trans b.symm
  have hall := CFSG.Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner_model
    (K := NativeSporadic.Co2) (MulEquiv.refl NativeSporadic.Co2)
  have hOut : ¬ 5 ∣ Nat.card (Outer NativeSporadic.Co2) := by
    rw [CFSG.RankThree.PartOne.SPOR.card_outer_eq_one_of_allInner hall]
    norm_num
  have hOne : OneClassE 5 NativeSporadic.Co2 := co2Five_oneClassE
  have hp : Nat.Prime 5 := by norm_num
  exact @oneClassE_of_model 5 hp Z _ _ K _ hC NativeSporadic.Co2 Units.instGroup e hOut hOne

theorem kdSporB_Co3
    {Z : Type} [Group Z] [Finite Z] (K : Subgroup Z) [K.Normal]
    (eK : ↥K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Co3).Group)
    (hC : Subgroup.centralizer (K : Set Z) = ⊥) : OneClassE 5 Z := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
  have e : ↥K ≃* NativeSporadic.Co3 := eK.trans b.symm
  have hOut : ¬ 5 ∣ Nat.card (Outer NativeSporadic.Co3) := by
    rw [CFSG.RankThree.PartOne.CTUC_Co3_all_automorphisms_inner.{0}.2.2.2.1]
    norm_num
  have hOne : OneClassE 5 NativeSporadic.Co3 := co3Five_oneClassE
  have hp : Nat.Prime 5 := by norm_num
  exact @oneClassE_of_model 5 hp Z _ _ K _ hC NativeSporadic.Co3 Units.instGroup e hOut hOne

theorem kdSporB_McL
    {Z : Type} [Group Z] [Finite Z] (K : Subgroup Z) [K.Normal]
    (eK : ↥K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.McL).Group)
    (hC : Subgroup.centralizer (K : Set Z) = ⊥) : OneClassE 5 Z := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  have e : ↥K ≃* NativeSporadic.McL := eK.trans b.symm
  haveI : Finite NativeSporadic.McL :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.McL.card_McL]; norm_num)
  have hOut : ¬ 5 ∣ Nat.card (Outer NativeSporadic.McL) := by
    have h2 := CFSG.RankThree.PartTwo.Sec4.card_outer_McL
    have hpos : 0 < Nat.card (Outer NativeSporadic.McL) := Nat.card_pos
    intro hd
    have := Nat.le_of_dvd hpos hd
    omega
  have hOne : OneClassE 5 NativeSporadic.McL := mclFive_oneClassE
  have hp : Nat.Prime 5 := by norm_num
  exact @oneClassE_of_model 5 hp Z _ _ K _ hC NativeSporadic.McL Units.instGroup e hOut hOne

theorem kdSporB_J4
    {Z : Type} [Group Z] [Finite Z] (K : Subgroup Z) [K.Normal]
    (eK : ↥K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J4).Group)
    (hC : Subgroup.centralizer (K : Set Z) = ⊥) : OneClassE 11 Z := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  have e : ↥K ≃* NativeSporadic.J4 := eK.trans b.symm
  have hOut : ¬ 11 ∣ Nat.card (Outer NativeSporadic.J4) := by
    intro hd
    rcases (@CFSG.Sporadic.J4Schreier.R3E_J4_outer_automorphism_group_no_large_primes
      NativeSporadic.J4 Units.instGroup ⟨MulEquiv.refl _⟩).1 11 (by norm_num) hd
      with h | h <;> omega
  have hOne : OneClassE 11 NativeSporadic.J4 := j4Eleven_oneClassE
  have hp : Nat.Prime 11 := by norm_num
  exact @oneClassE_of_model 11 hp Z _ _ K _ hC NativeSporadic.J4 Units.instGroup e hOut hOne

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKF
