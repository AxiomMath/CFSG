module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.Arith
public import CFSG.Blueprint.EvenStandardExact
import CFSG.Adapters.LieModelOrders
import CFSG.Sporadic.He.Simple
import CFSG.Monster.Existence.Compat.Sp8
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionTypeExceptions

public section

namespace CFSG.EvenSporadicStandard.Induction.Thm54Reach

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank

section


theorem not_evenStandardException_of_card {Y : Type} [Group Y] (hge : 29120 ≤ Nat.card Y)
    (hHe : Nat.card Y ≠ 4030387200) : ¬ Recognition.Exact.EvenStandardException Y := by
  classical
  rintro (h1 | h1 | h1 | ⟨K, _, _, hK, ⟨e⟩⟩ | ⟨K, _, _, hK, ⟨e⟩⟩ | h1 | h1 | h1)
  · rw [LieModel.card_eq_lieOrd (by norm_num) h1] at hge
    exact absurd hge (by decide)
  · rw [LieModel.card_eq_lieOrd (by norm_num) h1] at hge
    exact absurd hge (by decide)
  · rw [LieModel.card_eq_lieOrd (by norm_num) h1] at hge
    exact absurd hge (by decide)
  ·
    have hK2 : Nat.card K = 2 := by rw [Nat.card_eq_fintype_card, hK]
    let φ : Matrix.symplecticGroup (Fin 2) K ≃* Matrix.symplecticGroup (Fin 2) (ZMod 2) :=
      CFSG.Monster.Existence.Compat.sympMapEquiv
        (CFSG.Monster.Existence.Compat.ringEquivZMod2 hK2)
    have hmap : (commutator (Matrix.symplecticGroup (Fin 2) K)).map φ.toMonoidHom =
        commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.2 φ.surjective, ← _root_.commutator_def]
    have e6 : Y ≃* alternatingGroup (Fin 6) :=
      e.trans (((φ.subgroupMap (commutator (Matrix.symplecticGroup (Fin 2) K))).trans
        (MulEquiv.subgroupCongr hmap)).trans
        CFSG.ComponentClassification.StandardRecognition.symplecticCommutatorEquivAlternating)
    have h360 : Nat.card Y = 360 := by
      rw [Nat.card_congr e6.toEquiv, nat_card_alternatingGroup,
        Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num
    omega
  ·
    have hK2 : Nat.card K = 2 := by rw [Nat.card_eq_fintype_card, hK]
    have hH : Nat.card (Chevalley.adjointGroup .G2 K) = 12096 := by
      rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK2]
      rfl
    have : Finite (Chevalley.adjointGroup .G2 K) :=
      Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
    have hle : Nat.card Y ≤ 12096 := by
      rw [Nat.card_congr e.toEquiv, ← hH]
      refine Subgroup.card_le_of_le (Subgroup.commutator_le.2 fun a ha c hc => ?_)
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hc) (inv_mem ha)) (inv_mem hc)
    omega
  · rw [LieModel.card_eq_lieOrd (by norm_num) h1] at hge
    exact absurd hge (by decide)
  · rw [LieModel.card_eq_lieOrd (by norm_num) h1] at hge
    exact absurd hge (by decide)
  ·
    obtain ⟨e⟩ := h1
    apply hHe
    rw [Nat.card_congr e.toEquiv]
    change Nat.card CFSG.Blueprint.NativeSporadic.He = 4030387200
    exact CFSG.Sporadic.He.card_He

theorem not_evenStandardException_of_thm54Order {Y : Type} [Group Y]
    (hc : Thm54Order (Nat.card Y)) : ¬ Recognition.Exact.EvenStandardException Y :=
  not_evenStandardException_of_card hc.ge hc.ne_he

end

end CFSG.EvenSporadicStandard.Induction.Thm54Reach
