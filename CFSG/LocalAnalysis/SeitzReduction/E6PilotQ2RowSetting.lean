module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotMainSetup
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3Setup

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.SeitzReduction.F4Pilot (F4Work)


theorem not_evenStandardException_of_card_eq_ordE6_two {Q : Type} [Group Q]
    (hQ : Nat.card Q = ordE6 2) : ¬ Recognition.Exact.EvenStandardException Q := by
  classical
  have hQ' : Nat.card Q = 214841575522005575270400 := by rw [hQ]; decide
  rintro (h1 | h1 | h1 | ⟨K, _, _, hK, ⟨e⟩⟩ | ⟨K, _, _, hK, ⟨e⟩⟩ | h1 | h1 | h1)
  · rw [EvenSmallLie.Child3.card_of_lieModel_classical (by norm_num) h1] at hQ'
    exact absurd hQ' (by decide)
  · rw [EvenSmallLie.Child3.card_of_lieModel_classical (by norm_num) h1] at hQ'
    exact absurd hQ' (by decide)
  · rw [EvenSmallLie.Child3.card_of_lieModel_classical (by norm_num) h1] at hQ'
    exact absurd hQ' (by decide)
  · have hle : Nat.card Q ≤ Fintype.card K ^ 16 := by
      rw [Nat.card_congr e.toEquiv]
      calc Nat.card (commutator (Matrix.symplecticGroup (Fin 2) K))
          ≤ Nat.card (Matrix.symplecticGroup (Fin 2) K) := Subgroup.card_le_card_group _
        _ ≤ Nat.card (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :=
            Nat.card_le_card_of_injective _ Subtype.val_injective
        _ = Fintype.card K ^ 16 := by
            rw [Matrix, Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := K)]
            simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin]
            ring
    rw [hQ', hK] at hle
    exact absurd hle (by norm_num)
  · have hK2 : Nat.card K = 2 := by rw [Nat.card_eq_fintype_card, hK]
    have hH : Nat.card (adjointGroup .G2 K) = 12096 := by
      rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK2]
      rfl
    have : Finite (adjointGroup .G2 K) := Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
    have hle : Nat.card Q ≤ 12096 := by
      rw [Nat.card_congr e.toEquiv, ← hH]
      refine Subgroup.card_le_of_le (Subgroup.commutator_le.2 fun a ha c hc => ?_)
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hc) (inv_mem ha)) (inv_mem hc)
    rw [hQ'] at hle
    exact absurd hle (by norm_num)
  · rw [EvenSmallLie.Child3.card_of_lieModel_classical (by norm_num) h1] at hQ'
    exact absurd hQ' (by decide)
  · rw [EvenSmallLie.Child3.card_of_lieModel_classical (by norm_num) h1] at hQ'
    exact absurd hQ' (by decide)
  · obtain ⟨e⟩ := h1
    rw [Nat.card_congr e.toEquiv] at hQ'
    change Nat.card CFSG.Blueprint.NativeSporadic.He = _ at hQ'
    rw [CFSG.Sporadic.He.card_He] at hQ'
    exact absurd hQ' (by norm_num)

theorem seitzSetting_of_f4Work_E6_two {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {K : Type} [Field K] {t : G} (hw : F4Work L K t 1) (e : L ≃* adjointGroup .E6 K) :
    SeitzSetting G L := by
  have hZ := hw.center_eq_bot
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have : IsSimpleGroup G := hw.standard.simple
  have hLM : LieModel L .E6 0 2 1 := lieModel_of_mulEquiv_E6 le_rfl hw.card_eq e
  have hLMq : LieModel (L ⧸ center L) .E6 0 2 1 :=
    lieModel_of_mulEquiv (quotientCenterMulEquiv hZ).symm hLM
  have hcard : Nat.card (L ⧸ center L) = ordE6 2 := by
    rw [Nat.card_congr (quotientCenterMulEquiv hZ).toEquiv, Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6, hw.card_eq, pow_one]
  obtain ⟨S, hS⟩ := hw.standard.cyclic
  exact seitzSetting_of hw.standard.nonab hw.standard.kProper hw.standard.standard
    hw.standard.core S hS (Or.inl ⟨.E6, 0, 1, ⟨Nat.prime_two, le_rfl, rfl⟩, hLMq⟩)
    (not_evenStandardException_of_card_eq_ordE6_two hcard) hZ

end CFSG.SeitzReduction.E6Pilot
