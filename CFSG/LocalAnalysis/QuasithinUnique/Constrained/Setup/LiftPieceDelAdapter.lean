module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceAdapterCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelDecomp

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Lift.Piece CFSG.QuasithinUnique.Setup.Campbell

theorem delAdapterProp : DelAdapterProp := by
  intro G _ _ R M V n F _ r Lc ctx i Fs P hcore hbase hseed hH0 hmin hbasic himage hW hres
  classical
  have hSP : baum R ≤ P := hbasic.lt.le
  have hcard2 : Nat.card (ZMod 2) = 2 ^ 1 := by simp
  obtain ⟨hchi, -, hAlt, hE, hUK, hcent, hcardU⟩ := adapter_core (k := ZMod 2) (S := baum R)
    (P := P) (M := M) (W := modComm V Fs) hSP hW.W_le_S hbase.base.B_S hres.P_eq
    hbasic.charTwo hbasic.noChar le_rfl hcard2 hW.setting hW.thompson_ne
  obtain ⟨hA3, ⟨e⟩, hc3⟩ := hAlt rfl
  have hBP : oddOrderSubgroup P ≤ P := oddOrderSubgroup_le P
  have hWn : P ≤ Subgroup.normalizer (modComm V Fs : Set G) := hW.reduced.2.1
  have hUW : ⁅blockQ P, oddOrderSubgroup P⁆ ≤ modComm V Fs := by
    rw [hE]
    exact commutator_le_left_of_normalizes (hBP.trans hWn)
  have hU1 : (⁅blockQ P, oddOrderSubgroup P⁆ : Subgroup G) ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have h1 : x ∈ modComm V Fs ⊓ Subgroup.centralizer (oddOrderSubgroup P : Set G) :=
      ⟨hUW hx.1, Subgroup.centralizer_le hBP hx.2⟩
    rw [hres.fixed] at h1
    exact h1
  have hcardU' : Nat.card ↥(⁅blockQ P, oddOrderSubgroup P⁆ : Subgroup G) = 4 := by
    rw [hcardU, hU1, Subgroup.card_bot, hcard2]
    norm_num
  have hUeq : (⁅blockQ P, oddOrderSubgroup P⁆ : Subgroup G) = modComm V Fs :=
    Subgroup.eq_of_le_of_card_ge hUW (by rw [hW.card, hcardU'])
  have hcardB : Nat.card ↥(oddOrderSubgroup P) = 12 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hcardQ : Nat.card ↥(blockQ (oddOrderSubgroup P)) = 4 := by
    rw [blockQ_eq_map, Subgroup.card_map_of_injective (oddOrderSubgroup P).subtype_injective]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (CFSG.pCore 2 ↥(oddOrderSubgroup P))
    rw [hcardB, hc3] at h1
    omega
  have hWQ : modComm V Fs ≤ blockQ (oddOrderSubgroup P) := by
    rw [← hUeq, ← hUK]
    exact commutator_le_left_of_normalizes (le_normalizer_blockQ (oddOrderSubgroup P))
  refine ⟨hchi, hA3, ⟨e⟩, ?_, ?_, hUeq⟩
  · rw [hUeq] at hcent
    exact hcent
  · exact (Subgroup.eq_of_le_of_card_ge hWQ (by rw [hcardQ, hW.card])).symm

end CFSG.QuasithinUnique.Setup.Lift
