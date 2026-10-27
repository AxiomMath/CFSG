module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LeavesR
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Cl1Bridge

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

theorem inSA_of_properFixedComp (hC : ClosureLeaves) {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hS : Catalog S) {σ : MulAut S} {P : Subgroup S} (hP : ProperFixedComp σ P)
    (h : InSA (P ⧸ center P)) :
    InSA S ∧ Nat.card (P ⧸ center P) < Nat.card S := by
  unfold InSA at h ⊢
  obtain ⟨_, h20, hodd, hL34, _, _, _⟩ := h
  have hPne : P ≠ ⊤ := hP.2.2.1
  haveI : Nonempty ↥P := ⟨⟨1, P.one_mem⟩⟩
  have hcardP : Nat.card ↥P < Nat.card S := by
    rw [← P.card_mul_index]
    exact lt_mul_of_one_lt_right Nat.card_pos (P.one_lt_index_of_ne_top hPne)
  have hdvd : Nat.card (P ⧸ center P) ∣ Nat.card ↥P :=
    Subgroup.card_quotient_dvd_card (center ↥P)
  have hle : Nat.card (P ⧸ center P) ≤ Nat.card ↥P := Nat.le_of_dvd Nat.card_pos hdvd
  have hlt : Nat.card (P ⧸ center P) < Nat.card S := lt_of_le_of_lt hle hcardP
  refine ⟨⟨hS, by omega, ?_, ?_, ?_, ?_, ?_⟩, hlt⟩
  ·
    intro r hr hr2 hChev
    rcases cl1_of_gls3 hC.cl1 hP hr hr2 hChev with h' | h'
    · exact hodd r hr hr2 h'
    · have h504 : Nat.card (P ⧸ center P) = 504 := by
        rw [GH74.card_of_lieModel_PSL (G := P ⧸ center P) (n := 2) (p := 2) (f := 3)
          (by norm_num) h']
        decide
      omega
  ·
    intro h342
    have hS20160 : Nat.card S = 20160 := by
      rw [GH74.card_of_lieModel_PSL (G := S) (n := 3) (p := 2) (f := 2) (by norm_num) h342]
      decide
    omega
  ·
    intro hHe
    rcases hC.cl3 S (Or.inr (Or.inl hHe)) σ P hP with hsmall | hL34'
    · omega
    · exact hL34 hL34'
  ·
    intro hM12
    rcases hC.cl3 S (Or.inr (Or.inr (Or.inl hM12))) σ P hP with hsmall | hL34'
    · omega
    · exact hL34 hL34'
  ·
    intro hJ2
    rcases hC.cl3 S (Or.inr (Or.inr (Or.inr hJ2))) σ P hP with hsmall | hL34'
    · omega
    · exact hL34 hL34'

end CFSG.OddStandard.SmallF3.HypA2
