module

public import CFSG.LocalAnalysis.RankThreeUC.K37HGONGen
public import CFSG.HardMathSupport.Solomon.Coordinator.ON25Top
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCSylow
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCoverCert
public import CFSG.LocalAnalysis.RankThreeUC.K37HDefs
public import CFSG.LocalAnalysis.RankThreeUC.K37HGKit

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.S15.K37
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma59Ns (InputONSylow)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (gammaLBelow)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

theorem k37Rest₁₄_of_inputs (hSyl : InputONSylow)
    (hGen : ∀ (Y : Type) [Group Y] [Finite Y], IsHatON Y → ∀ B₀ : Subgroup Y,
      IsElemAbelian 3 B₀ → Nat.card B₀ = 27 → (⊤ : Subgroup Y) ≤ gammaLBelow B₀ ⊤)
    (hMult : ∀ (Y : Type) [Group Y] [Finite Y], CFSG.IsQuasisimple Y →
      Nonempty (Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.sporadic .ONan).Group) →
        Nat.card (Subgroup.center Y) ∣ 3)
    (hOut : ∀ (S : Type) [Group S],
      Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic .ONan).Group) → ¬ 3 ∣ Nat.card (Outer S)) :
    K37Rest₁₄ := by
  intro X _ _ K E S hs hO
  exfalso
  obtain ⟨-, h3, ⟨e⟩⟩ := hO
  have hZ3 : Nat.card (Subgroup.center ↥K) = 3 := Nat.dvd_antisymm (hMult ↥K hs.quasi ⟨e⟩) h3
  have hHat : IsHatON ↥K := ⟨Group.isPerfect_def.mp hs.quasi.1, hZ3, ⟨e⟩⟩
  have hout : ¬ 3 ∣ Nat.card (Outer (↥K ⧸ Subgroup.center ↥K)) := hOut _ ⟨e⟩
  have hEK := k37G_E_le hs hSyl hHat hout
  exact k37G_false_of_le_centGenI hs (k37G_le_centGenI_of_E_le hs hEK hZ3 (hGen ↥K hHat))

section Certified


private theorem k37G_card_center_dvd_three_ON (Y : Type) [Group Y] [Finite Y]
    (hq : CFSG.IsQuasisimple Y)
    (he : Nonempty (Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.sporadic .ONan).Group)) :
    Nat.card (Subgroup.center Y) ∣ 3 := by
  obtain ⟨e⟩ := he
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b' : CFSG.Blueprint.NativeSporadic.Carrier .ONan ≃*
      (TauCeti.CFSGIndex.sporadic .ONan).Group := b
  have h := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq (e.trans b'.symm)
  rwa [CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCover.nativeRow_ONan] at h

private theorem k37G_not_three_dvd_outer_ON (S : Type) [Group S]
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic .ONan).Group)) :
    ¬ 3 ∣ Nat.card (Outer S) := by
  obtain ⟨e⟩ := he
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b' : CFSG.Blueprint.NativeSporadic.Carrier .ONan ≃*
      (TauCeti.CFSGIndex.sporadic .ONan).Group := b
  have h := (CFSG.Sporadic.ONOddCore.r3e_on_outer_order_divides_four).1
  have hcard : Nat.card (Outer S) =
      Nat.card (Outer (CFSG.Blueprint.NativeSporadic.Carrier .ONan)) :=
    Nat.card_congr (equivalence (e.trans b'.symm)).toEquiv
  have h' : Nat.card (Outer S) ∣ 4 := by
    rw [hcard]
    exact h
  exact fun h3 => absurd (h3.trans h') (by norm_num)

theorem k37Rest₁₄_holds : K37Rest₁₄ :=
  k37Rest₁₄_of_inputs CFSG.HardMathSupport.Solomon.Coordinator.inputONSylow_holds
    (fun Y _ _ => CFSG.HardMathSupport.Solomon.Coordinator.input23_25_2Facts_on1_holds Y)
    (fun Y _ _ hq he => k37G_card_center_dvd_three_ON Y hq he)
    fun S _ he => k37G_not_three_dvd_outer_ON S he

end Certified

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H

end
