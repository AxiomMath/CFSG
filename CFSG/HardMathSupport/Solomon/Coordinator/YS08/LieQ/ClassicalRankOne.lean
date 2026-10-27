module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Suzuki
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsStated
import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits
open scoped MatrixGroups

theorem fusionIsBenderGroup_of_statedPSL_two {S : Type} [Group S] {f : ℕ}
    (h : StatedClassicalModel S .PSL 2 2 f) : fusionIsBenderGroup S := by
  obtain ⟨⟨-, hf1, -, hne, -⟩, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  have hf2 : 2 ≤ f := by
    by_contra hlt
    obtain rfl : f = 1 := by omega
    exact hne (by simp)
  have hcard' : Nat.card K = Nat.card (GaloisField 2 f) := by
    rw [hcard, GaloisField.card 2 f (by omega)]
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  let θ : K ≃+* GaloisField 2 f := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
    exact hcard')
  exact Or.inl ⟨f, hf2, ⟨e.trans (CFSG.ComponentClassification.AutL2Facts.statedEquiv θ)⟩⟩

theorem fusionIsBenderGroup_of_statedPSU_three {S : Type} [Group S] {f : ℕ}
    (h : StatedClassicalModel S .PSU 3 2 f) : fusionIsBenderGroup S := by
  obtain ⟨⟨-, hf1, -, hne⟩, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  have hf2 : 2 ≤ f := by
    by_contra hlt
    obtain rfl : f = 1 := by omega
    exact hne (by simp)
  have hcard' : Nat.card K = 2 ^ (2 * f) := by
    rw [hcard, ← pow_mul, mul_comm]
  exact Or.inr (Or.inl ⟨f, hf2,
    ⟨e.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative f hf2 hcard')⟩⟩)

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
