module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalData
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6TwoCodes
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.KGroups.Sp6 CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

theorem inner_of_card_le_two_mul {X : Type*} [Group X] [Finite X]
    (hZ : ∀ k : X, (∀ x : X, k * x = x * k) → k = 1)
    (hcard : Nat.card (MulAut X) ≤ 2 * Nat.card X) (φ : MulAut X) {m : ℕ}
    (hm : φ ^ (2 * m + 1) = 1) : ∃ g : X, ∀ x : X, φ x = g * x * g⁻¹ := by
  set I := (MulAut.conj : X →* MulAut X).range
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    rw [Subgroup.mem_bot]
    apply hZ
    intro x
    have h := congrArg (fun α : MulAut X => α x) (MonoidHom.mem_ker.mp hk)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc k * x = (k * x * k⁻¹) * k := by group
      _ = x * k := by rw [h]
  have hI : Nat.card I = Nat.card X := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hpos : 0 < Nat.card X := Nat.card_pos
  have hidx : I.index = 1 ∨ I.index = 2 := by
    have h := I.card_mul_index
    rw [hI] at h
    have h1 : 1 ≤ I.index := Nat.one_le_iff_ne_zero.mpr (Subgroup.index_ne_zero_of_finite)
    have h2 : I.index ≤ 2 := by nlinarith
    omega
  have hφ : φ ∈ I := by
    rcases hidx with h1 | h2
    · rw [Subgroup.index_eq_one.mp h1]
      exact Subgroup.mem_top φ
    · have hsq : φ ^ (2 * m) ∈ I := by
        rw [pow_mul]
        exact Subgroup.pow_mem _ (Subgroup.sq_mem_of_index_two h2 φ) m
      have h : φ = (φ ^ (2 * m))⁻¹ * φ ^ (2 * m + 1) := by group
      rw [h, hm, mul_one]
      exact I.inv_mem hsq
  obtain ⟨g, rfl⟩ := hφ
  exact ⟨g, fun x => MulAut.conj_apply g x⟩

theorem conjC_cA_cZ : conjC cA cZ = mulC (mulC (mulC (mulC cW0 cW0) cW1) cW2) cW2 := by decide

theorem not_inZ_cAz : inZ (mulC (mulC (mulC (mulC cW0 cW0) cW1) cW2) cW2) = false := by decide

theorem not_inZ_cAz2 : inZ (mulC (mulC (mulC (mulC (mulC cW0 cW0) cW1) cW2) cW2)
    (mulC (mulC (mulC (mulC cW0 cW0) cW1) cW2) cW2)) = false := by decide

theorem genB_cA' : genB cA = true := by decide

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
