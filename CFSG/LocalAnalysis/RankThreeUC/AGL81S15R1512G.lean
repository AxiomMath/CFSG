module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PerfectSolv
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsGroup
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Open
open scoped commutatorElement

section Interface1510

variable {X : Type} [Group X] [Finite X]

theorem mem_of_pElement_sup_of_le_centralizer {Y : Type} [Group Y] [Finite Y] {A W : Subgroup Y}
    {q : ℕ} (hq : q.Prime) (hAW : A ≤ Subgroup.centralizer (W : Set Y)) (hW : ¬ q ∣ Nat.card W)
    {x : Y} (hx : x ∈ A ⊔ W) {k : ℕ} (hk : orderOf x = q ^ k) : x ∈ A := by
  have hLE : A ≤ Subgroup.normalizer (W : Set Y) :=
    hAW.trans (Subgroup.centralizer_le_normalizer _)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A W hLE] at hx
  obtain ⟨l, hl, w, hw, rfl⟩ := hx
  have hc : Commute l w := ((Subgroup.mem_centralizer_iff.1 (hAW hl)) w hw).symm
  have hwm : w ^ Nat.card W = 1 := by
    have h1 : (⟨w, hw⟩ : ↥W) ^ Nat.card W = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h1
  have hlm : (l * w) ^ Nat.card W ∈ A := by
    rw [hc.mul_pow, hwm, mul_one]
    exact Subgroup.pow_mem _ hl _
  have hcop : Nat.Coprime (Nat.card W) (orderOf (l * w)) := by
    rw [hk]
    exact ((Nat.Prime.coprime_iff_not_dvd hq).2 hW).symm.pow_right k
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  have hfin : l * w ∈ A := by
    rw [← hj]
    exact Subgroup.pow_mem _ hlm j
  exact hfin

end Interface1510

end CFSG.LocalAnalysis.RankThreeUC.S15
