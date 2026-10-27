module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndNat
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.CGT6M.FiveYSide
public import CFSG.CGT.PushingUpLit.CGT6X.End3Mod
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512DeltaA

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End4

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
  CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6X.End3
  CFSG.CGT.PushingUpLit.CGT6M
open CFSG.Open (StatedClassicalModel)

section Bound

variable {V : Type} [CommGroup V] [Finite V]

theorem card_models_sixteen_l34 :
    Nat.card (Multiplicative (Fin 2 → Fq 2)) = 16 ∧ Nat.card ↥(G6.coreMod 5) = 16 := by
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → Fq 2) ≃ _), Nat.card_fun,
      GaloisField.card 2 2 (by norm_num)]
    simp
  · rw [Quasithin.X1512.card_coreMod (Or.inr rfl)]
    norm_num

theorem card_commV_le_sixteen_l34 (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    (hperf : ⁅Y, Y⁆ = Y)
    (hcls : InClassX ↥(yuHol Y) ∨
      ∃ n : ℕ, 2 ≤ n ∧ IsNatSectionBy (omegaMinusAct n) Y (commV Y) ⊥)
    (hY : YSL Y 2) : Nat.card ↥(commV Y) ≤ 2 ^ 4 * Nat.card ↥(commV Y ⊓ fixV Y) := by
  rcases hcls with hX | ⟨n, hn, hΩ⟩
  · obtain ⟨h16, h5⟩ := card_models_sixteen_l34
    rcases natSection_of_classX hV hperf hX le_rfl hY with hsl | ⟨-, halt⟩
    · exact card_commV_le_sixteen_of_isNatSectionBy (slAct 2) Y h16 hsl
    · exact card_commV_le_sixteen_of_isNatSectionBy (altAct 5) Y h5 halt
  · have := not_natOmegaMinus_of_ysl (f := 2) (by norm_num) (by omega) hY hΩ
    omega

end Bound

end CFSG.CGT.PushingUpLit.CGT6X.End4
