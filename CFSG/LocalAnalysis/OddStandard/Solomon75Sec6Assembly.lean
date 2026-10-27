module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Defs

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

theorem sec6_normalizer_ne_top_of_odd {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {W : Subgroup X} (hodd : Odd (Nat.card ↥W)) (hne : W ≠ ⊥) {t : X} (ht : orderOf t = 2) :
    normalizer (W : Set X) ≠ ⊤ := by
  intro htop
  haveI : W.Normal := normalizer_eq_top_iff.1 htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W with hb | htW
  · exact hne hb
  · rw [htW, Subgroup.card_top] at hodd
    have h2 : 2 ∣ Nat.card X := ht ▸ orderOf_dvd_natCard t
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

theorem oddCoreOf_cen_le_sec6Sig {X : Type} [Group X] {n : ℕ} {t b : X}
    (hb : b ∈ Sec6M X n (cen t)) (hb2 : orderOf b = 2) : oddCoreOf (cen b) ≤ sec6Sig X n t :=
  (le_iSup (fun _ : orderOf b = 2 => oddCoreOf (cen b)) hb2).trans
    (le_iSup₂ (f := fun y (_ : y ∈ Sec6M X n (cen t)) => ⨆ (_ : orderOf y = 2), oddCoreOf (cen y))
      b hb)

end CFSG.OddStandard.Solomon75
