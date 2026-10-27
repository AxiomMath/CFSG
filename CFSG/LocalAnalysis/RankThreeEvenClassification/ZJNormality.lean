module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ZJGrowthExtension

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem thompsonCenterOf_normal_of_stable_normal_actions {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hodd : Odd prime) (sylow : Sylow prime G)
    (hcharacteristic : Subgroup.centralizer (pCore prime G : Set G) ≤ pCore prime G)
    (hstable : StableNormalPrimeActions prime G) : (thompsonCenterOf (sylow : Subgroup G)).Normal := by
  classical
  let center := thompsonCenterOf (sylow : Subgroup G)
  let orders := {order : ℕ | ∃ kernel : Subgroup G, kernel.Normal ∧ kernel ≤ center ∧ Nat.card kernel = order}
  have hnonempty : orders.Nonempty := ⟨1, ⊥, inferInstance, bot_le, Subgroup.card_bot⟩
  have hbounded : BddAbove orders := by
    refine ⟨Nat.card center, ?_⟩
    rintro order ⟨kernel, _, hle, rfl⟩
    exact Subgroup.card_le_of_le hle
  obtain ⟨kernel, hnormal, hle, hcard⟩ := Nat.sSup_mem hnonempty hbounded
  have heq : kernel = center := by
    by_contra hne
    have hproper : kernel < center := lt_of_le_of_ne hle hne
    have : kernel.Normal := hnormal
    obtain ⟨extension, hextensionNormal, hstrict, hextensionLe⟩ :=
      zj_growth_extension prime hprime hodd sylow kernel hproper hcharacteristic hstable
    have hmem : Nat.card extension ∈ orders := ⟨extension, hextensionNormal, hextensionLe, rfl⟩
    have hbound := le_csSup hbounded hmem
    have hcardLt := subgroup_card_lt_of_lt kernel extension hstrict
    rw [hcard] at hcardLt
    omega
  change center.Normal
  exact heq ▸ hnormal

end CFSG.RankThreeEvenClassification.Helpers
