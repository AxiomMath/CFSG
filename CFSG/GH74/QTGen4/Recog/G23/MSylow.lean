module

public import CFSG.Quasithin.Recognition.G23TypeDefs
public import CFSG.Quasithin.Background.A1aFStar
public meta import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G23Type
open scoped MatrixGroups

variable {G : Type*} [Group G]

theorem card_SL3_two : Nat.card (SL(3, ZMod 2)) = 168 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem G23Two.card_quotient {M : Subgroup G} (hM : G23Two M) :
    Nat.card (M ⧸ (quasithinGenFitting M).subgroupOf M) = 168 := by
  obtain ⟨θ, hθs, hθk⟩ := hM.quot
  rw [← hθk, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hθs).toEquiv,
    card_SL3_two]

theorem G23Two.card_group [Finite G] {M : Subgroup G} (hM : G23Two M) :
    Nat.card M = 1344 := by
  have hle : quasithinGenFitting M ≤ M := CFSG.Quasithin.quasithinGenFitting_le M
  have hK : Nat.card ↥((quasithinGenFitting M).subgroupOf M) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hM.card]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((quasithinGenFitting M).subgroupOf M),
    G23Two.card_quotient hM, hK]

theorem G23Two.card_sylow [Finite G] {M T : Subgroup G} (hM : G23Two M) (hTM : T ≤ M)
    (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ (T.subgroupOf M).index) :
    Nat.card T = 64 := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT2
  have hmul := Subgroup.card_mul_index (T.subgroupOf M)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv, G23Two.card_group hM, hn] at hmul
  have hle : 2 ^ n ≤ 1344 := Nat.le_of_dvd (by norm_num) (Dvd.intro _ hmul)
  have hn11 : n < 11 := by
    by_contra h
    have h2 : 2 ^ 11 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (not_lt.mp h)
    have h3 : (2 : ℕ) ^ 11 = 2048 := by norm_num
    omega
  have h64 : 2 ^ n = 64 := by
    interval_cases n <;> norm_num at hmul ⊢ <;> omega
  rw [hn]
  exact h64

end CFSG.GH74.QTGen4.Recog.G23
