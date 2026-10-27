module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.A7Data
public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour

open Equiv Equiv.Perm CFSG.Open CFSG.Quasithin

@[expose] def A7Good (P : Subgroup A7) : Prop :=
  ∃ H : Subgroup A7, IsSimpleGroup ↥H ∧ (∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a) ∧ P ≤ H ∧
    ¬ 2 ∣ (P.subgroupOf H).index

theorem card_A7 : Nat.card A7 = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem not_dvd_index {P H : Subgroup A7} (hPH : P ≤ H) {a b : ℕ} (ha : Nat.card ↥P = a)
    (hb : Nat.card ↥H = b) (hodd : ∀ k, k * a = b → ¬ 2 ∣ k) : ¬ 2 ∣ (P.subgroupOf H).index := by
  have h := Subgroup.relIndex_mul_card (H := P) (K := H)
  rw [inf_eq_left.mpr hPH, ha, hb] at h
  exact hodd _ h

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour
