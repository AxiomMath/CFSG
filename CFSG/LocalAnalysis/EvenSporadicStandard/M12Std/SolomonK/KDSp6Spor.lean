module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.BasicSylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.P1ThreeSporOrders

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def SporadicNoE64 : Prop :=
  ∀ s : TauCeti.SporadicName, (s = .HS ∨ s = .ONan) →
    ∀ E : Subgroup (Carrier s), (∀ x ∈ E, x * x = 1) → Nat.card E ≠ 2 ^ 6

private theorem factorization_two_eq_nine_iff {m : ℕ} (hm : m ≠ 0) :
    m.factorization 2 = 9 ↔ 2 ^ 9 ∣ m ∧ ¬ 2 ^ 10 ∣ m := by
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm,
    Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm]
  constructor <;> intro h <;> omega

theorem sporadic_two_part (s : TauCeti.SporadicName)
    (h : (CFSG.AGLEmbedding.sporOrd s).factorization 2 = 9) : s = .HS ∨ s = .ONan := by
  cases s <;> simp only [CFSG.AGLEmbedding.sporOrd] at h
  all_goals rw [factorization_two_eq_nine_iff (by norm_num)] at h
  all_goals norm_num at h
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | (exfalso; exact h)

variable {K : Type} [Group K] [Finite K]

theorem false_of_sporadic (hcard : ∀ s, Nat.card (Carrier s) = CFSG.AGLEmbedding.sporOrd s)
    (hSpor : SporadicNoE64) (hP : P12Facts) (hK : SolomonA12HypK K) (h : SporadicRep K) :
    False := by
  obtain ⟨s, ⟨e⟩⟩ := h
  obtain ⟨E, hE⟩ := hK.exists_goodE
  have hf : (CFSG.AGLEmbedding.sporOrd s).factorization 2 = 9 := by
    rw [← hcard s, ← Nat.card_congr e.toEquiv]
    exact two_part_card hP hK
  have hs : s = .HS ∨ s = .ONan := sporadic_two_part s hf
  let E' : Subgroup (Carrier s) := E.map e.toMonoidHom
  have hE'card : Nat.card E' = 2 ^ 6 := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact hE.card
  have hE'sq : ∀ x ∈ E', x * x = 1 := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    rw [← map_mul, hE.sq y hy, map_one]
  exact hSpor s hs E' hE'sq hE'card

end CFSG.EvenSporadicStandard.M12Std.SolomonK
