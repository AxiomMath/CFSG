module

public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersSporadic
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1PThOrd8
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1PMonsterOrd8

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open CFSG.EvenSmallLie.CatalogOrders CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem false_of_order_eight {T U : Type} [Group T] [Group U] (e : T ≃* U)
    (h4 : ∀ (x : T) (k : ℕ), x ^ (2 ^ k) = 1 → x ^ 4 = 1)
    (hx : ∃ x : U, x ^ 8 = 1 ∧ x ^ 4 ≠ 1) : False := by
  obtain ⟨x, hx8, hx4⟩ := hx
  apply hx4
  have h1 : (e.symm x) ^ (2 ^ 3) = 1 := by
    rw [← map_pow, show 2 ^ 3 = 8 by norm_num, hx8, map_one]
  have h2 := h4 _ 3 h1
  have h3 : e.symm (x ^ 4) = 1 := by rw [map_pow]; exact h2
  exact (MulEquiv.map_eq_one_iff e.symm).1 h3

theorem sporadicOrders_false : ∀ N ∈ sporadicOrders, 979200 ∣ N → ¬ 2 ^ 9 ∣ N → False := by
  decide +kernel

theorem not_sporadic
    {T : Type} [Group T] [Finite T] (hs : SporadicRep T) (hnab : ∃ a b : T, a * b ≠ b * a)
    (hdvd : 979200 ∣ Nat.card T) (hv : ¬ 2 ^ 9 ∣ Nat.card T)
    (h4 : ∀ (x : T) (k : ℕ), x ^ (2 ^ k) = 1 → x ^ 4 = 1) : False := by
  obtain ⟨s, ⟨e⟩⟩ := hs
  have hcard : Nat.card T = Nat.card (Carrier s) := Nat.card_congr e.toEquiv
  have hmem : ∀ m ∈ sporadicOrders, Nat.card (Carrier s) = m → False := fun m hm h =>
    sporadicOrders_false m hm (by rw [← h, ← hcard]; exact hdvd)
      (by rw [← h, ← hcard]; exact hv)
  cases s
  case M11 => exact hmem _ (by decide) CFSG.Sporadic.Mathieu.card_M11
  case M12 => exact hmem _ (by decide) CFSG.Sporadic.Mathieu.card_M12
  case M22 => exact hmem _ (by decide) CFSG.Sporadic.Mathieu.card_M22
  case M23 => exact hmem _ (by decide) card_M23
  case M24 => exact hmem _ (by decide) CFSG.Sporadic.Mathieu.card_M24
  case J1 => exact hmem _ (by decide) CFSG.Sporadic.J1.card_J1
  case J2 => exact hmem _ (by decide) CFSG.Sporadic.J2.card_J2
  case J3 => exact hmem _ (by decide) CFSG.Sporadic.J3.card_J3
  case J4 => exact hmem _ (by decide) CFSG.Sporadic.J4.card_J4
  case HS => exact hmem _ (by decide) CFSG.Sporadic.HS.card_HS
  case McL => exact hmem _ (by decide) CFSG.Sporadic.McL.card_McL
  case He => exact hmem _ (by decide) CFSG.Sporadic.He.fam_he_order.1
  case Ru => exact hmem _ (by decide) CFSG.Sporadic.Ru.card_Ru
  case Suz => exact hmem _ (by decide) CFSG.Sporadic.Suz.card_Suz
  case ONan => exact hmem _ (by decide) CFSG.Sporadic.ON.card_ON
  case Co1 => exact hmem _ (by decide) CFSG.Sporadic.Co1.card_Co1
  case Co2 => exact hmem _ (by decide) CFSG.Sporadic.Co2.card_Co2
  case Co3 => exact hmem _ (by decide) CFSG.Sporadic.Co3.card_Co3
  case Fi22 => exact hmem _ (by decide) CFSG.Sporadic.Fi22.card_Fi22
  case Fi23 => exact hmem _ (by decide) CFSG.Sporadic.Fi23.card_Fi23
  case Fi24Prime => exact hmem _ (by decide) CFSG.Sporadic.Fi24.card_Fi24prime
  case HN => exact hmem _ (by decide) CFSG.Sporadic.HN.card_HN
  case Ly => exact hmem _ (by decide) CFSG.Sporadic.Ly.card_Ly
  case Th => exact false_of_order_eight e h4 exists_order_eight_Th
  case B => exact hmem _ (by decide) CFSG.Monster.Existence.card_nativeB
  case M =>
    obtain ⟨a, b, hab⟩ := hnab
    haveI : Nontrivial T := ⟨⟨a * b, b * a, hab⟩⟩
    obtain ⟨x, hx8, hx4⟩ := exists_order_eight_of_mulEquiv_M e
    exact hx4 (h4 x 3 (by simpa using hx8))

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
