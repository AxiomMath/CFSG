module

public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M23
public import CFSG.Sporadic.J1
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.J3
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.McL.Simple
public import CFSG.Sporadic.He
public import CFSG.Sporadic.Ru
public import CFSG.Sporadic.Suz.Simple
public import CFSG.Sporadic.ON
public import CFSG.Sporadic.Co3
public import CFSG.Sporadic.Fi22.Simple
public import CFSG.Sporadic.Fi24.Simple
public import CFSG.Sporadic.HN
public import CFSG.Sporadic.Ly
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersTh
public import CFSG.Monster.Existence.BabyOrder

public section

namespace CFSG.EvenSmallLie.CatalogOrders

open CFSG.Blueprint NativeSporadic

@[expose] def sporadicOrders : List ℕ :=
  [7920, 95040, 443520, 10200960, 244823040, 175560, 604800, 50232960,
    86775571046077562880, 44352000, 898128000, 4030387200, 145926144000, 448345497600,
    460815505920, 4157776806543360000, 42305421312000, 495766656000, 64561751654400,
    4089470473293004800, 1255205709190661721292800, 273030912000000, 51765179004000000,
    CFSG.Open.monsterBabyOrder]

theorem card_M23
    : Nat.card NativeSporadic.M23 = 10200960 := by
  rw [CFSG.Sporadic.Mathieu.nativeM23_eq]
  exact (Nat.card_eq_fintype_card (α := CFSG.M23.M23Group.H0)).trans CFSG.M23.M23Group.card_M23

theorem mem_of_card_eq {X : Type*} {m : ℕ} (h : Nat.card X = m) (hm : m ∈ sporadicOrders) :
    Nat.card X ∈ sporadicOrders :=
  h ▸ hm

theorem card_mem_sporadicOrders_or_M
    {T : Type} [Group T] (h : SporadicRep T) :
    Nat.card T ∈ sporadicOrders ∨ 19 ∣ Nat.card T ∨ Nonempty (T ≃* NativeSporadic.M) := by
  obtain ⟨s, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  cases s
  case M11 => exact Or.inl (mem_of_card_eq CFSG.Sporadic.Mathieu.card_M11 (by decide))
  case M12 => exact Or.inl (mem_of_card_eq CFSG.Sporadic.Mathieu.card_M12 (by decide))
  case M22 => exact Or.inl (mem_of_card_eq CFSG.Sporadic.Mathieu.card_M22 (by decide))
  case M23 => exact Or.inl (mem_of_card_eq card_M23 (by decide))
  case M24 => exact Or.inl (mem_of_card_eq CFSG.Sporadic.Mathieu.card_M24 (by decide))
  case J1 => exact Or.inl (mem_of_card_eq CFSG.Sporadic.J1.card_J1 (by decide))
  case J2 => exact Or.inl (mem_of_card_eq CFSG.Sporadic.J2.card_J2 (by decide))
  case J3 => exact Or.inl (mem_of_card_eq CFSG.Sporadic.J3.card_J3 (by decide))
  case J4 => exact Or.inl (mem_of_card_eq CFSG.Sporadic.J4.card_J4 (by decide))
  case HS => exact Or.inl (mem_of_card_eq CFSG.Sporadic.HS.card_HS (by decide))
  case McL => exact Or.inl (mem_of_card_eq CFSG.Sporadic.McL.card_McL (by decide))
  case He => exact Or.inl (mem_of_card_eq CFSG.Sporadic.He.fam_he_order.1 (by decide))
  case Ru => exact Or.inl (mem_of_card_eq CFSG.Sporadic.Ru.card_Ru (by decide))
  case Suz => exact Or.inl (mem_of_card_eq CFSG.Sporadic.Suz.card_Suz (by decide))
  case ONan => exact Or.inl (mem_of_card_eq CFSG.Sporadic.ON.card_ON (by decide))
  case Co1 => exact Or.inl (mem_of_card_eq CFSG.Sporadic.Co1.card_Co1 (by decide))
  case Co2 => exact Or.inl (mem_of_card_eq CFSG.Sporadic.Co2.card_Co2 (by decide))
  case Co3 => exact Or.inl (mem_of_card_eq CFSG.Sporadic.Co3.card_Co3 (by decide))
  case Fi22 => exact Or.inl (mem_of_card_eq CFSG.Sporadic.Fi22.card_Fi22 (by decide))
  case Fi23 => exact Or.inl (mem_of_card_eq CFSG.Sporadic.Fi23.card_Fi23 (by decide))
  case Fi24Prime => exact Or.inl (mem_of_card_eq CFSG.Sporadic.Fi24.card_Fi24prime (by decide))
  case HN => exact Or.inl (mem_of_card_eq CFSG.Sporadic.HN.card_HN (by decide))
  case Ly => exact Or.inl (mem_of_card_eq CFSG.Sporadic.Ly.card_Ly (by decide))
  case Th => exact Or.inr (Or.inl nineteen_dvd_card_Th)
  case B => exact Or.inl (mem_of_card_eq CFSG.Monster.Existence.card_nativeB (by decide))
  case M => exact Or.inr (Or.inr ⟨e⟩)

end CFSG.EvenSmallLie.CatalogOrders
