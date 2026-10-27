module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HL34Cent

public section

namespace CFSG.EvenSporadicStandard.HSStd.HFI

open Equiv Equiv.Perm Subgroup CFSG.EvenSporadicStandard.HSStd.HL34

theorem card_centralizer_of_good {D : Type*} [Group D] {x : D}
    (e : Nonempty (↥(centralizer ({x} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5))) :
    Nat.card ↥(centralizer ({x} : Set D)) = 240 := by
  obtain ⟨e⟩ := e
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, card_perm_five]
  have : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  rw [this]

theorem card_centralizer_singleton_map {G H : Type*} [Group G] [Group H] (φ : G ≃* H) (x : G) :
    Nat.card ↥(centralizer ({φ x} : Set H)) = Nat.card ↥(centralizer ({x} : Set G)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv φ.symm.toEquiv fun y => ?_)
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg φ.symm h
    simpa [map_mul] using this
  · intro h
    have := congrArg φ h
    simpa [map_mul] using this

theorem orderOf_mul_eq_two {D : Type*} [Group D] {a b : D} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hab : a ≠ b) (hcomm : a * b = b * a) : orderOf (a * b) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha2 : a * a = 1 := by rw [← sq, ← ha]; exact pow_orderOf_eq_one a
  have hb2 : b * b = 1 := by rw [← sq, ← hb]; exact pow_orderOf_eq_one b
  refine orderOf_eq_prime ?_ ?_
  · calc (a * b) ^ 2 = (a * b) * (a * b) := sq _
      _ = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hcomm]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  · intro h
    exact hab ((inv_eq_of_mul_eq_one_right ha2).symm.trans (eq_inv_of_mul_eq_one_right h).symm)

end CFSG.EvenSporadicStandard.HSStd.HFI
