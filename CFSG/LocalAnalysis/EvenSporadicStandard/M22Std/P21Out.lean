module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Simple
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Cent

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.M24Std CFSG.EvenSporadicStandard.M23Std

theorem natCard_centralizer_congr {U E : Type*} [Group U] [Group E] (e : U ≃* E) (u : U) :
    Nat.card (centralizer ({u} : Set U)) = Nat.card (centralizer ({e u} : Set E)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨e x.1, ?_⟩
      invFun := fun y => ⟨e.symm y.1, ?_⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }
  · have := mem_centralizer_singleton_iff.1 x.2
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, this]
  · have := mem_centralizer_singleton_iff.1 y.2
    rw [mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, this]

variable {G : Type} [Group G] [Finite G] {z : G}

theorem prop21_simple_case (hz : orderOf z = 2)
    (hC : Nonempty (↥(centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6)))
    (hG : Nat.card G ∣ gl8) (hE : EData ↥(egaLayer (G ⧸ fusionOddCore G)))
    (hbig : 1440 < Nat.card (egaLayer (G ⧸ fusionOddCore G)))
    (hTab : ∀ u : ↥(egaLayer (G ⧸ fusionOddCore G)), u * u = 1 → u ≠ 1 →
      ¬ (Nat.card (centralizer ({u} : Set ↥(egaLayer (G ⧸ fusionOddCore G)))) = 1 ∨
        Nat.card (centralizer ({u} : Set ↥(egaLayer (G ⧸ fusionOddCore G)))) = 2 ∨
        Nat.card (centralizer ({u} : Set ↥(egaLayer (G ⧸ fusionOddCore G)))) = 360 ∨
        Nat.card (centralizer ({u} : Set ↥(egaLayer (G ⧸ fusionOddCore G)))) = 720 ∨
        Nat.card (centralizer ({u} : Set ↥(egaLayer (G ⧸ fusionOddCore G)))) = 1440)) :
    ∃ U : Subgroup G, U.Normal ∧ Nonempty (U ≃* ↥(egaLayer (G ⧸ fusionOddCore G))) ∧
      egaLayer G = U ∧ z ∉ U ⊔ centralizer (U : Set G) := by
  obtain ⟨U, hUn, -, ⟨e⟩, hU⟩ := exists_cover_of_eData hG hE
  refine ⟨U, hUn, ⟨e⟩, hU, ?_⟩
  obtain ⟨c⟩ := id hC
  have hZ : ∀ u : U, (∀ g : U, g * u = u * g) → u = 1 := by
    intro u hu
    have h1 : e u = 1 := hE.chief.center (e u) fun x => by
      have := congrArg e (hu (e.symm x))
      simpa using this
    exact e.injective (by rw [h1, map_one])
  have hbigU : 1440 < Nat.card U := by rwa [Nat.card_congr e.toEquiv]
  exact not_mem_sup_centralizer_of_table hz c U hZ hbigU fun u hu hu1 => by
    have := hTab (e u) (by rw [← map_mul, hu, map_one])
      (fun h => hu1 (e.injective (by rw [h, map_one])))
    rwa [← natCard_centralizer_congr e u] at this

end CFSG.EvenSporadicStandard.M22Std
