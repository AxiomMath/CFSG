module

public import CFSG.HardMathSupport.GuralnickMalle.SLnNatural2F

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open Module
open CFSG.Open

variable {K : Type} [Field K]

@[expose] noncomputable def sl6Exterior3Rep (K : Type) [Field K] :
    Representation K (StatedSL 6 K) (⋀[K]^3 (Fin 6 → K)) where
  toFun g := exteriorPower.map 3 ((slNaturalRep 6 K) g)
  map_one' := by
    change exteriorPower.map 3 ((slNaturalRep 6 K) 1) = 1
    rw [map_one]
    change exteriorPower.map 3 (LinearMap.id : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) =
      LinearMap.id
    rw [exteriorPower.map_id]
  map_mul' g h := by
    change exteriorPower.map 3 ((slNaturalRep 6 K) (g * h)) =
      exteriorPower.map 3 ((slNaturalRep 6 K) g) *
        exteriorPower.map 3 ((slNaturalRep 6 K) h)
    rw [map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      exteriorPower.map_comp]

theorem sl6Exterior3Rep_apply (g : StatedSL 6 K) :
    (sl6Exterior3Rep K) g = exteriorPower.map 3 ((slNaturalRep 6 K) g) :=
  rfl

@[expose] def stdTriple6 : Set.powersetCard (Fin 6) 3 :=
  Set.powersetCard.ofCard (s := {0, 1, 2}) (by decide)

@[simp] theorem stdTriple6_val : (stdTriple6 : Finset (Fin 6)) = {0, 1, 2} := rfl

theorem finrank_sl6Exterior3 :
    Module.finrank K (⋀[K]^3 (Fin 6 → K)) = 20 := by
  rw [exteriorPower.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  decide

theorem card_sl6Exterior3 [Finite K] :
    Nat.card (⋀[K]^3 (Fin 6 → K)) = Nat.card K ^ 20 := by
  rw [Module.natCard_eq_pow_finrank (K := K) (V := ⋀[K]^3 (Fin 6 → K)),
    finrank_sl6Exterior3]

@[expose] def replaceTriple (q p : Fin 6) (s : Set.powersetCard (Fin 6) 3)
    (hq : q ∈ (s : Finset (Fin 6))) (hp : p ∉ (s : Finset (Fin 6))) :
    Set.powersetCard (Fin 6) 3 :=
  ⟨insert p ((s : Finset (Fin 6)).erase q), by
    rw [Set.powersetCard.mem_iff]
    have hp' : p ∉ (s : Finset (Fin 6)).erase q :=
      fun h => hp (Finset.mem_of_mem_erase h)
    rw [Finset.card_insert_of_notMem hp', Finset.card_erase_of_mem hq, s.2]⟩

@[simp] theorem replaceTriple_val (q p : Fin 6) (s : Set.powersetCard (Fin 6) 3)
    (hq : q ∈ (s : Finset (Fin 6))) (hp : p ∉ (s : Finset (Fin 6))) :
    (replaceTriple q p s hq hp : Finset (Fin 6)) =
      insert p ((s : Finset (Fin 6)).erase q) :=
  rfl

end CFSG.HardMathSupport.GuralnickMalle
