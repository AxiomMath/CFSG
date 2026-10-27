module

public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.R2

open Subgroup CFSG.Blueprint

section CentTwoThree

variable {K : Type} [Group K] {u : K}

theorem map_centralizer_singleton {L : Type} [Group L] (e : K ≃* L) (u : K) :
    (centralizer ({u} : Set K)).map e.toMonoidHom = centralizer ({e u} : Set L) := by
  ext y
  simp only [mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, hx]
  · intro hy
    refine ⟨e.symm y, e.injective ?_, e.apply_symm_apply y⟩
    rw [map_mul, map_mul, e.apply_symm_apply, hy]

theorem card_centralizer_mulEquiv {L : Type} [Group L] (e : K ≃* L) (u : K) :
    Nat.card (centralizer ({e u} : Set L)) = Nat.card (centralizer ({u} : Set K)) := by
  rw [← map_centralizer_singleton e u, card_map_of_injective e.injective]

end CentTwoThree

end CFSG.LocalAnalysis.EvenBN.Tits.R2
