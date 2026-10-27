module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Product
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42ToSetup
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Transfer
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42GInst
public import CFSG.Adapters.GeneralizedFitting

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem gomiU42_of_selector (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : GomiU42Selector fun _ _ => True) (hYsq : ∀ y ∈ d.Y, y * y = 1) (h : d.Hyp) :
    d.K ⊓ d.H = d.K₃ ∧
      (CFSG.Blueprint.LieModel ↥d.K .PSL 4 2 2 ∨
        ∃ K₀ : Subgroup G, CFSG.Blueprint.LieModel ↥K₀ .PSU 4 2 1 ∧
          d.K = K₀ ⊔ K₀.map (MulAut.conj d.t).toMonoidHom ∧
          ⁅K₀, K₀.map (MulAut.conj d.t).toMonoidHom⁆ = ⊥ ∧
          K₀ ⊓ K₀.map (MulAut.conj d.t).toMonoidHom = ⊥) := by
  have hset := h.gomiU42SetupG hYsq
  have hset' := hset.toSetup
  haveI := hset'.normal_zpowers_e
  obtain ⟨h1, h2⟩ := hset'.reduction hGA hS
  obtain ⟨h3, h4⟩ := layer_transfer hset.t_mem hset.J₀_le h1 h2
  have hK : d.K = (CFSG.layer ↥(centralizer ({d.e₂} : Set G))).map
      (centralizer ({d.e₂} : Set G)).subtype := by
    rw [Data.K, CFSG.Adapters.genFittingLayer_eq_foundations]
  rw [hK]
  exact ⟨h3, h4⟩

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
