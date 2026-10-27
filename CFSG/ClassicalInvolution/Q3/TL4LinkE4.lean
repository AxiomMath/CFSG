module

public import CFSG.ClassicalInvolution.Q3.TL4LinkCases
public import CFSG.ClassicalInvolution.Q3.TL4LinkE2Nbr
public import CFSG.ClassicalInvolution.Q3.TL4SecIdLeaves

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.Blueprint

@[expose] def SecIdE4O8TwoNbrs : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightDatum R S t → TightCls Y R S t → ¬ TightInO2 t → Subgroup.center Y ≠ ⊥ →
      LieModel (Y ⧸ Subgroup.center Y) .POmegaPlus 4 2 1 →
        ∃ L ∈ CoreAssembly.conjClass (tightCore R),
          ∃ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) L,
            ∃ M' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) L, M ≠ M'

section Cit3


variable {r n : ℕ}

theorem tightLinkE4R_of (hD : SecIdE4DStar) (h8 : SecIdE4O8TwoNbrs) : TightLinkE4R r n := by
  intro Y _ _ R S t hL _ hT _ htr hnc R' S' t' hd' hc' heq hO2 hZ hE4
  rcases hE4 with hSp | hO8
  · refine ⟨htr, hnc, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hZ, hSp, ?_⟩)))))⟩
    have h := hD _ R' S' t' hd' hc' hO2 hZ (Or.inl hSp)
    rw [heq] at h
    exact h
  · exfalso
    obtain ⟨L, hLm, M, hM, M', hM', hne⟩ := h8 _ R' S' t' hd' hc' hO2 hZ hO8
    rw [heq] at hLm hM hM'
    exact hne (LinkE2.subsingleton_omegaNbr_link hL hT htr L hLm M hM M' hM')

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
