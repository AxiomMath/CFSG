module

public import CFSG.ClassicalInvolution.Q3.TL4Conn274

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section Cit3

variable {r n : ℕ}

@[expose] def TightC27_8nE4R (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (z : Y) (J : Subgroup Y)
    (S : Sylow 2 Y) (R T W : Subgroup Y) (t : Y), TightStd8R r n Rd Sd z J S R T W t →
      ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)) →
        ¬ MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W →
          Subgroup.centralizer ({z * t} : Set Y) ≤
            sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)

@[expose] def TightC27_8R (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (z : Y) (J : Subgroup Y)
    (S : Sylow 2 Y) (R T W : Subgroup Y) (t : Y), TightStd8R r n Rd Sd z J S R T W t →
      ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)) →
        Subgroup.centralizer ({z * t} : Set Y) ≤
          sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)

theorem tightC27_8R_of (hE4 : TightF26E4R r n) (hnE4 : TightC27_8nE4R r n) :
    TightC27_8R r n := by
  intro Y _ _ Rd Sd z J S R T W t hs hdisc
  by_cases h : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W
  · exact hE4 Y Rd Sd z J S R T W t hs hdisc h
  · exact hnE4 Y Rd Sd z J S R T W t hs hdisc h

theorem tightConnLeafR'_of_steps (h274 : TightC27_4R r n) (h278 : TightC27_8R r n) :
    TightConnLeafR' r n := by
  intro Y _ _ Rd Sd z hL
  by_contra hdisc
  obtain ⟨J, hJ, t, ht⟩ := TightLargeHypR.exists_nbr hL
  obtain ⟨S, R, T, W, hs⟩ := TightLargeHypR.exists_std8 hL hJ ht
  have h4 := h274 Y Rd Sd z J S R T W t hs hdisc
  have hle : H274 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z ≤
      sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) := by
    refine sup_le le_rfl (iSup₂_le fun M hM => iSup_le fun s => iSup_le fun hs' => ?_)
    obtain ⟨S', R', T', W', hstd'⟩ := TightLargeHypR.exists_std8 hL hM hs'
    exact h278 Y Rd Sd z M S' R' T' W' s hstd' hdisc
  rw [h4] at hle
  exact hdisc (dConnected_of_sigmaNorm_eq_top hs.mem hs.trans (top_le_iff.mp hle))

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
