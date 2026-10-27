module

public import CFSG.ClassicalInvolution.Q3.Q3CLSwap
import CFSG.ClassicalInvolution.Q3.Q3CLMirror
public import CFSG.ClassicalInvolution.Q3.Q3CLNine3

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3CL

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} {Q Q' : Subgroup G}

namespace T8R.Loc

open CFSG.ClassicalInvolution.Asc77.T8R.Loc
  CFSG.ClassicalInvolution.Asc77.T8R
  CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.T8
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

theorem eq_of_mem_conj_sylow (hs : Std8Core Ω K J S R T W z t)
    (hX : Loc26 Ω K J S R T z t Q) (hXs : Loc26 Ω J K S T R t z Q') {n : G}
    (hzP : z ∈ conjSub n (S : Subgroup G)) (htP : t ∈ conjSub n (S : Subgroup G)) :
    n * (z * t) * n⁻¹ = z * t := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hs' := hs.conj n
  have hX' := loc26_conj hΩ hX n
  have hV := extraTrans hs' hX' (loc26_conj hΩ hXs n)
  exact eq_of_mem_conj_sylow_of hs.toFrame hs'.toFrame (R_ne_T hs')
    (fix_or_swap hs' hX') (eq_of_swap hs' hX' hV) (eq_of_centralizes hs' hX' hV)
    (fun hy => ⟨Q, hX.odd, hX.zt hy⟩) (fun hy => ⟨Q', hXs.odd, hXs.zt hy⟩)
    (l9_3 (partIHyp_of_std8 hs)) hzP htP

theorem outerFusion (hs : Std8Core Ω K J S R T W z t)
    (hX : Loc26 Ω K J S R T z t Q)
    (hXs : Loc26 Ω J K S T R t z Q') : OuterFusion K J S R T z t := by
  exact outerFusion_of hs.toFrame (conj_zt_of_mem_sylow hs hX) (eq_of_mem_conj_sylow hs hX hXs)

theorem false_of_loc26 [IsSimpleGroup G] (hs : Std8Core Ω K J S R T W z t)
    (hX : Loc26 Ω K J S R T z t Q) (hXs : Loc26 Ω J K S T R t z Q') : False :=
  false_of_loc hs hX hXs (extraTrans hs hX hXs) (extraTrans hs.symm' hXs hX) (outerFusion hs hX hXs)

end T8R.Loc


end CFSG.ClassicalInvolution.Q3.Q3CL
