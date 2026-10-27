module

public import CFSG.ClassicalInvolution.SmallCases.NDBH4
import CFSG.ClassicalInvolution.Q3.Q3CLMirror

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3 CFSG.ClassicalInvolution.Asc77.T8
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen CFSG.ClassicalInvolution.Asc77.T8R

namespace T8R.Loc

section Cert

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} {Q Q' : Subgroup G}


theorem eq_of_mem_conj_sylow (hs : Std8Core p f Ω K J S R T W z t)
    (hX : Loc26 Ω K J S R T z t Q) (hXs : Loc26 Ω J K S T R t z Q') {n : G}
    (hzP : z ∈ conjSub n (S : Subgroup G)) (htP : t ∈ conjSub n (S : Subgroup G)) :
    n * (z * t) * n⁻¹ = z * t := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hs' := hs.conj n
  have hX' := hX.conj hΩ n
  have hV := extraTrans hs' hX' (hXs.conj hΩ n)
  exact Q3.Q3CL.T8R.Loc.eq_of_mem_conj_sylow_of hs.toFrame hs'.toFrame (R_ne_T hs')
    (fix_or_swap hs' hX') (eq_of_swap hs' hX' hV) (eq_of_centralizes hs' hX' hV)
    (fun hy => ⟨Q, hX.odd, hX.zt hy⟩) (fun hy => ⟨Q', hXs.odd, hXs.zt hy⟩)
    (l9_3 (p := p) (f := f) G Ω (partIHyp_of_std8 hs)) hzP htP

theorem outerFusion (hs : Std8Core p f Ω K J S R T W z t)
    (hX : Loc26 Ω K J S R T z t Q)
    (hXs : Loc26 Ω J K S T R t z Q') : OuterFusion K J S R T z t := by
  exact Q3.Q3CL.T8R.Loc.outerFusion_of hs.toFrame
    (conj_zt_of_mem_sylow hs hX) (eq_of_mem_conj_sylow hs hX hXs)


theorem false_of_loc26 [IsSimpleGroup G] (hs : Std8Core p f Ω K J S R T W z t)
    (hX : Loc26 Ω K J S R T z t Q) (hXs : Loc26 Ω J K S T R t z Q') : False :=
  false_of_loc hs hX hXs (extraTrans hs hX hXs) (extraTrans hs.symm' hXs hX) (outerFusion hs hX hXs)


end Cert

end T8R.Loc

end CFSG.ClassicalInvolution.Asc77
