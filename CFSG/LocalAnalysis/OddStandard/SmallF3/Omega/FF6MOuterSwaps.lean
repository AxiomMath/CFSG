module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MFieldModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem ff6m_outer_swaps (G : Type) [Group G] [Finite G] (L : Subgroup G) (h : IsOm6M L)
    (s : G) (hsN : s ∈ normalizer (L : Set G))
    (hout : InducesOutsideGStar L 6 (-1) s) (U : Subgroup G) (hUL : U ≤ L)
    (hU : IsElemAb2 U 4) : s ∉ normalizer (U : Set G) := by
  obtain ⟨V, _, _, _, Q, hQ, e, x, hdim, hsgn, hs, hxx, hxG⟩ := hout
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  obtain ⟨fr⟩ := exists_nframe_six hQ hdim hsgn
  obtain ⟨y, hy⟩ := ff_adapt_exists hQ hdim hsgn h2 e (ff6m_odd_center h) fr hUL hU
  let e' := ffAdapt h2 e y
  let x' := y⁻¹ * x * y
  have hs' : InducesViaP L (Subgroup.center ↥L) hQ e' s x' :=
    inducesViaP_ffAdapt h2 e y hs
  have hy' : ffImg (ff6mPhi e') U = ffB1 hQ fr := hy
  have hx'x' : x' * x' = 1 := by
    have h : x' * x' = y⁻¹ * (x * x) * y := by
      dsimp only [x']
      group
    rw [h, hxx]
    group
  have hx'G : ¬ SimInGStar x' := fun hh => hxG ((simInGStar_conj_iff x y).mp hh)
  intro hn
  have hle : (ffB1 hQ fr).map (ffSimOmegaAct hQ h2 x').toMonoidHom ≤ ffB1 hQ fr := by
    intro b hb
    obtain ⟨c, hc, hcb⟩ := Subgroup.mem_map.mp hb
    have hc' : c ∈ ffImg (ff6mPhi e') U := by
      rw [hy']
      exact hc
    obtain ⟨l, hlU, hlφ⟩ := mem_ffImg_iff.mp hc'
    let l' : ↥L := ⟨s * (l : G) * s⁻¹,
      (Subgroup.mem_normalizer_iff.mp hs'.1 (l : G)).mp l.2⟩
    have hb1 : ff6mPhi e' l' ∈ ffB1 hQ fr := by
      rw [← hy']
      exact mem_ffImg_iff.mpr ⟨l', (Subgroup.mem_normalizer_iff.mp hn (l : G)).mp hlU, rfl⟩
    rw [← hcb, ← hlφ]
    change ffSimOmegaAct hQ h2 x' (ff6mPhi e' l) ∈ ffB1 hQ fr
    rw [ff6m_phi_conj hQ h2 e' hs' l l' rfl]
    exact hb1
  have hge : ffB1 hQ fr ≤ (ffB1 hQ fr).map (ffSimOmegaAct hQ h2 x').toMonoidHom := by
    intro b hb
    rw [Subgroup.mem_map]
    refine ⟨ffSimOmegaAct hQ h2 x' b, hle ⟨b, hb, rfl⟩, ?_⟩
    show ffSimOmegaAct hQ h2 x' (ffSimOmegaAct hQ h2 x' b) = b
    rw [← MulAut.mul_apply, ← map_mul, hx'x', map_one, MulAut.one_apply]
  exact hx'G (ff_star_normalizes_simInGStar hQ h2 fr (le_antisymm hle hge))

end CFSG.OddStandard.SmallF3.Omega
