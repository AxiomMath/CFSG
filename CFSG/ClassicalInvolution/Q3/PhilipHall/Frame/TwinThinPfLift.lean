module

public import CFSG.ClassicalInvolution.Q3.TL3T14
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfModel

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3.AE

variable {G : Type} [Group G] [Finite G]

@[expose] def threeGens (P : Set (Subgroup G)) (zS : ↥(pSpan P)) : Set ↥(pSpan P) :=
  {w | w * zS = zS * w ∧ ∃ a : ℕ, w ^ 3 ^ a = 1}

theorem exists_mem_threeClosure {P : Set (Subgroup G)} {m : ℕ} {𝒜 : Set (Finset (Fin m))}
    {H : Subgroup (AEQ m)} (hm : 5 ≤ m) (I : AEIdentOn P m 𝒜 H) (hCl : OddClosure H 𝒜)
    (hO : classicalInvolutionOddCore ↥(pSpan P) = ⊥) (hc8 : ∀ L ∈ P, Nat.card L = 8)
    {K : Subgroup G} (hK : K ∈ P) {z : G} (hz : IsUniqueInvolution K z)
    {L : Subgroup G} (hL : L ∈ P) {u : G} (hu : IsUniqueInvolution L u) :
    ∃ t ∈ Subgroup.closure (threeGens P ⟨z, le_pSpan hK hz.mem⟩),
      t⁻¹ * ⟨u, le_pSpan hL hu.mem⟩ ∈ I.φ.ker := by
  set J := I.toLabel with hJ
  have hk : IsPGroup 2 J.φ.ker := J.isPGroup_ker hO
  obtain ⟨α, hα, h4, b, hlabK⟩ := I.label K hK
  set zS : ↥(pSpan P) := ⟨z, le_pSpan hK hz.mem⟩ with hzSdef
  have hzmap : J.φ zS = zBar α h4 := phi_map_eq_zBar J.φ hm hK (hc8 K hK) hlabK hz
  obtain ⟨β, hβ, h4', b', hlab'⟩ := I.label L hL
  have hu' : J.φ ⟨u, le_pSpan hL hu.mem⟩ = zBar β h4' :=
    phi_map_eq_zBar J.φ hm hL (hc8 L hL) hlab' hu
  have h1 := hCl α hα h4 β hβ h4'
  have hmodel : zBar β h4' ∈ (Subgroup.closure (threeGens P zS)).map J.φ := by
    refine (Subgroup.closure_le ((Subgroup.closure (threeGens P zS)).map J.φ)).mpr ?_ h1
    rintro x ⟨hxH, hxc, hx3⟩
    have hxr : x ∈ J.φ.range := by
      rw [show J.φ = I.φ from rfl, I.range_eq]; exact hxH
    obtain ⟨y, hyx, a, hya⟩ := J.exists_lift_pow_three hxr hx3
    refine ⟨y, Subgroup.subset_closure ⟨?_, a, hya⟩, hyx⟩
    refine J.comm_of_pow_three hk hya ?_
    rw [hyx, hzmap]
    exact hxc
  obtain ⟨t, htT, hte⟩ := hmodel
  refine ⟨t, htT, ?_⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv]
  show (J.φ t)⁻¹ * J.φ ⟨u, le_pSpan hL hu.mem⟩ = 1
  rw [hte, hu', inv_mul_cancel]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf
