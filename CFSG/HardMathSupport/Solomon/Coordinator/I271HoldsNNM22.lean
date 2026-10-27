module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsM22Plane
public import CFSG.HardMathSupport.Solomon.Coordinator.I271TwistPlane
public import CFSG.HardMathSupport.Solomon.Coordinator.I271TwistRel
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsNNFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.I271TwistGlue
public import CFSG.Sporadic.Bridge.M22

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem m22_plane_tauCeti
    (E : Subgroup (MulAut TauCeti.SporadicName.M22.Group)) (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 9) :
    Subgroup.closure {s : TauCeti.SporadicName.M22.Group | ∃ ε ∈ E, ε ≠ 1 ∧ ε s = s} = ⊤ := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  set E' : Subgroup (MulAut M22Plane.G) := E.map (MulAut.congr e.symm).toMonoidHom with hE'
  have hE'e : IsElemAbelian 3 E' := CFSG.SectionRank.isElemAbelian_map hE _
  have hE'c : Nat.card E' = 9 := by
    rw [← hc]
    exact Subgroup.card_map_of_injective (MulAut.congr e.symm).injective
  have hgen := M22Plane.m22_plane E' hE'e hE'c
  have hEE : E'.map (MulAut.congr e).toMonoidHom = E := by
    rw [hE', Subgroup.map_map]
    have : (MulAut.congr e).toMonoidHom.comp (MulAut.congr e.symm).toMonoidHom = MonoidHom.id _ := by
      ext φ x
      simp [MulAut.congr_apply]
    rw [this, Subgroup.map_id]
  have := (CFSG.LieType.SeitzGeneration.planeGen_map_congr e E').2 hgen
  rw [hEE] at this
  exact this

theorem nnExcZ_hatMTwentyTwo :
    NNExcZ (fun _ _ K => IsHatMTwentyTwo ↥K) := by
  intro X _ _ hXK K B hH hNN hidx h4 h9 hZ1 hZ2 hP
  left
  obtain ⟨-, -, ⟨e⟩⟩ := hP
  have hBel : IsElemAbelian 3 B := hH.scp.2.1
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hH.core hH.comp
  have h9' : autOrderIn B K = 9 := by rw [h9]; norm_num
  exact nn_caseA_of_twist hH hidx (rel_of_ZJ hH hZ1 hZ2)
    (hgen_of_plane hBel hq.1 h9' e (fun E hE hc => m22_plane_tauCeti E hE hc))

theorem nnHatMTwentyTwo_holds
    (T : Tables112) (TL : TableL2) (TT : Tables112Types) : NNHatMTwentyTwo :=
  nnFor_of_excZ (fun _ _ K => IsHatMTwentyTwo ↥K) (nnFactsZ_of_tables T TL TT _)
    nnExcZ_hatMTwentyTwo

end CFSG.HardMathSupport.Solomon.Coordinator
