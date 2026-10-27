module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwoOrbit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwoL2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step CFSG.ClassicalInvolution.Disconnected.AschTight

theorem isE3aGroup_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : IsE3aGroup X) : IsE3aGroup X' := by
  obtain ⟨p, f, hp, hp2, ⟨hfe, hl2⟩ | ⟨hl3, h3⟩⟩ := h
  · exact ⟨p, f, hp, hp2, Or.inl ⟨hfe, hl2.of_mulEquiv e⟩⟩
  · exact ⟨p, f, hp, hp2,
      Or.inr ⟨hl3.imp (fun h => h.of_mulEquiv e) (fun h => h.of_mulEquiv e), h3⟩⟩

section Main

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)}

theorem not_isE3aGroup_of_orbitLie (hL3 : L3CentComponent) (hF : FStarSimple Y)
    (hΦ : TypeRHyp Φ) {M : Subgroup Y} (hM : M ∈ Φ) {z : Y} (hz : IsUniqueInvolution M z)
    (hzH : z ∈ omegaGen (lOrbit (genFittingFStar Y) M))
    (h : OrbitLie ↥(omegaGen (lOrbit (genFittingFStar Y) M))
      (M.subgroupOf (omegaGen (lOrbit (genFittingFStar Y) M))) ⟨z, hzH⟩) :
    ¬ IsE3aGroup ↥(genFittingFStar Y) := by
  obtain ⟨hHL, -, -⟩ := lie_case hF hΦ hM hz hzH h
  obtain ⟨c, hV, hne, φ, hs, hk, F, hFf, hMF, h24, hcl⟩ := h
  intro he
  exact not_isE3aGroup_of_classical l2CentDihedral hL3 hcl h24
    (isE3aGroup_of_mulEquiv (MulEquiv.subgroupCongr hHL).symm he)

theorem twoOrbitOfIdent'_of_facts (hTL : TwoLieOrbitsSame) (hL3 : L3CentComponent)
    (hCT : CoincTwin) (hOC : SocleOddCore) (hTO : TwinOddCore) (hL33 : L33Q8Class)
    (hU3 : U33Q8Classes) (hM12 : M12Q8Classes) (hTQ : TwinQ8Class) : TwoOrbitOfIdent' := by
  intro Y _ _ hcit hO h2 hF Φ hΦ hgen hid K hK J hJ hJK hG2
  exact twoOrbit_of_cases (e3aOneClass_of_inputs l2CentDihedral hL3) hCT hOC hTO hL33 hU3 hM12
    hTQ hO h2 hF hΦ hgen hid hK hJ hJK
    (fun M hM z hz hzH h => not_isE3aGroup_of_orbitLie hL3 hF hΦ hM hz hzH h)
    fun zK zJ hzK hzJ hlK hlJ => hTL Y hcit hO h2 hF Φ hΦ K hK J hJ zK zJ hzK hzJ hlK hlJ hG2

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident
