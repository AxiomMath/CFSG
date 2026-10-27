module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Bridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8FrameAux2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Lines

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ffE8_frame (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {E : Subgroup (OGroup Q)} {t ν : OGroup Q}
    (h : FFE8VData hQ E t ν) :
    ∃ (ε : ZMod 3) (_ : ε = 1 ∨ ε = -1) (fr : PFrame Q FFE8Idx (ffE8Norm ε)),
      E = ffE8Group fr ∧ t = fr.signChange (ffE8Hat Finset.univ) :=
  ffOutFFE8Frame_main hQ hdim h (fun fr hc K => ffE8Sign_mem_omega_iff hQ fr hc K)
    (ffE8Dim_fix hQ hdim hsgn h) (ffE8Lines_exists hQ hdim hsgn h)

theorem ffE8_frame_sim (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {Ē : Subgroup (ProjSim Q)} {z ν : ProjSim Q}
    (h : FFE8SData hQ Ē z ν) :
    ∃ (ε : ZMod 3) (_ : ε = 1 ∨ ε = -1) (fr : PFrame Q FFE8Idx (ffE8Norm ε)),
      Ē = (ffE8Group fr).map (ffSim Q) ∧
        z = ffSim Q (fr.signChange (ffE8Hat Finset.univ)) := by
  obtain ⟨E, t, ν', hV, hĒ, hz, -⟩ := ffE8_bridge hQ hdim hsgn h
  obtain ⟨ε, hε, fr, hE, ht⟩ := ffE8_frame hQ hdim hsgn hV
  exact ⟨ε, hε, fr, by rw [hĒ, hE], by rw [hz, ht]⟩

end CFSG.OddStandard.SmallF3.Omega
