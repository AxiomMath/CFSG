module

public import CFSG.ClassicalInvolution.Q3.Q3VLiftLoc
public import CFSG.ClassicalInvolution.Q3.Q3VLocDef

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V.Lift

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane)


theorem exists_locLift {m : ℕ} (hm : 2 ≤ m) {G : Type} [Group G] [Finite G] {K : Subgroup G}
    {z : G} (hR : Q3W.RouteD3Setup K z)
    (hshape : Q3W.LocalShapeC3 1 (CompData.model .PSp m) (conjClass3 K) z)
    (hO3 : Q3W.LocalOddThreeFree3 (conjClass3 K) z) :
    ∃ Θ : StatedSp m (GaloisField 3 1) →* G, IsLocLift m (conjClass3 K) K Θ := by
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  obtain ⟨d⟩ := nonempty_cdictR hm hR.inClass hK hR.cls hshape
  let c : CCoreR m (conjClass3 K) K z :=
    ⟨hm, hR.inClass, hR.setup.1, hK, hR.cls, hR.setup.2, hO3, d⟩
  obtain ⟨l⟩ := c.nonempty_layer
  refine ⟨l.Θ, ⟨l.ker_le, ?_, ?_, ?_⟩⟩
  · rintro _ ⟨s, rfl⟩ b hb
    exact l.commutes_K s hb
  · intro P hP
    exact (l.plane P hP).1.1
  · intro M hM hMK hcomm
    have hMz : M ∈ centralizingMembers (conjClass3 K) {z} :=
      ⟨hM, fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hcomm x hx z hR.cls.mem)⟩
    obtain ⟨P, hP, hMP⟩ := l.exists_plane_of_ne hMz hMK
    exact ⟨P, hP, hMP⟩

end CFSG.ClassicalInvolution.Q3.Q3V.Lift
