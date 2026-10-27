module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeExcBasic
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4


theorem noSmall_of_isTE6two {S : Type} [Group S] (h : catalogIs S S9.isTE6two) :
    HStdExcl.NoSmall S := by
  obtain ⟨K, hfield, hfinite, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.CatB.I2610.exists_twistedE6RootGroup_of_catalogIs_isTE6two h
  letI : Field K := hfield
  letI : Finite K := hfinite
  exact noSmall_of_mulEquiv e (CFSG.LocalAnalysis.GLTheoremA.HStdExcl.exclTE6_holds K σ hK hσ)

theorem noSmall_lie_twistedE6 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (hq : q.card = 2) :
    HStdExcl.NoSmall (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group :=
  noSmall_of_isTE6two ⟨TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩, hq, ⟨MulEquiv.refl _⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
