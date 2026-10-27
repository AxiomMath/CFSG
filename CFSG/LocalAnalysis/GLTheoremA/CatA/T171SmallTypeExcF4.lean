module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeExcBasic
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclF4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4


theorem noSmall_of_isF4two {S : Type} [Group S] (h : catalogIs S S9.isF4two) :
    HStdExcl.NoSmall S := by
  obtain ⟨K, hfield, hfinite, hK, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.CatB.I2610.exists_adjointGroup_of_catalogIs_isF4two h
  letI : Field K := hfield
  letI : Finite K := hfinite
  exact noSmall_of_mulEquiv e (CFSG.LocalAnalysis.GLTheoremA.HStdExcl.exclF4_holds K hK)

theorem noSmall_lie_F4 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.F4 q).Valid)
    (hq : q.card = 2) :
    HStdExcl.NoSmall (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group :=
  noSmall_of_isF4two ⟨TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩, hq, ⟨MulEquiv.refl _⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
