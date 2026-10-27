module

public import CFSG.GH74.GLS.Stage2.Local.P34OneClass

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

theorem oneClassNoDiag : OneClassNoDiag := fun _ _ _ _ _ _ _ _ _ hL4 hone y hy hy2 =>
  hL4.noDiag hone y hy hy2

theorem noOneClassC0' : NoOneClassC0' := noOneClassC0'_of oneClassNoDiag

end CFSG.GH74.GLS.Stage2.Local.P34
