module

public import CFSG.CGT.Foote81L6.MainL6Inputs
public import CFSG.CGT.Foote81L6.Fusion3.One
public import CFSG.CGT.Foote81L6.Fusion3.Two

public section

namespace CFSG.CGT.Foote81L6

theorem footeLemma3One_holds : FooteLemma3One :=
  fun _ _ _ _ _ _ D _ hx _ hy hxy => Fusion3.lemma3_one D hx hy hxy

theorem footeLemma3Two_holds : FooteLemma3Two :=
  fun _ _ _ _ _ D hcen _ ha₁ ha₁1 ha₁a => Fusion3.lemma3_two D hcen ha₁ ha₁1 ha₁a

end CFSG.CGT.Foote81L6
