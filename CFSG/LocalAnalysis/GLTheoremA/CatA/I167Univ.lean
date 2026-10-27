module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Assembly
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Field
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Tri
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CLin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CUni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CSymp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthFam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167


theorem i167Exc3_holds : I167Exc3 := by
  intro Ω _ _ p B X D J x hp hp2 hB hX hchev hBN hrk hsc hcard hD hJ hDJ hJt hcase hxD hxc hDx hnf hhalf hinn hcl hp3
  exact false_of_exc3 hp hp2 hB hX hchev hBN hrk hsc hcard hD hJ hDJ hJt hcase hxD hxc hDx hnf hhalf hinn hcl hp3

theorem i167Exc_holds : I167Exc := by
  intro Ω _ _ p B X D J x hp hp2 hB hX hchev hBN hrk hsc hcard hD hJ hDJ hJt hcase hxD hxc hDx hnf hhalf hinn hcl hp3
  exact false_of_exc hp hp2 hB hX hchev hBN hrk hsc hcard hD hJ hDJ hJt hcase hxD hxc hDx hnf hhalf hinn hcl hp3

theorem i167Univ_holds : T123C.I167Univ :=
  i167Univ_of_cases i167Field_holds i167Tri_holds
    (i167Class_of_families i167CLin_holds i167CUni_holds i167CSymp_holds i167COrth_holds)
    i167Exc3_holds i167Exc_holds

end CFSG.LocalAnalysis.GLTheoremA.I167

end
