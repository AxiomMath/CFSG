module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UResDef
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UGlue
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UOfRes
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UClMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA


theorem qsFamF5URes_holds : QSFamF5URes := qsFamF5URes_of_cls qsF5UCls_holds

theorem qsFamF5U_holds : QSFamF5U := qsFamF5U_of_res qsFamF5URes_holds

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
