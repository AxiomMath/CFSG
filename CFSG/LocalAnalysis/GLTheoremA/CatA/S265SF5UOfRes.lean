module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UResDef
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UCenter
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UTw25

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA


theorem qsFamF5U_of_res (hres : QSFamF5URes) : QSFamF5U := by
  intro p Ω _ _ S B T x D K h hp hF
  subst hp
  refine hres Ω S B T x D K h hF (center_eq_bot_of_qsnl h hF) ?_
  intro m F _ hFd hθ
  obtain ⟨θ⟩ := hθ
  exact not_dvd_of_qsnl h hF hFd θ

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
