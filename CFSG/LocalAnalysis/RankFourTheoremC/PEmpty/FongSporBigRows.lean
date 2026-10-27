module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigOrd
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigSound
public import Certificates.Certificate40340
public import Certificates.Certificate40341
public import CFSG.Sporadic.Bridge.J4Surj
public import CFSG.Sporadic.Bridge.LySurj
public import CFSG.Sporadic.Bridge.ONSurj
public import CFSG.Sporadic.ON
public import CFSG.Sporadic.Bridge.ThSurj
public import CFSG.RankThree.OddKernel.SporadicKernelTh

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Blueprint CFSG.SectionRank

set_option maxRecDepth 20000

theorem row_J4_23 :
    KFactSporLocalRow .J4 23 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  obtain ⟨z₀, n₀, hz₀, hn₀⟩ := MGen.exists_norm_of_checkBase (spec2 112) NativeSporadic.J4Seed1
    NativeSporadic.J4Seed2 j4_23_claims Certificates.certificate40340.1 _
    (List.mem_singleton_self _)
  exact row_of_normalizing NativeSporadic.J4 (fun G _ h => by obtain ⟨e⟩ := h; exact ⟨e.trans b.symm⟩) (e := 21) (m := 41377816699065)
    (by rw [CFSG.Sporadic.J4.card_J4]; norm_num) (by decide) (by norm_num) hz₀ hn₀ (resGenSet 23 22)
    (fun x hx => mem_resGenSet hx) (by decide +kernel)

theorem row_Ly_31 :
    KFactSporLocalRow .Ly 31 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv
  obtain ⟨z₀, n₀, hz₀, hn₀⟩ := MGen.exists_norm_of_checkBase (specP 5 111) NativeSporadic.LySeed1
    NativeSporadic.LySeed2 ly_31_claims Certificates.certificate40340.2 _
    (List.mem_singleton_self _)
  exact row_of_normalizing NativeSporadic.Ly (fun G _ h => by obtain ⟨e⟩ := h; exact ⟨e.trans b.symm⟩) (e := 8) (m := 202207730484375)
    (by rw [CFSG.Sporadic.Ly.card_Ly]; norm_num) (by decide) (by norm_num) hz₀ hn₀ (resGenSet 31 30)
    (fun x hx => mem_resGenSet hx) (by decide +kernel)

theorem row_ON_31 :
    KFactSporLocalRow .ONan 31 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  obtain ⟨z₀, n₀, hz₀, hn₀⟩ := PClaim.exists_norm_of_check (specP 3 154) NativeSporadic.ONSeed1
    NativeSporadic.ONSeed2 on_31_claims Certificates.certificate40341.1
  exact row_of_normalizing NativeSporadic.ON (fun G _ h => by obtain ⟨e⟩ := h; exact ⟨e.trans b.symm⟩) (e := 9) (m := 900030285)
    (by rw [CFSG.Sporadic.ON.card_ON]; norm_num) (by decide) (by norm_num) hz₀ hn₀ (resGenSet 31 25)
    (fun x hx => mem_resGenSet hx) (by decide +kernel)

theorem row_Th_31 :
    KFactSporLocalRow .Th 31 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  obtain ⟨z₀, n₀, hz₀, hn₀⟩ := PClaim.exists_norm_of_check (spec2 248) NativeSporadic.ThSeed1
    NativeSporadic.ThSeed2 th_31_claims Certificates.certificate40341.2.1
  obtain ⟨g₀, hg₀⟩ := OClaim.exists_orderOf_of_check (spec2 248) NativeSporadic.ThSeed1
    NativeSporadic.ThSeed2 th_ord4_claims Certificates.certificate40341.2.2
  exact row_of_normalizing_sylow NativeSporadic.Th (fun G _ h => by obtain ⟨e⟩ := h; exact ⟨e.trans b.symm⟩) (e := 15) (m := 2769346432125)
    (by rw [CFSG.RankThree.OddKernel.card_Th_eq]; norm_num) (by decide) (by norm_num) hz₀ hn₀
    (resGenSet 31 25) (fun x hx => mem_resGenSet hx) (by decide +kernel) (g₀ := g₀) (by simpa [th_ord4_claims] using hg₀)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
