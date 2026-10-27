module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore

public section

namespace CFSG.QuasithinUnique.A6Facts.Core

theorem p0_cent_aut : p0Lit.all (fun a => !(p0Lit.all fun p => cmul a p == cmul p a) || a == cid ||
    autL.all (fun c => !(cmul c a == cmul a c) || p0Lit.contains c)) = true := by
  decide +kernel

theorem psl_build6 : pslLit6 = buildCodes (List.range 6) pslGen6 pslTree := by decide +kernel

theorem psl_tbl6 : tblCheckC (List.range 6) pslGen6 pslLit6 pslTbl = true := by decide +kernel

theorem psl_nodup6 : pslLit6.Nodup := by decide +kernel

theorem psl_head : pslLit[0]? = some cid ∧ pslLit6[0]? = some (List.range 6) := by decide +kernel

@[expose] def tFrobC : List Nat := [0, 1, 2, 6, 7, 8, 3, 4, 5, 9]

theorem frob_involution : cmul tFrobC tFrobC = cid := by decide +kernel

theorem tau6_involution : cmul tau6 tau6 = List.range 6 := by decide +kernel

theorem frob_not_psl : pslLit.contains tFrobC = false := by decide +kernel

theorem psl_length6 : pslLit6.length = 360 := by decide +kernel

theorem frob_conj : ∀ k < 3, ∃ i < 360,
    pslLit[i]? = some (cmul (cmul tFrobC (pslGenC.getD k [])) tFrobC) ∧
      pslLit6[i]? = some (cmul (cmul tau6 (pslGen6.getD k [])) tau6) := by
  decide +kernel

end CFSG.QuasithinUnique.A6Facts.Core
