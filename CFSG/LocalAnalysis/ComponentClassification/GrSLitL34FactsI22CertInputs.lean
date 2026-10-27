module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsLocalCertInputs

public section

namespace CFSG.ASVolI

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts in
@[expose] def burnsideI22P3_o2Check (ws : List (List ℕ)) (inU : ℕ → Bool) : Bool :=
  let ET := (enumBFS 42 (wordTabs wT₀) 64).tabs
  let gens := wordTabs ws
  let ginv := gens.map (invTab 42)
  invsOK 42 gens ginv &&
    allBelow 64 fun k => inU k ||
      anyBelow gens.size fun j => notInOK ET (conjTab 42 gens[j]! ginv[j]! (tgT k))

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts in
@[expose] def burnsideI22P3_transCheck (ws : List (List ℕ)) (inU : ℕ → Bool) (k₀ : ℕ) : Bool :=
  let EP := enumBFS 42 (wordTabs ws) 960
  enumOK 42 (wordTabs ws) EP && EP.tabs.size == 960 && inU k₀ && k₀ != 0 &&
    allBelow 64 fun k => !inU k || k == 0 ||
      anyBelow EP.tabs.size fun i =>
        comp 42 EP.tabs[i]! (tgT k₀) == comp 42 (tgT k) EP.tabs[i]!

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts in
@[expose] def burnsideI22P3_prodCheck (inU inV : ℕ → Bool) : Bool :=
  allBelow 64 fun k => anyBelow 64 fun a => inU a && anyBelow 64 fun b =>
    inV b && comp 42 (tgT a) (tgT b) == tgT k

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts in
@[expose] def burnsideI22P3_ncCheck (a b : ℕ) : Bool :=
  !(comp 42 (tgT a) (tgT b) == comp 42 (tgT b) (tgT a))

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts in
@[expose] def burnsideI22P3_check (_ : Unit := ()) : Bool :=
  burnsideI22P3_o2Check wP₁ (fun k => k < 16) &&
    burnsideI22P3_o2Check wP₂ (fun k => k % 4 == 0) &&
    burnsideI22P3_transCheck wP₁ (fun k => k < 16) 4 &&
    burnsideI22P3_transCheck wP₂ (fun k => k % 4 == 0) 4 &&
    burnsideI22P3_prodCheck (fun k => k < 16) (fun k => k % 4 == 0) &&
    burnsideI22P3_prodCheck (fun k => k % 4 == 0) (fun k => k < 16) &&
    burnsideI22P3_ncCheck 1 16

end CFSG.ASVolI
