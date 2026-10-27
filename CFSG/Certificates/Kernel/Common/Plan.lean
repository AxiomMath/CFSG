module

public import CFSG.Certificates.Kernel.Common.Chain
meta import all CFSG.Certificates.Kernel.Common.Chain
meta import all CFSG.Certificates.Kernel.Common.Harness

open Lean Elab Command

open CFSG.KC.Chain CFSG.KC.Load in
elab "#kc_plan " pre:ident path:str size:num hash:num : command => do
  let b ← readRepoPinned path.getString size.getNat hash.getNat
  withSync do
    discard <| loadPlan pre.getId b
