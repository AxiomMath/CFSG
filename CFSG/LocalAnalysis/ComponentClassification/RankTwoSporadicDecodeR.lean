module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheck

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Cert

section DecodeR

variable (tk : Array ℕ) (regs : Array (Array ℕ))

@[expose] def rdReg (p : ℕ) : Array ℕ × ℕ := (regs[tk[p]!]!, p + 1)

@[expose] def rdGFacR (p : ℕ) : GFac × ℕ :=
  let a := rdReg tk regs (p + 1)
  let b := rdReg tk regs a.2
  (⟨tk[p]!, a.1, b.1⟩, b.2)

@[expose] def rdCFacR (p : ℕ) : CFac × ℕ :=
  let a := rdReg tk regs p
  let b := rdReg tk regs a.2
  (⟨a.1, b.1⟩, b.2)

@[expose] def rdNFacR (p : ℕ) : NFac × ℕ :=
  let l := rdListC tk (rdGFacR tk regs) (p + 1)
  (⟨tk[p]!, l.1⟩, l.2)

@[expose] def rdWitR (p : ℕ) : Wit × ℕ :=
  match tk[p]! with
  | 0 =>
    let w := rdListC tk (rdNFacR tk regs) (p + 1)
    (.order4 w.1 tk[w.2]!, w.2 + 1)
  | 1 =>
    let g := rdListC tk (rdPow tk (rdNFacR tk regs)) (p + 1)
    (.twoGroup g.1 tk[g.2]!, g.2 + 1)
  | 2 =>
    let g := rdListC tk (rdPow tk (rdGFacR tk regs)) (p + 1)
    let c := rdListC tk (rdPair tk) g.2
    let q := c.2
    let cj := rdListC tk (fun p => (tk[p]!, p + 1)) (q + 2)
    (.perfect g.1 c.1 tk[q]! tk[q + 1]! cj.1 tk[cj.2]! tk[cj.2 + 1]!, cj.2 + 2)
  | 3 => (.inX, p + 1)
  | 5 =>
    let c := rdReg tk regs (p + 3)
    let g := rdListC tk (rdPow tk (rdCFacR tk regs)) (c.2 + 2)
    let cm := rdListC tk (rdPair tk) g.2
    (.closing tk[p + 1]! tk[p + 2]! c.1 tk[c.2]! tk[c.2 + 1]! g.1 cm.1, cm.2)
  | _ => (.small, p + 1)

@[expose] def rdNodeR (p : ℕ) : Node × ℕ :=
  let b := rdListC tk (rdReg tk regs) p
  let w := rdWitR tk regs b.2
  let c := rdListC tk (fun p => (tk[p]!, p + 1)) w.2
  (⟨b.1.toArray, w.1, c.1.toArray⟩, c.2)

@[expose] def rdCensusR : CensusData :=
  let s := rdListC tk (rdReg tk regs) 0
  let r := rdListC tk (fun p => (tk[p]!, p + 1)) s.2
  let d := rdListC tk (rdNodeR tk regs) r.2
  ⟨s.1.toArray, r.1.toArray, d.1.toArray⟩

end DecodeR

@[expose] def decodeCertR (regs : Array (Array ℕ)) (s : String) : CensusData :=
  rdCensusR (decodeNats s) regs

end CFSG.ComponentClassification.RankTwoSporadic.Cert
