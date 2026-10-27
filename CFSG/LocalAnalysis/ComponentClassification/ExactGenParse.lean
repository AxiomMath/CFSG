module

public import CFSG.LocalAnalysis.ComponentClassification.ExactGenCert

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2.ExactFin

structure Rd where
  toks : Array ℤ
  pos : ℕ

abbrev RdM := StateM Rd

@[expose] def rdInt : RdM ℤ := do
  let s ← get
  set { s with pos := s.pos + 1 }
  return s.toks[s.pos]!

@[expose] def rdNat : RdM ℕ := do
  return (← rdInt).toNat

@[expose] def rdList {α : Type} (f : RdM α) : RdM (List α) := do
  let len ← rdNat
  let mut out : Array α := #[]
  for _ in [0:len] do
    out := out.push (← f)
  return out.toList

@[expose] def rdArr {α : Type} (f : RdM α) : RdM (Array α) := do
  let len ← rdNat
  let mut out : Array α := #[]
  for _ in [0:len] do
    out := out.push (← f)
  return out

@[expose] def rdWord : RdM (List ℤ) := rdList rdInt

@[expose] def rdWords : RdM (List (List ℤ)) := rdList rdWord

@[expose] def rdPerm (n : ℕ) : RdM (Array ℕ) := do
  let mut out : Array ℕ := Array.mkEmpty n
  for _ in [0:n] do
    out := out.push (← rdNat)
  return out

@[expose] def rdChain (n : ℕ) : RdM ChainData := do
  let S ← rdArr (rdPerm n)
  let k ← rdNat
  let base ← rdList rdNat
  let W ← rdArr rdWord
  let chunks ← rdNat
  return { S := S, k := k, base := base, W := W, chunks := chunks }

@[expose] def rdCtx (n : ℕ) : RdM Ctx := do
  let chP ← rdChain n
  let chN ← rdChain n
  let normW ← rdWords
  let transW ← rdWords
  let stabLetters ← rdList rdNat
  return { chP := chP, chN := chN, normW := normW, transW := transW, stabLetters := stabLetters }

@[expose] def rdCover : RdM CoverCert := do
  let ws ← rdWords
  let cj ← rdList (do
    let j ← rdNat
    let w ← rdWord
    return (j, w))
  return { ws := ws, cj := cj }

@[expose] def rdGen : RdM GenCert := do
  let Aw ← rdWords
  let ka ← rdList rdNat
  let Bw ← rdWords
  let kb ← rdList rdNat
  let pw ← rdWords
  return { Aw := Aw, ka := ka, Bw := Bw, kb := kb, pw := pw }

@[expose] def rdRep (n : ℕ) : RdM RepCert := do
  let nuW ← rdWord
  let chC ← rdChain n
  let cgW ← rdWords
  let par ← rdList (do
    let p ← rdNat
    let l ← rdInt
    return (p, l))
  let ord ← rdList rdNat
  let chX ← rdChain n
  let xgW ← rdWords
  let xnorm ← rdList rdWords
  let xcomm ← rdList rdWords
  let chT ← rdChain n
  let tgW ← rdWords
  let sylA ← rdNat
  let sylM ← rdNat
  let tel ← rdCover
  let epsW ← rdWords
  let gens ← rdList rdGen
  return {
    nuW := nuW, chC := chC, cgW := cgW, par := par, ord := ord, chX := chX, xgW := xgW,
    xnorm := xnorm, xcomm := xcomm, chT := chT, tgW := tgW, sylA := sylA, sylM := sylM, tel := tel,
    epsW := epsW, gens := gens }

@[expose] def rdFC (n : ℕ) : RdM FCCert := do
  let ctx ← rdCtx n
  let chTN ← rdChain n
  let tnW ← rdWords
  let sylA ← rdNat
  let sylM ← rdNat
  let tel ← rdCover
  let reps ← rdList (rdRep n)
  return {
    ctx := ctx, chTN := chTN, tnW := tnW, sylA := sylA, sylM := sylM, tel := tel, reps := reps }

@[expose] def fcTokens (txt : String) : Array ℤ :=
  ((txt.splitToList Char.isWhitespace).filter (fun s => !s.isEmpty)).toArray.map String.toInt!

@[expose] def parseFC (n : ℕ) (txt : String) : FCCert :=
  ((rdFC n).run' { toks := fcTokens txt, pos := 0 })

end CFSG.ComponentClassification.SolMax.SwapP2.ExactFin
