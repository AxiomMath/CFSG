module

public import CFSG.RankThree.Asc83Table.MatCertDefs

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

structure NAct where
  reg : Nat
  ord : Nat
  mat : List Nat
deriving Inhabited

structure NMod where
  basis : List Nat
  indep : List (List Nat × Nat)
  acts : List NAct
deriving Inhabited

@[expose] def allVecs (p : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (List.range p).flatMap fun a => (allVecs p n).map (a :: ·)

@[expose] def NMod.word (m : NMod) (c : List Nat) : Word :=
  (List.range m.basis.length).map fun k => (m.basis.getD k 0, c.getD k 0)

@[expose] def NMod.col (m : NMod) (g : NAct) (i : Nat) : Word :=
  (List.range m.basis.length).map fun k =>
    (m.basis.getD k 0, g.mat.getD (m.basis.length * k + i) 0)

@[expose] def NMod.commFacts (m : NMod) : List MFact :=
  (List.range m.basis.length).flatMap fun i =>
    ((List.range m.basis.length).filter (i < ·)).map fun j =>
      MFact.eq [(m.basis.getD i 0, 1), (m.basis.getD j 0, 1)]
        [(m.basis.getD j 0, 1), (m.basis.getD i 0, 1)]

@[expose] def NMod.facts (p : Nat) (m : NMod) : List MFact :=
  m.basis.map (fun b => MFact.ord b p) ++ m.commFacts ++
  m.indep.map (fun v => MFact.ne (m.word v.1) [] v.2) ++
  m.acts.flatMap fun g => MFact.ord g.reg g.ord ::
    (List.range m.basis.length).map fun i =>
      MFact.conj g.reg [(m.basis.getD i 0, 1)] (m.col g i)

@[expose] def NMod.wf (p : Nat) (m : NMod) : Bool :=
  decide (2 ≤ p) &&
  m.acts.all (fun g => decide (g.mat.length = m.basis.length * m.basis.length)) &&
  (allVecs p m.basis.length).all fun c => c.all (· == 0) || m.indep.any fun q => q.1 == c

@[expose] def kd (a b : Nat) : Int := if a = b then 1 else 0

@[expose] def fsum (N : Nat) (f : Fin N → Int) : Int := ((List.finRange N).map f).sum

@[expose] def NAct.ent (g : NAct) (n k i : Nat) : Int := ((g.mat.getD (n * k + i) 0 : Nat) : Int)

@[expose] def NMod.funOK (p : Nat) (m : NMod) (cf : Nat → Nat → Nat → Int) : Bool :=
  (List.finRange m.basis.length).all fun r₀ => (List.finRange m.basis.length).all fun r =>
    (fsum m.acts.length (fun j => fsum m.basis.length fun s =>
        cf r₀.val j.val s.val *
          ((m.acts.get j).ent m.basis.length r.val s.val - kd r.val s.val)) -
      kd r.val r₀.val) % (p : Int) == 0

@[expose] def NMod.altOK (p : Nat) (m : NMod) (ci : Nat → Nat → Nat → Nat → Nat → Int)
    (ct : Nat → Nat → Nat → Nat → Int) (tgt : Nat → Nat → Nat → Nat → Int) : Bool :=
  (List.finRange m.basis.length).all fun a₀ => (List.finRange m.basis.length).all fun b₀ =>
    (List.finRange m.basis.length).all fun a => (List.finRange m.basis.length).all fun b =>
      (fsum m.acts.length (fun j => fsum m.basis.length fun r => fsum m.basis.length fun s =>
          ci a₀.val b₀.val j.val r.val s.val *
            ((m.acts.get j).ent m.basis.length a.val r.val *
              (m.acts.get j).ent m.basis.length b.val s.val -
              kd a.val r.val * kd b.val s.val)) +
        fsum m.basis.length (fun r => fsum m.basis.length fun s =>
          ct a₀.val b₀.val r.val s.val *
            (kd a.val r.val * kd b.val s.val + kd a.val s.val * kd b.val r.val)) -
        tgt a₀.val b₀.val a.val b.val) % (p : Int) == 0

@[expose] def tgtAlt (a₀ b₀ a b : Nat) : Int := kd a a₀ * kd b b₀

@[expose] def tgtNondeg (n : Nat) (q : List Nat) (a₁ b₁ a₀ b₀ a b : Nat) : Int :=
  kd a a₀ * kd b b₀ - ((q.getD (n * a₀ + b₀) 0 : Nat) : Int) * (kd a a₁ * kd b b₁)


@[expose] def absCheck {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (nregs : Nat)
    (prog : List Op) (p : Nat) (m : NMod) (cf : Nat → Nat → Nat → Int)
    (ci : Nat → Nat → Nat → Nat → Nat → Int) (ct : Nat → Nat → Nat → Nat → Int)
    (q : List Nat) (a₁ b₁ : Nat) : Bool :=
  mcertCheck O sA sB ⟨nregs, prog, m.facts p⟩ && m.wf p && decide (m.basis.length ≤ 4) &&
  decide (a₁ < m.basis.length) && decide (b₁ < m.basis.length) && m.funOK p cf &&
  m.altOK p ci ct (tgtNondeg m.basis.length q a₁ b₁)

end CFSG.AGLEmbedding.R3
