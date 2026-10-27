module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

open CFSG.QuasithinUnique.Unc25K1.Six

section DiagExt

variable {G H : Type} [Group G] [Group H] {R S : Type} [Mul R] [One R] [DecidableEq R] [Hashable R]
  [Mul S] [One S] [DecidableEq S] [Hashable S]

@[expose] def diagExtOK (e₁ : G → R) (e₂ : H → S) (depth : ℕ) (a : List G) (b : List H) (n m : ℕ) :
    Bool :=
  closedH (a.map e₁) (elts e₁ depth a) && (elts e₁ depth a).size == n &&
    closedH (b.map e₂) (elts e₂ depth b) && (elts e₂ depth b).size == m &&
    closedH ((a.zip b).map fun p => (e₁ p.1, e₂ p.2))
      (elts (fun p : G × H => (e₁ p.1, e₂ p.2)) depth (a.zip b)) &&
    (elts (fun p : G × H => (e₁ p.1, e₂ p.2)) depth (a.zip b)).size == n &&
    decide (a.length = b.length) &&
    (let K := ((elts (fun p : G × H => (e₁ p.1, e₂ p.2)) depth (a.zip b)).toList.filter
        fun r => r.2 == 1)
     K.all fun r => r.1 * r.1 == 1 && K.all fun s => r.1 * s.1 == s.1 * r.1)

end DiagExt

section Perfect

@[expose] def commProd {R : Type*} [Mul R] [One R] (gens : List R) : List CommWord → R
  | [] => 1
  | q :: l => (evalW gens q.1 * evalW gens q.2.1 * evalW gens q.2.2.1 * evalW gens q.2.2.2) *
      commProd gens l

variable {G : Type} [Group G] {R : Type} [Mul R] [One R] [DecidableEq R] [Hashable R]
  (enc : G → R)

@[expose] def perfOK (gens : List G) (cert : List (List CommWord)) : Bool :=
  decide (cert.length = gens.length) &&
    (gens.zip cert).all (fun p => commProd (gens.map enc) p.2 == enc p.1) &&
    cert.all fun l => l.all fun q =>
      evalW (gens.map enc) q.1 * evalW (gens.map enc) q.2.2.1 == 1 &&
        evalW (gens.map enc) q.2.1 * evalW (gens.map enc) q.2.2.2 == 1

end Perfect

end CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
