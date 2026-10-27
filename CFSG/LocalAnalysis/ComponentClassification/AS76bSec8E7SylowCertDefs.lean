module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneOddDerivationTests

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open CFSG.Blueprint.Chevalley CFSG.SeitzReduction

section Deriv

inductive E7NStep : Type
  | seed (γ s : Fin Tag.E7.rank → ℤ)
  | close (a b : Fin Tag.E7.rank → ℤ)
  | tuple (ω : List (Fin Tag.E7.rank))

@[expose] def e7SCommB (β σ : Fin Tag.E7.rank → ℤ) : Bool :=
  !oddDerivVecEq β (-σ) && oddDerivNotRootB .E7 (β + σ)

@[expose] def e7WordImage (ω : List (Fin Tag.E7.rank)) (F : List (Fin Tag.E7.rank → ℤ)) :
    List (Fin Tag.E7.rank → ℤ) :=
  F.map fun σ => ω.foldr (reflect .E7) σ

@[expose] def e7NStepRoots (F : List (Fin Tag.E7.rank → ℤ)) :
    E7NStep → List (Fin Tag.E7.rank → ℤ)
  | .seed γ s => [γ + s]
  | .close a b => [a + b]
  | .tuple ω => e7WordImage ω F

@[expose] def e7NStepB (F D : List (Fin Tag.E7.rank → ℤ)) : E7NStep → Bool
  | .seed γ s => oddDerivIsRootB .E7 γ && oddDerivMemB s F && oddDerivIsRootB .E7 (γ + s) &&
      !oddDerivVecEq γ s && !oddDerivVecEq γ (-s) &&
      F.all (fun σ => oddDerivVecEq σ s || e7SCommB γ σ) && F.all (e7SCommB (γ + s))
  | .close a b => oddDerivMemB a D && oddDerivIsRootB .E7 a && oddDerivIsRootB .E7 b &&
      oddDerivIsRootB .E7 (a + b) && !oddDerivVecEq a b && !oddDerivVecEq a (-b) &&
      F.all (e7SCommB b)
  | .tuple ω => (e7WordImage ω F).all fun t => F.all (e7SCommB t)

@[expose] def e7NDeriv (F : List (Fin Tag.E7.rank → ℤ)) :
    List E7NStep → List (Fin Tag.E7.rank → ℤ) → Option (List (Fin Tag.E7.rank → ℤ))
  | [], D => some D
  | st :: sts, D => if e7NStepB F D st then e7NDeriv F sts (D ++ e7NStepRoots F st) else none

end Deriv

section Lists

@[expose] def e7NodupB : List (Fin Tag.E7.rank → ℤ) → Bool
  | [] => true
  | a :: l => !oddDerivMemB a l && e7NodupB l

@[expose] def e7Erase (a : Fin Tag.E7.rank → ℤ) : List (Fin Tag.E7.rank → ℤ) →
    List (Fin Tag.E7.rank → ℤ)
  | [] => []
  | b :: l => if oddDerivVecEq b a then l else b :: e7Erase a l

end Lists

section Ann

@[expose] def e7AnnWalkB (S L : List (Fin Tag.E7.rank → ℤ)) :
    List ℕ → List (Fin Tag.E7.rank → ℤ) → Bool
  | [], _ => true
  | c :: cs, W =>
    if (decide (oddDerivHeight (decodeVec c : Fin Tag.E7.rank → ℤ) ≤ 0) ||
        L.any fun γ => CFSG.LieType.Ree.vecBEq γ (decodeVec c)) = true then
      e7AnnWalkB S L cs W
    else
      match W with
      | [] => false
      | δ :: W' => oddDerivMemB δ S && oddDerivIsRootB .E7 (decodeVec c + δ) &&
          e7AnnWalkB S L cs W'

@[expose] def e7AnnB (S L W : List (Fin Tag.E7.rank → ℤ)) : Bool :=
  (S.all fun δ => oddDerivIsRootB .E7 δ && decide (0 < oddDerivHeight δ)) &&
    (L.all fun γ => oddDerivIsRootB .E7 γ && decide (0 < oddDerivHeight γ)) &&
    e7AnnWalkB S L Tag.E7.rootCertificate.roots W &&
    L.all fun γ => L.all fun γ' =>
      decide (17 < oddDerivHeight (γ + γ')) || oddDerivNotRootB .E7 (γ + γ')

end Ann

section Kill

@[expose] def e7KillStepB (D C : List (Fin Tag.E7.rank → ℤ)) (ℓ β : Fin Tag.E7.rank → ℤ) :
    Bool :=
  oddDerivMemB ℓ C && oddDerivMemB β D && oddDerivIsRootB .E7 β &&
    oddDerivIsRootB .E7 (ℓ + β) && decide (0 < oddDerivHeight (ℓ + β)) &&
    !oddDerivMemB (ℓ + β) C && !oddDerivVecEq β ℓ &&
    C.all (fun y => !oddDerivVecEq β (-y) && (oddDerivVecEq y ℓ || oddDerivNotRootB .E7 (β + y))) &&
    !oddDerivVecEq β (-(ℓ + β)) && oddDerivNotRootB .E7 (β + (ℓ + β)) &&
    C.all (e7SCommB (ℓ + β)) && C.all (fun s => !oddDerivMemB (s - β) (C ++ [ℓ + β]))

@[expose] def e7KillsB (D : List (Fin Tag.E7.rank → ℤ)) :
    List (Fin Tag.E7.rank → ℤ) → List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ)) →
      Option (List (Fin Tag.E7.rank → ℤ))
  | C, [] => some C
  | C, p :: ks => if e7KillStepB D C p.1 p.2 then e7KillsB D (e7Erase p.1 C) ks else none

end Kill

section Mix

structure E7Mix : Type where
  word : List (Fin Tag.E7.rank)
  rhos : List (Fin Tag.E7.rank → ℤ)
  eqs : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ))

@[expose] def e7MixSources (F F' : List (Fin Tag.E7.rank → ℤ)) (ρ : Fin Tag.E7.rank → ℤ) :
    List (Fin Tag.E7.rank → ℤ) :=
  F'.filterMap fun β =>
    if oddDerivMemB (ρ - β) F && !oddDerivVecEq β (ρ - β) then some (ρ - β) else none

@[expose] def e7ListEqB : List (Fin Tag.E7.rank → ℤ) → List (Fin Tag.E7.rank → ℤ) → Bool
  | [], [] => true
  | a :: l, b :: l' => oddDerivVecEq a b && e7ListEqB l l'
  | _, _ => false

@[expose] def e7MixB (F : List (Fin Tag.E7.rank → ℤ)) (m : E7Mix) : Bool :=
  e7NodupB m.rhos &&
    m.rhos.all (fun ρ => oddDerivIsRootB .E7 ρ && decide (0 < oddDerivHeight ρ) &&
      !oddDerivMemB ρ F) &&
    m.rhos.all (fun ρ => F.all (e7SCommB ρ)) &&
    m.rhos.all (fun ρ => m.rhos.all fun ρ' => oddDerivVecEq ρ ρ' || e7SCommB ρ ρ') &&
    (e7WordImage m.word F).all (fun β => oddDerivIsRootB .E7 β &&
      (F ++ m.rhos).all fun y => !oddDerivVecEq β (-y) &&
        (oddDerivNotRootB .E7 (β + y) || oddDerivMemB (β + y) (F ++ m.rhos))) &&
    F.all (fun s => (e7WordImage m.word F).all fun β => !oddDerivMemB (s - β) (F ++ m.rhos)) &&
    m.rhos.all (fun ρ => (e7WordImage m.word F).all fun β => !oddDerivMemB (ρ - β) m.rhos) &&
    m.rhos.all (fun ρ => m.eqs.any fun e => oddDerivVecEq e.1 ρ) &&
    m.eqs.all fun e => oddDerivMemB e.1 m.rhos &&
      e7ListEqB (e7MixSources F (e7WordImage m.word F) e.1) [e.2.1, e.2.2]

end Mix

section Conn

@[expose] def e7ConnStep (acc : List (Fin Tag.E7.rank → ℤ))
    (p : (Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ)) : List (Fin Tag.E7.rank → ℤ) :=
  if oddDerivMemB p.1 acc then (if oddDerivMemB p.2 acc then acc else p.2 :: acc)
  else if oddDerivMemB p.2 acc then p.1 :: acc else acc

@[expose] def e7ConnB : List (Fin Tag.E7.rank → ℤ) →
    List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ)) → Bool
  | [], _ => false
  | s₀ :: F, pairs => (s₀ :: F).all fun s => oddDerivMemB s (pairs.foldl e7ConnStep [s₀])

end Conn

section Cert

structure E7SylowCert : Type where
  steps : List E7NStep
  tail : ℤ
  annS : List (Fin Tag.E7.rank → ℤ)
  annL : List (Fin Tag.E7.rank → ℤ)
  kills : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ))
  mixes : List E7Mix
  annW : List (Fin Tag.E7.rank → ℤ)

@[expose] def E7SylowCert.pairs (cert : E7SylowCert) :
    List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ)) :=
  cert.mixes.flatMap fun m => m.eqs.map fun e => (e.2.1, e.2.2)

@[expose] def e7SylowCheck (F : List (Fin Tag.E7.rank → ℤ)) (cert : E7SylowCert) : Bool :=
  match e7NDeriv F cert.steps [] with
  | none => false
  | some D =>
    decide (1 ≤ cert.tail) && decide (cert.tail ≤ 11) && oddDerivTailB .E7 cert.tail D &&
      cert.annS.all (fun δ => oddDerivMemB δ D) && e7AnnB cert.annS cert.annL cert.annW &&
      e7NodupB cert.annL &&
      (match e7KillsB D cert.annL cert.kills with
        | none => false
        | some C => decide (C.length ≤ F.length) && F.all fun s => oddDerivMemB s C) &&
      cert.mixes.all (e7MixB F) && e7ConnB F cert.pairs

end Cert

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
