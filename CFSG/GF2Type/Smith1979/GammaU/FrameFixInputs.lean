module

public import Certificates.Data.CFSGNative.GammaU.Pairs

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GammaU.Native

@[expose] def frameFixAt (i : Nat) : Bool :=
  let S := spanList d0
  ((List.range 4096).all fun n =>
      n == 0 || n == a0 || !((compGens i).all fun g => appN g n == n)) &&
    (compOf i).all (fun r => appN r a0 == a0) &&
    (compOf i).all (fun r =>
      (List.range 4096).all fun x => f0b x a0 || S.contains (appN r x ^^^ x)) &&
    d0.all (fun d => d == a0 || (compOf i).any fun l =>
      (List.range 4096).any fun x => !f0b x a0 && (appN l x ^^^ x) == d) &&
    (n2Gens i).all gammaUN

@[expose] def frameFixCheck (_ : Unit := ()) : Bool := frameFixAt 0 && frameFixAt 1

end CFSG.GF2Type.Smith1979.GammaU.StepA
