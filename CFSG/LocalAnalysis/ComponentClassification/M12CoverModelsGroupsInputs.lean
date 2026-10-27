module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsCocycle

public section
namespace CFSG.ComponentClassification.M12Cover.InternalSylow

open CFSG.ComponentClassification.CentralCover

@[expose] def centerCheckN (N : ℕ) (mul : ℕ → ℕ → ℕ) : Bool :=
  (List.range N).all fun z =>
    if z == 0 || z == 27 || z == 64 || z == 91 then (List.range N).all fun x => mul z x == mul x z
    else (List.range 9).any fun x => mul z x != mul x z

@[expose] def isCentralLabel (z : ℕ) : Bool := z == 0 || z == 27 || z == 64 || z == 91

@[expose] def zN (c : ℕ) : ℕ := if c % 2 = 1 then 64 else 0

@[expose] def tmulN (ε X Y : ℕ) : ℕ :=
  starN (starN (X % 128) (if (X / 128) % 2 = 1 then tauN lamIdx (Y % 128) else Y % 128))
      (zN (ε * (X / 128) * (Y / 128))) +
    128 * ((X / 128 + Y / 128) % 2)

end CFSG.ComponentClassification.M12Cover.InternalSylow
