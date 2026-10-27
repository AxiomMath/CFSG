module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

namespace CFSG.ComponentClassification.CatFC

@[expose] def SporadicInnerRow : TauCeti.SporadicName → ℕ → Prop
  | .Co1, c => c = 251596800
  | .Co2, _ => False
  | .Co3, c => c = 1451520 ∨ c = 95040
  | .B, c => c = 76532479683774853939200 ∨ c = 3311126603366400
  | .M, c => 2 ^ 41 ∣ c ∧ ¬ 2 ^ 42 ∣ c
  | .J4, _ => False
  | .Th, _ => False
  | .HN, c => c = 44352000
  | .HS, c => c = 360
  | .McL, c => c = 20160
  | .Fi22, c => c = 9196830720
  | .Fi23, c => c = 64561751654400 ∨ c = 9196830720
  | .Fi24Prime, c => c = 64561751654400
  | .Ly, c => c = 19958400
  | .Suz, c => c = 20160
  | .ONan, c => c = 20160
  | .He, c => c = 20160
  | .Ru, c => ¬ 3 ∣ c
  | .M22, c => c ≠ 20160
  | .M23, c => c ≠ 20160
  | .M24, c => c ≠ 20160
  | .J2, c => c ≠ 20160
  | _, _ => True

@[expose] def SporadicOuterRow : TauCeti.SporadicName → ℕ → Prop
  | .HN, c => c = 1814400
  | .HS, c => c = 20160 ∨ c ∣ 1920
  | .McL, c => c = 7920
  | .Fi22, c => c = 174182400 ∨ c = 1451520
  | .Fi24Prime, c => c = 4089470473293004800 ∨ c = 9196830720
  | .Suz, c => c = 95040 ∨ c = 604800
  | .ONan, c => c = 175560
  | .He, c => c ∣ 15120
  | .M22, c => c ≠ 20160
  | .M23, c => c ≠ 20160
  | .M24, c => c ≠ 20160
  | .J2, c => c ≠ 20160
  | .M11, _ => True
  | .M12, _ => True
  | .J1, _ => True
  | .J3, _ => True
  | _, _ => False

end CFSG.ComponentClassification.CatFC
