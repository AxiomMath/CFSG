module

public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.Open.MonsterDefs

public section

namespace CFSG.EvenSmallLie.Child3

open CFSG.EvenSmallLie.CatalogOrders CFSG.Assembly.LowTwoRank

@[expose] def glOrd (N : ℕ) : ℕ :=
  2 ^ (N * (N - 1) / 2) * ((List.range N).map fun i => 2 ^ (i + 1) - 1).prod

@[expose] def glPrimes12 : List (ℕ × ℕ) :=
  [(2, 66), (3, 8), (5, 3), (7, 4), (11, 1), (13, 1), (17, 1), (23, 1), (31, 2), (73, 1),
    (89, 1), (127, 1)]

@[expose] def glPrimes9 : List (ℕ × ℕ) :=
  [(2, 36), (3, 5), (5, 2), (7, 3), (17, 1), (31, 1), (73, 1), (127, 1)]

@[expose] def lieSearchV (pv : List (ℕ × ℕ)) (N : ℕ)
    (C : StatedLieTag → ℕ → ℕ → ℕ → ℕ → Bool) : Bool :=
  pv.all fun pe =>
    (List.range pe.2).all fun f =>
      searchTags.all fun t =>
        (List.range (if lieMin t = 0 then 1 else pe.2 + 2)).all fun n =>
          !(decide (lieMin t ≤ n) && lieAdm t pe.1 (f + 1) &&
              decide ((f + 1) * lieExp t n ≤ pe.2) && N % lieOrd t n (pe.1 ^ (f + 1)) == 0) ||
            C t n pe.1 (f + 1) (lieOrd t n (pe.1 ^ (f + 1)))

@[expose] def sectorTuple : StatedLieTag → ℕ → ℕ → ℕ → Bool
  | .PSL, n, p, _ => p == 2 || n == 2
  | .PSU, _, p, _ => p == 2
  | .PSp, _, p, _ => p == 2
  | .POmegaOdd, _, p, _ => p == 2
  | .G2, _, p, f => decide (p ^ f < 3)
  | .twistedB2, _, _, _ => true
  | .twistedG2, _, _, _ => true
  | _, _, _, _ => false

@[expose] def residualTuples12 : List (StatedLieTag × ℕ × ℕ × ℕ) :=
  [(.PSL, 3, 3, 2), (.PSU, 3, 3, 1), (.PSU, 4, 3, 1), (.PSU, 3, 5, 1), (.PSp, 2, 7, 1),
    (.POmegaPlus, 4, 2, 1), (.POmegaPlus, 5, 2, 1), (.POmegaPlus, 6, 2, 1),
    (.POmegaPlus, 7, 2, 1), (.POmegaMinus, 4, 2, 1), (.POmegaMinus, 5, 2, 1),
    (.POmegaMinus, 6, 2, 1), (.G2, 0, 2, 2), (.G2, 0, 3, 1), (.trialityD4, 0, 2, 1),
    (.F4, 0, 2, 1), (.E6, 0, 2, 1)]

@[expose] def residualTuples9 : List (StatedLieTag × ℕ × ℕ × ℕ) :=
  [(.PSU, 3, 3, 1), (.POmegaPlus, 4, 2, 1), (.POmegaPlus, 5, 2, 1), (.POmegaMinus, 4, 2, 1)]

@[expose] def filterCheck (l : List (StatedLieTag × ℕ × ℕ × ℕ)) (t : StatedLieTag)
    (n p f o : ℕ) : Bool :=
  !(o % 168 == 0) || sectorTuple t n p f || l.contains (t, n, p, f)

@[expose] def sporadicCard : TauCeti.SporadicName → ℕ
  | .M11 => 7920
  | .M12 => 95040
  | .M22 => 443520
  | .M23 => 10200960
  | .M24 => 244823040
  | .J1 => 175560
  | .J2 => 604800
  | .J3 => 50232960
  | .J4 => 86775571046077562880
  | .HS => 44352000
  | .McL => 898128000
  | .He => 4030387200
  | .Ru => 145926144000
  | .Suz => 448345497600
  | .ONan => 460815505920
  | .Co1 => 4157776806543360000
  | .Co2 => 42305421312000
  | .Co3 => 495766656000
  | .Fi22 => 64561751654400
  | .Fi23 => 4089470473293004800
  | .Fi24Prime => 1255205709190661721292800
  | .HN => 273030912000000
  | .Ly => 51765179004000000
  | .Th => 0
  | .B => CFSG.Open.monsterBabyOrder
  | .M => 0

@[expose] def residualSporadic12 : List TauCeti.SporadicName :=
  [.M22, .M23, .M24, .J2, .HS, .McL, .He, .Suz, .Co3, .Co2]

@[expose] def residualSporadic9 : List TauCeti.SporadicName := [.J2, .He]

end CFSG.EvenSmallLie.Child3
