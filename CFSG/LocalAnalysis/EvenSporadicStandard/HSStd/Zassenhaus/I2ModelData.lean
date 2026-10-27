module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.I2Mats
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.SpecialData

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.I2

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.Certificates.Native
  CFSG.RankThree.Native

@[expose] def i2R : Array (Array ℕ) := #[
#[
    42, 5, 11, 67, 63, 1, 84, 94, 51, 28, 29, 12, 71, 88, 9, 31, 61, 83, 16, 25, 48, 90, 78, 89,
    15, 19, 68, 66, 77, 7, 47, 39, 32, 40, 37, 44, 36, 21, 96, 24, 30, 87, 54, 74, 60, 52, 80,
    33, 82, 4, 58, 8, 17, 97, 55, 0, 72, 18, 3, 81, 86, 57, 59, 99, 65, 6, 95, 50, 26, 27, 70, 2,
    91, 76, 43, 56, 73, 14, 23, 20, 41, 85, 79, 45, 64, 62, 35, 46, 38, 22, 34, 75, 92, 98, 10,
    69, 13, 53, 93, 49],
#[
    35, 5, 38, 45, 46, 1, 77, 66, 97, 6, 69, 88, 13, 2, 84, 90, 82, 3, 79, 93, 16, 24, 62, 81,
    34, 98, 73, 29, 65, 95, 56, 21, 32, 91, 31, 54, 36, 15, 12, 37, 72, 4, 86, 74, 42, 50, 99,
    75, 18, 80, 17, 53, 67, 51, 60, 44, 33, 20, 52, 78, 0, 48, 23, 87, 9, 14, 10, 83, 76, 7, 70,
    96, 47, 26, 43, 40, 68, 64, 85, 61, 63, 22, 57, 58, 28, 89, 55, 49, 71, 59, 39, 30, 92, 19,
    27, 94, 11, 8, 25, 41]]

@[expose] def selA (a : Array ℕ) (b : ZMod 2) : Array ℕ := if b = 0 then idA 100 else a

@[expose] def vecEA (v : Vec) : Array ℕ :=
  compA 100 (selA zasE0Gens[0]! (v 0)) (compA 100 (selA zasE0Gens[1]! (v 1))
    (compA 100 (selA zasE0Gens[2]! (v 2)) (compA 100 (selA zasE0Gens[3]! (v 3)) (idA 100))))

@[noinline, expose] def i2ModelOK : Bool :=
  decide (∀ j : Fin 2, ∀ i : Fin 4,
    eqA 100 (zasConj zasNGens[j.1]! zasE0Gens[i.1]!) (vecEA (rho j i)) = true) &&
  decide (∀ i : Fin 4, eqA 100 (zasConj i2R[0]! zasE0Gens[i.1]!) (vecEA (kx i)) = true) &&
  decide (∀ i : Fin 4, eqA 100 (zasConj i2R[1]! zasE0Gens[i.1]!) (vecEA (ky i)) = true) &&
  validA 100 i2R[0]! && validA 100 i2R[1]! &&
  zasMem zasE0Cert (compA 100 i2R[0]! i2R[0]!) && zasMem zasE0Cert (compA 100 i2R[1]! i2R[1]!) &&
  zasMem zasE0Cert (compA 100 (compA 100 i2R[0]! i2R[1]!) (compA 100 i2R[0]! i2R[1]!)) &&
  zasMem zasNCert i2R[0]! && zasMem zasNCert i2R[1]! &&
  (zasNCert.pts.toList.all fun x =>
    !decide (∀ i : Fin 4, eqA 100 (compA 100 x zasE0Gens[i.1]!) (compA 100 zasE0Gens[i.1]! x) = true) ||
      zasMem zasE0Cert x)

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.I2
