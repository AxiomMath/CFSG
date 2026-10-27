module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinFour
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Cls3
public import Certificates.Certificate55104

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native FinGlue FinFour
  CFSG.ComponentClassification.PSL3Four

namespace FinL34


theorem noFourPerfIn_R : NoFourPerfIn R :=
  noFourPerfIn_of_reps (c := 1) (fun x hx => Or.inl hx) (mul_one 1)
    (fun x hx => by simpa using hx) [r₁, r₂, r₃, r₄] Nat.prime_two Nat.prime_three (by norm_num)
    (a := 30) (b := 30) Certificates.certificate55104.1 Certificates.certificate55104.2

end FinL34

theorem finCellB_l34 {Y : Type}
    [Group Y] (hY : LieModel Y .PSL 3 2 2) : FinCellB Y := by
  obtain ⟨e⟩ := CFSG.ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel hY
  exact finCellB_of (NoFourPerf.of_equiv
    (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.Cls3.conjIso.trans (MulAut.congr e.symm)).symm
    (NoFourPerf.of_in FinL34.noFourPerfIn_R))

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
