module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Sym6Check

public section

namespace CFSG.EvenSporadicStandard.M24Std.DResH

open CFSG.Blueprint CFSG.QuasithinUnique.Setup.X1

@[expose] def sext3Gens : List S24 := [Sym6.sxS, Sym6.sxT]

@[expose] def sext3WA : List ℤ := [-2, -2, -2, -2]

@[expose] def sext3WB : List ℤ := [1, -2, -2, 1, 2, 2, 2, 2, 1, -2]

@[expose] def sext3A : S24 := evalN NativeSporadic.M24 sext3Gens sext3WA

@[expose] def sext3B : S24 := evalN NativeSporadic.M24 sext3Gens sext3WB

@[expose] def Sext3Data : Prop :=
  QdNormChk sext3A ∧ QdNormChk sext3B ∧ sext3A * sext3A * sext3A = 1 ∧
    sext3B * sext3B * sext3B = 1 ∧
    ∃ x ∈ m24E1l, sext3A * sext3B * sext3A⁻¹ * sext3B⁻¹ = qdOmega * x

instance : Decidable Sext3Data := by unfold Sext3Data; infer_instance

end CFSG.EvenSporadicStandard.M24Std.DResH
