module

public import CFSG.Adapters.TauCetiExceptional.MinusculeCore
public import CFSG.Adapters.TauCetiExceptional.MinusculeClosure

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.TauCetiBridge.BigCell TauCeti

theorem e6Data_degOrdered : DegOrdered e6Data := by
  unfold DegOrdered
  decide +kernel

theorem e7Data_degOrdered : DegOrdered e7Data := by
  unfold DegOrdered
  decide +kernel

theorem e6_exists_toMat_eq
    (K : Type) [Field K] (g : Matrix.GeneralLinearGroup (Fin 27) K)
    (hg : g ∈ E6Minuscule.points K)
    (hΔ : bigCellDet ((g : Matrix (Fin 27) (Fin 27) K).submatrix e6Match.lab.symm
      e6Match.lab.symm) ≠ 0) :
    ∃ h : e6Data_valid.minGroup K, toMat e6Match.lab K h = g :=
  exists_toMat_eq e6Data_valid isFiniteType_cartan_E6 posDef_cartan_E6 e6Data_degOrdered
    e6Match.lab K g (fun P hP => e6_evalMat_eq_zero P hP K g hg) hΔ

theorem e7_exists_toMat_eq
    (K : Type) [Field K] (g : Matrix.GeneralLinearGroup (Fin 56) K)
    (hg : g ∈ E7Minuscule.points K)
    (hΔ : bigCellDet ((g : Matrix (Fin 56) (Fin 56) K).submatrix e7Match.lab.symm
      e7Match.lab.symm) ≠ 0) :
    ∃ h : e7Data_valid.minGroup K, toMat e7Match.lab K h = g :=
  exists_toMat_eq e7Data_valid isFiniteType_cartan_E7 posDef_cartan_E7 e7Data_degOrdered
    e7Match.lab K g (fun P hP => e7_evalMat_eq_zero P hP K g hg) hΔ

end CFSG.TauCetiBridge.Minuscule
