module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.G6Words
public import CFSG.Sporadic.HNOddCore.OuterFix
public import CFSG.Sporadic.HNOddCore.CRec
public import Std.Data.HashSet
public import CFSG.Sporadic.HNOddCore.SixB
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.SylowReduce
public import CFSG.Sporadic.HNOddCore.SixD
public import Certificates.Certificate25550

public noncomputable section

namespace CFSG.EvenSporadicStandard.TwoHS

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore
  CFSG.Sporadic.HNOddCore.Native CFSG.ONSchreier CFSG.ONSchreier.Native
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem coe_t6C : ((t6C : C6) : JH) = aJ := rfl

section Pure

theorem t6C_central (x : C6) : x * t6C = t6C * x := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_t6C]
  exact ((Subgroup.mem_centralizer_iff.1 x.2) aJ (Set.mem_singleton aJ)).symm

end Pure

section Abstract

theorem sign_core_aux (t : C6) (htJ : (t : JH) = aJ)
    (_ht1 : phi6 t = 1) (_htc : ∀ y : C6, y * t = t * y) :
    (∀ g : C6, g ∉ Dsub.comap phi6 → g ^ 2 = t → False) ∧
      ∃ x : C6, x ∈ Dsub.comap phi6 ∧ x ^ 2 = t := by
  have ht : t = t6C := Subtype.ext htJ
  subst ht
  exact Certificates.certificate25550

theorem sign_core :
    (∀ g : C6, g ∉ Dsub.comap phi6 → g ^ 2 = t6C → False) ∧
      ∃ x : C6, x ∈ Dsub.comap phi6 ∧ x ^ 2 = t6C :=
  sign_core_aux t6C coe_t6C (MonoidHom.mem_ker.1 t6C_mem_ker) t6C_central

end Abstract

end CFSG.EvenSporadicStandard.TwoHS
