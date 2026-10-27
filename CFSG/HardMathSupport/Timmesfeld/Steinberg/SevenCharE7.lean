module

public import Certificates.Certificate13721
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.PrimeCharGroup

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Steinberg

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem charStabilizer_eq_kernelWeylGroup_E7_seven
    (χ : Multiplicative (Fin Tag.E7.rank → ℤ) →* Zp 7) :
    charStabilizer χ = kernelWeylGroup χ :=
  Certificates.certificate13721 χ

theorem rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_seven
    {K : Type} [Field K] (a : Fin Tag.E7.rank → Kˣ) (h : ∀ i, a i ^ 7 = 1) :
    rootCharStabilizerSubgroup a = kernelReflectionGroup a :=
  rootCharStabilizerSubgroup_eq_kernelReflectionGroup_of_pChar (by norm_num)
    (fun χ => (charStabilizer_eq_kernelWeylGroup_E7_seven χ).le) a h

end CFSG.HardMathSupport.Timmesfeld.Steinberg
