module

public import Certificates.Certificate13720
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.PrimeCharGroup

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Steinberg

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem charStabilizer_eq_kernelWeylGroup_E8_five
    (χ : Multiplicative (Fin Tag.E8.rank → ℤ) →* Zp 5) :
    charStabilizer χ = kernelWeylGroup χ :=
  Certificates.certificate13720 χ

theorem rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_five
    {K : Type} [Field K] (a : Fin Tag.E8.rank → Kˣ) (h5 : ∀ i, a i ^ 5 = 1) :
    rootCharStabilizerSubgroup a = kernelReflectionGroup a :=
  rootCharStabilizerSubgroup_eq_kernelReflectionGroup_of_pChar Nat.prime_five
    (fun χ => (charStabilizer_eq_kernelWeylGroup_E8_five χ).le) a h5

end CFSG.HardMathSupport.Timmesfeld.Steinberg
