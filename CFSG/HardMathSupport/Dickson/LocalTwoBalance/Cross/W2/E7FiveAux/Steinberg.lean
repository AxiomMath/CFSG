module

public import Certificates.Certificate13723
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.PrimeCharGroup

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg

theorem charStabilizer_eq_kernelWeylGroup_E7_five
    (χ : Multiplicative (Fin Tag.E7.rank → ℤ) →* Zp 5) :
    charStabilizer χ = kernelWeylGroup χ :=
  Certificates.certificate13723 χ

theorem rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_five
    {K : Type} [Field K] (a : Fin Tag.E7.rank → Kˣ) (h : ∀ i, a i ^ 5 = 1) :
    rootCharStabilizerSubgroup a = kernelReflectionGroup a :=
  rootCharStabilizerSubgroup_eq_kernelReflectionGroup_of_pChar Nat.prime_five
    (fun χ => (charStabilizer_eq_kernelWeylGroup_E7_five χ).le) a h

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
