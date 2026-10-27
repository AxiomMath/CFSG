module

public import Certificates.Certificate9704
public import Certificates.Certificate9706
public import Certificates.Certificate9707
public import CFSG.LieType.SeitzGeneration.HeisSmallSound

public section

namespace CFSG.LieType.SeitzGeneration.HeisSmall

open CFSG.LocalAnalysis.ComponentInitial

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem isPrimitiveRoot_omega {F : Type} [Field F] [NoCubeRoot F] :
    IsPrimitiveRoot (QExt.omega : QExt F) 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := orderOf_eq_prime (QExt.omega_pow_three (F := F)) QExt.omega_ne_one
  rw [← h]
  exact IsPrimitiveRoot.orderOf _

theorem heisB12_le_heisClosure_q5 (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) (hq : ℓ ^ f = 5) {ω : K} (hω : IsPrimitiveRoot ω 3) :
    heisB12 ℓ f K ≤ heisClosure ℓ f K ω := by
  obtain ⟨ι, hι, hιω⟩ := exists_ringHom_omega (L := Q5) h hq3 (by rw [card_q5, hq])
    isPrimitiveRoot_omega hω
  exact heisB12_le_of_check h ι hι hιω hq Certificates.certificate9704

theorem heisB12_le_heisClosure_q8 (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) (hq : ℓ ^ f = 8) {ω : K} (hω : IsPrimitiveRoot ω 3) :
    heisB12 ℓ f K ≤ heisClosure ℓ f K ω := by
  obtain ⟨ι, hι, hιω⟩ := exists_ringHom_omega (L := Q8) h hq3 (by rw [card_q8, hq])
    isPrimitiveRoot_omega hω
  exact heisB12_le_of_check h ι hι hιω hq Certificates.certificate9706

theorem heisB12_le_heisClosure_q11 (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) (hq : ℓ ^ f = 11) {ω : K} (hω : IsPrimitiveRoot ω 3) :
    heisB12 ℓ f K ≤ heisClosure ℓ f K ω := by
  obtain ⟨ι, hι, hιω⟩ := exists_ringHom_omega (L := Q11) h hq3 (by rw [card_q11, hq])
    isPrimitiveRoot_omega hω
  exact heisB12_le_of_check h ι hι hιω hq Certificates.certificate9707

end CFSG.LieType.SeitzGeneration.HeisSmall
