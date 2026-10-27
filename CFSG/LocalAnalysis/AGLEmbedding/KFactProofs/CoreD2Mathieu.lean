
module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2MathieuBase

public import Certificates.Certificate19751
public import Certificates.Certificate19752

public section

namespace CFSG.AGLEmbedding

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Certificates.CoreD2Perm
  CFSG.Blueprint CFSG.Open

theorem m12_core_generation :
    CoreD2.CoreGenerationOf ↥NativeSporadic.M12 3 :=
  Certificates.certificate19751

theorem glbCore_M12_three :
    ∀ S : Sylow 3 (NativeSporadic.Carrier .M12),
      GLBCore 3 2 (S : Subgroup (NativeSporadic.Carrier .M12)) = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact fun S => CoreD2.glbCore_two_eq_top_of_coreGenerationOf
    (G := NativeSporadic.Carrier .M12) m12_core_generation S

theorem coreGenerationZOf_M24 :
    CoreD2.CoreGenerationZOf (NativeSporadic.Carrier .M24) 3 :=
  Certificates.certificate19752

theorem glbCore_sup_M24_three :
    ∀ S : Sylow 3 (NativeSporadic.Carrier .M24), ∀ A : Subgroup (NativeSporadic.Carrier .M24),
      A ≤ (S : Subgroup (NativeSporadic.Carrier .M24)) → IsElemAbelian 3 A → Nat.card A = 3 ^ 2 →
        GLBCore 3 2 (S : Subgroup (NativeSporadic.Carrier .M24)) ⊔ GLBCore 3 1 A = ⊤ :=
  fun S A hAS hAe hA => CoreD2.glbCore_sup_of_coreGenerationZOf coreGenerationZOf_M24
    card_sylow_M24_three S A hAS hAe hA

end CFSG.AGLEmbedding
