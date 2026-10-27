module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Normalizer
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporadicCarrierFinite
public import CFSG.Sporadic.Schreier.Co3Faithful
public import CFSG.Sporadic.Co3
public import Certificates.Certificate19757

public section

namespace CFSG.AGLEmbedding

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Certificates.CoreD2Perm
  CFSG.Blueprint CFSG.Open CFSG.Sporadic.Schreier.Co3

theorem co3_normalizer_gens : CoreD2.NormalizerGens ↥co3P 5 :=
  Certificates.certificate19757

theorem coreGenerationVOf_Co3 :
    CoreD2.CoreGenerationVOf (NativeSporadic.Carrier .Co3) 5 :=
  CoreD2.coreGenerationVOf_of_mulEquiv Nat.prime_five co3PermEquiv.symm
    (CoreD2.coreGenerationVOf_of_normalizerGens Nat.prime_five co3_normalizer_gens)

theorem card_sylow_Co3_five :
    ∀ T : Sylow 5 (NativeSporadic.Carrier .Co3), Nat.card T = 5 ^ 3 := by
  intro T
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcard : Nat.card (NativeSporadic.Carrier .Co3) = 495766656000 := CFSG.Sporadic.Co3.card_Co3
  have h0 : (495766656000 : ℕ) ≠ 0 := by norm_num
  have h1 := (Nat.prime_five.pow_dvd_iff_le_factorization h0).1
    (by norm_num : 5 ^ 3 ∣ 495766656000)
  have h2 : ¬ 4 ≤ (495766656000 : ℕ).factorization 5 := fun h => by
    have := (Nat.prime_five.pow_dvd_iff_le_factorization h0).2 h
    norm_num at this
  rw [Sylow.card_eq_multiplicity T, hcard, show (495766656000 : ℕ).factorization 5 = 3 by omega]

theorem glbCore_sup_Co3_five :
    ∀ S : Sylow 5 (NativeSporadic.Carrier .Co3), ∀ A : Subgroup (NativeSporadic.Carrier .Co3),
      A ≤ (S : Subgroup (NativeSporadic.Carrier .Co3)) → IsElemAbelian 5 A →
        Nat.card A = 5 ^ 2 →
        GLBCore 5 2 (S : Subgroup (NativeSporadic.Carrier .Co3)) ⊔ GLBCore 5 1 A = ⊤ :=
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  fun S A hAS hAe hA => CoreD2.glbCore_sup_of_coreGenerationVOf coreGenerationVOf_Co3
    card_sylow_Co3_five S A hAS hAe hA

end CFSG.AGLEmbedding
