module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Normalizer
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporadicCarrierFinite
public import CFSG.Sporadic.Schreier.PairJ2Faithful
public import CFSG.Sporadic.J2
public import Certificates.Certificate19756

public section

namespace CFSG.AGLEmbedding

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Certificates.CoreD2Perm
  CFSG.Blueprint CFSG.Open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative

theorem j2_normalizer_gens : CoreD2.NormalizerGens ↥j2P 3 :=
  Certificates.certificate19756

theorem coreGenerationVOf_J2 :
    CoreD2.CoreGenerationVOf (NativeSporadic.Carrier .J2) 3 :=
  CoreD2.coreGenerationVOf_of_mulEquiv Nat.prime_three j2PermEquiv.symm
    (CoreD2.coreGenerationVOf_of_normalizerGens Nat.prime_three j2_normalizer_gens)

theorem card_sylow_J2_three :
    ∀ T : Sylow 3 (NativeSporadic.Carrier .J2), Nat.card T = 3 ^ 3 := by
  intro T
  have hcard : Nat.card (NativeSporadic.Carrier .J2) = 604800 := CFSG.Sporadic.J2.card_J2
  have h0 : (604800 : ℕ) ≠ 0 := by norm_num
  have h1 := (Nat.prime_three.pow_dvd_iff_le_factorization h0).1
    (by norm_num : 3 ^ 3 ∣ 604800)
  have h2 : ¬ 4 ≤ (604800 : ℕ).factorization 3 := fun h => by
    have := (Nat.prime_three.pow_dvd_iff_le_factorization h0).2 h
    norm_num at this
  rw [Sylow.card_eq_multiplicity T, hcard, show (604800 : ℕ).factorization 3 = 3 by omega]

theorem glbCore_sup_J2_three :
    ∀ S : Sylow 3 (NativeSporadic.Carrier .J2), ∀ A : Subgroup (NativeSporadic.Carrier .J2),
      A ≤ (S : Subgroup (NativeSporadic.Carrier .J2)) → IsElemAbelian 3 A →
        Nat.card A = 3 ^ 2 →
        GLBCore 3 2 (S : Subgroup (NativeSporadic.Carrier .J2)) ⊔ GLBCore 3 1 A = ⊤ :=
  fun S A hAS hAe hA => CoreD2.glbCore_sup_of_coreGenerationVOf coreGenerationVOf_J2
    card_sylow_J2_three S A hAS hAe hA

end CFSG.AGLEmbedding
