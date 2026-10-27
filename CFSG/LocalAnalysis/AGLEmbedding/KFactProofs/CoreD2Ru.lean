module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Lines
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporadicCarrierFinite
public import CFSG.Sporadic.Schreier.RuIso
public import Certificates.Certificate19754
public import Certificates.Certificate19755

public section

namespace CFSG.AGLEmbedding

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Certificates.CoreD2Perm
  CFSG.Blueprint CFSG.Open CFSG.Sporadic.RuSchreier

theorem ru_five_core_generation :
    CoreD2.CoreGenerationOf ↥ruP 5 :=
  Certificates.certificate19754

theorem coreGenerationOf_Ru_five :
    CoreD2.CoreGenerationOf (NativeSporadic.Carrier .Ru) 5 :=
  CoreD2.coreGenerationOf_of_mulEquiv Nat.prime_five ruEquivP.symm ru_five_core_generation

theorem glbCore_Ru_five :
    ∀ S : Sylow 5 (NativeSporadic.Carrier .Ru),
      GLBCore 5 2 (S : Subgroup (NativeSporadic.Carrier .Ru)) = ⊤ :=
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  fun S => CoreD2.glbCore_two_eq_top_of_coreGenerationOf coreGenerationOf_Ru_five S

theorem ru_three_core_generation :
    CoreD2.CoreGenerationVOf ↥ruP 3 :=
  Certificates.certificate19755

theorem coreGenerationVOf_Ru_three :
    CoreD2.CoreGenerationVOf (NativeSporadic.Carrier .Ru) 3 :=
  CoreD2.coreGenerationVOf_of_mulEquiv Nat.prime_three ruEquivP.symm ru_three_core_generation

theorem card_sylow_Ru_three :
    ∀ T : Sylow 3 (NativeSporadic.Carrier .Ru), Nat.card T = 3 ^ 3 := by
  intro T
  have hcard : Nat.card (NativeSporadic.Carrier .Ru) = 145926144000 := CFSG.Sporadic.Ru.card_Ru
  have h0 : (145926144000 : ℕ) ≠ 0 := by norm_num
  have h1 := (Nat.prime_three.pow_dvd_iff_le_factorization h0).1
    (by norm_num : 3 ^ 3 ∣ 145926144000)
  have h2 : ¬ 4 ≤ (145926144000 : ℕ).factorization 3 := fun h => by
    have := (Nat.prime_three.pow_dvd_iff_le_factorization h0).2 h
    norm_num at this
  rw [Sylow.card_eq_multiplicity T, hcard, show (145926144000 : ℕ).factorization 3 = 3 by omega]

theorem glbCore_sup_Ru_three :
    ∀ S : Sylow 3 (NativeSporadic.Carrier .Ru), ∀ A : Subgroup (NativeSporadic.Carrier .Ru),
      A ≤ (S : Subgroup (NativeSporadic.Carrier .Ru)) → IsElemAbelian 3 A →
        Nat.card A = 3 ^ 2 →
        GLBCore 3 2 (S : Subgroup (NativeSporadic.Carrier .Ru)) ⊔ GLBCore 3 1 A = ⊤ :=
  fun S A hAS hAe hA => CoreD2.glbCore_sup_of_coreGenerationVOf coreGenerationVOf_Ru_three
    card_sylow_Ru_three S A hAS hAe hA

end CFSG.AGLEmbedding
