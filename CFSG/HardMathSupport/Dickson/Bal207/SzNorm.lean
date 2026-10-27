module

public import CFSG.HardMathSupport.Dickson.Bal207.SzParts
import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigSzCore
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSz32Local
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSz32Field

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Blueprint CFSG.RankThree.PartOne.K159.SzAbs

theorem bal207SzNorm :
    Bal207SzNorm := by
  intro G _ _ hM k hk5 hk1 S hS hkS
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨eF⟩⟩ := hM
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hF
  have hsimple : IsSimpleGroup G := by
    have := (CFSG.LieType.Ree.suzuki_simple ha hF').2.2
    exact eF.isSimpleGroup
  obtain rfl : a = 2 := by omega
  have hSz : SzSylow G := SzSylow.of_mulEquiv eF (szSylow_model hF')
  let ε : G ≃* suzukiGroup 2 CFSG.AGLEmbedding.KFactProofs.Sz32.F32 :=
    eF.trans (CFSG.AGLEmbedding.KFactProofs.Sz32Local.modelEquiv
      (CFSG.AGLEmbedding.KFactProofs.Sz32.F32.ringEquiv F hF'))
  have hC : ∀ T : Sylow 5 G, ∀ t ∈ (T : Subgroup G), t ≠ 1 → ∀ g : G, g * t = t * g →
      g ∈ (T : Subgroup G) := fun T =>
    CFSG.AGLEmbedding.KFactProofs.Sz32Local.centralizer_le_of_equiv ε T
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact CFSG.LocalAnalysis.RankFourTheoremC.SzSignalizer.eq_bot_of_normalizes hSz hsimple hC
    (orderOf_eq_prime hk5 hk1) ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).1 hS) hkS

end CFSG.HardMathSupport.Dickson.Bal207
