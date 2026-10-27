module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3Max
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.M11Three
import CFSG.Sporadic.Bridge.M11

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.MaxD2
open CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.AGLEmbeddingD2
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueSchreierAlternating Certificates.MaxD2Perm

theorem kFactM11ThreeIrr :
    KFactM11ThreeIrr := by
  intro L _ _ ⟨e⟩ S Y hYS hY3
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  let e' : L ≃* ↥NativeSporadic.M11 := e.trans eC.symm
  obtain ⟨R₀, hR₀⟩ := m11_three_localData
  have hT := torusLocal_of_localData hR₀ (by norm_num) orderOf_two_zmod_three (by norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := torusLocal_sylow e' hT (by
    rw [hT.1, card_M11, factorization_eq_of_pow_dvd Nat.prime_three (k := 2) (by norm_num)
      (by norm_num) (by norm_num)]) S
  obtain ⟨-, -, -, -, t, htN, m, lam, e2, hm, -, -, -, -, hline⟩ := h
  exact ⟨t, htN, by simpa using hline 1 one_pos (by omega) Y hYS hY3⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
