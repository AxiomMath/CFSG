module

public import CFSG.LieType.BorelExponent.Defs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrR2PlusSyl

public section

namespace CFSG.LieType.BorelExponent

open CFSG.Open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.AGLEmbedding.ParabAutIrr (plusDiag mem_plusDerivedUnipotent_of_diag)

theorem pow_card_sub_one_mem_plusProjectiveUnipotent {n : ℕ} {K : Type} [Field K] [Finite K]
    (hn : 3 ≤ n) {b : StatedProj (StatedOmega (StatedQuadPlus n K))}
    (hb : b ∈ plusProjectiveBorel n K) : b ^ (Nat.card K - 1) ∈ plusProjectiveUnipotent n K := by
  rw [← plusDerivedBorel_project n K] at hb
  obtain ⟨g, hg, rfl⟩ := hb
  have hd : plusDiag n hn ((⟨g, hg⟩ : plusDerivedBorel n K) ^ (Nat.card K - 1)) = 1 := by
    rw [map_pow]
    exact units_pi_pow_card_sub_one _
  exact ⟨_, mem_plusDerivedUnipotent_of_diag n hn hd, by simp [map_pow]⟩

theorem borelExponentAt_POmegaPlus : BorelExponentAt .POmegaPlus := by
  intro X _ _ m f hadm hLie
  have hm4 : 4 ≤ m := by simpa only [StatedLieAdmissible] using hadm.2.2
  obtain ⟨-, K, hK, hfin, hcard, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel hLie (by decide)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  obtain ⟨P, hP⟩ := plusProjectiveUnipotent_isSylow (n := m) (K := K) 2 (by omega)
  refine HasBorelExponent.of_mulEquiv e.symm (hasBorelExponent_of_sylow P ?_)
  intro x hx
  rw [hP, plusProjectiveUnipotent_normalizer m K (by omega)] at hx
  rw [hP]
  have h := pow_card_sub_one_mem_plusProjectiveUnipotent (by omega) hx
  rwa [hcard] at h

end CFSG.LieType.BorelExponent

end
