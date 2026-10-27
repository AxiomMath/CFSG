module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinPrimeGlue
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinPrimeBlocks

public section

namespace CFSG.AGLEmbedding

open CFSG.LocalAnalysis.ComponentInitial LinearFlag ToralCensus


theorem fixPrimeATorus (hGA : CFSG.Open.GriessAllModelsStatement) : FixPrimeATorus := by
  intro Y _ _ L J p u h hX
  obtain ⟨r, f, hr, hf2, hpf, ⟨e⟩⟩ := exists_projectiveSL_of_isLieOfTorus hX
  have : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hZ := oddCenterLinear_of_griess hGA
  obtain ⟨ρ, hρs, -, hρ⟩ := exists_cover_of_oddCenter hZ (kFactCoverLinear_of_griess hGA)
    h.parab.comp h.parab.odd (by omega : 2 ≤ r + 1) e
  obtain ⟨σ, e', I, hσs, hσ, hI, hcomap, hne, hnb⟩ :=
    exists_comap_eq_flagStabilizer h.parab.odd (by omega) e hρs hρ h.parab.parab
  obtain ⟨-, hσk⟩ := surjective_and_ker_le_of_compat h.parab.comp.2.2.1 e' σ hσ
  have hJL : J ≤ L := h.parab.parab.1
  obtain ⟨t, ht, c, hc, hut⟩ := exists_eq_mul_of_mem_perfectJoin_sup hσs hσk hJL h.join
  have hK4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hn : r + 1 = 3 := eq_three_of_cyc_fix hI (hne h.parab.ne_top) (hnb h.parab.ne_borel)
    h.prime (by have := h.five_le; omega) hK4 (hcard ▸ hpf)
    (fun Q hQ hQp hQZ => isCyclic_of_cycPerfect_comap hσs hσk hJL h.cyc (hcomap ▸ hQ) hQp hQZ)
    (hcomap ▸ ht) (pow_mem_center_of_eq_mul hσ hc hut h.pow)
    (hcomap ▸ centralizer_le_comap_of_eq_mul hc hut h.fix)
  obtain rfl : r = 2 := by omega
  exact ⟨not_dvd_card_center_of_three hZ h.parab.comp h.parab.odd e h.five_le,
    Or.inr ⟨f, hpf, ⟨e⟩⟩⟩

theorem fixPrimeA (hGA : CFSG.Open.GriessAllModelsStatement) : FixPrimeA :=
  fixPrimeA_of_torus hGA (fixPrimeATorus hGA)

end CFSG.AGLEmbedding
