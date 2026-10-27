module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11P34Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Model
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools
import CFSG.Sporadic.Bridge.M11

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup M11Model

theorem m11SylowTransitive_proved :
    KFactM11SylowTransitive := by
  intro K _ _ hK S a b ha hb ha1 hb1
  obtain ⟨e⟩ := hK
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_map_eq_sylow (e.trans eC.symm)
    (IsPGroup.of_card sylowR_card) sylowR_index S
  rw [hΦ] at ha hb
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
  obtain ⟨n, hn, hnab⟩ := sylowR_transitive a' ha' (fun h => ha1 (by rw [h, map_one]))
    b' hb' (fun h => hb1 (by rw [h, map_one]))
  refine ⟨Φ n, ?_, ?_⟩
  · rw [hΦ, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map_of_mem Φ.toMonoidHom hn
  · change Φ n * Φ a' * (Φ n)⁻¹ = Φ b'
    rw [← map_inv, ← map_mul, ← map_mul, hnab]

end CFSG.LocalAnalysis.RankThreeTheoremC
