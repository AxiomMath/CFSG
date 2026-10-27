module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6Cgroup
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6Good
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6Part22

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin A6Facts

theorem lemma2522 : Lemma2522 := by
  intro G _ _ T M hs N t zK h
  have hK0 : N.K0 = N.K := h.concl2520
  have hKH : N.H ≤ Subgroup.normalizer (N.K : Set G) := by
    rw [← hK0]; exact N.H_le_normalizer_K0
  have h254 := h.facts254
  have hsimple := h.facts258.simple
  obtain ⟨D⟩ := exists_a6Datum N hKH h.facts258 h.concl2521
  have hK : Nat.card N.K = 360 := by
    obtain ⟨eK⟩ := h.concl2521.nonempty_K
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hzT : N.z ∈ centerOf T := N.tuple.z_mem
  have hzS : N.z ∈ centerOf N.S :=
    ⟨N.tuple.center_le hzT,
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr N.S_le_T) hzT.2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    have hgood := D.good_of_conj h hg
    have huH := N.S_le_H hg
    have hnc : ¬ ∀ k ∈ N.K, (g⁻¹ * N.z * g) * k = k * (g⁻¹ * N.z * g) := by
      intro hall
      exact hgood.1 ((D.ker _ huH).mpr hall)
    refine ⟨commutator_zpowers_eq_of_simple hsimple (hKH huH) hnc, ?_⟩
    have hs6 : D.Φ (g⁻¹ * N.z * g) ∈ s6 := hgood.2.elim (fun h => psl29_le_s6 h) id
    exact D.exists_s6_inducesAut hKH hsimple hK huH hs6
  · exact le_antisymm h.facts2511.H_le (D.centralizer_t_le_H h)
  · apply le_antisymm
    · rintro c ⟨hcH, hcz⟩
      exact D.mem_S_of_centralizes_z hK0 hKH h254 hsimple hzS hcH
        (Subgroup.mem_centralizer_singleton_iff.mp hcz)
    · intro s hs
      exact ⟨N.S_le_H hs, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hzS.2 s hs)⟩

end CFSG.QuasithinUnique
