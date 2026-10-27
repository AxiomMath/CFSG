module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion
public import CFSG.Dihedral.DisconnectedInvolutionGraph.PGroupNormalizerExtension

public section

namespace CFSG.EvenSporadicStandard

open Subgroup

theorem false_of_index_two_of_controls_fusion {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {N N₀ S : Subgroup G} {z : G}
    (hz : orderOf z = 2) (hN₀ : (N₀.subgroupOf N).Normal)
    (hidx : N₀.relIndex N = 2) (hzN₀ : z ∉ N₀)
    (hSN : S ≤ N) (hS : IsPGroup 2 S)
    (hSmax : ∀ R : Subgroup G, IsPGroup 2 R → S ≤ R → R ≤ N → R = S)
    (hzS : z ∈ S) (hnorm : normalizer (S : Set G) ≤ N)
    (hfus : ∀ u ∈ N, IsConj z u → ∃ g ∈ N, g * z * g⁻¹ = u) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSmaxG : ∀ R : Subgroup G, IsPGroup 2 R → S ≤ R → R = S := by
    intro R hR hSR
    by_contra hne
    have hproper : S < R := lt_of_le_of_ne hSR (Ne.symm hne)
    obtain ⟨E, hSE, hE2, hER⟩ :=
      CFSG.DisconnectedInvolutionGraph.Helpers.pgroup_strict_normalizer_extension 2 S R hR hproper
    have hEN : E ≤ N := (hER.trans inf_le_right).trans hnorm
    exact hSE.ne' (hSmax E hE2 hSE.le hEN)
  let P : Sylow 2 G :=
    { toSubgroup := S
      isPGroup' := hS
      is_maximal' := fun {R} hR hSR => hSmaxG R hR hSR }
  have hSidx : ¬ 2 ∣ S.index := by simpa using P.not_dvd_index
  set U : Subgroup G := S ⊓ N₀ with hUdef
  have hUS : U ≤ S := inf_le_left
  have hzU : z ∉ U := fun h => hzN₀ (mem_inf.1 h).2
  have hzN : z ∈ N := hSN hzS
  have hzH : (⟨z, hzN⟩ : N) ∉ N₀.subgroupOf N := fun hx =>
    hzN₀ (Subgroup.mem_subgroupOf.1 hx)
  have hHidx : (N₀.subgroupOf N).index = 2 := by
    simpa [Subgroup.relIndex] using hidx
  have hdvd : (N₀.subgroupOf N).relIndex (S.subgroupOf N) ∣ 2 := by
    rw [← hHidx]
    exact Subgroup.relIndex_dvd_index_of_normal (H := N₀.subgroupOf N) (K := S.subgroupOf N)
  have hne : (N₀.subgroupOf N).relIndex (S.subgroupOf N) ≠ 1 := by
    intro h1
    exact hzH (Subgroup.relIndex_eq_one.1 h1 (Subgroup.mem_subgroupOf.2 hzS))
  have hrel : (N₀.subgroupOf N).relIndex (S.subgroupOf N) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact absurd h1 hne
    · exact h2
  have hU : U.relIndex S = 2 := by
    rw [hUdef, inf_comm, Subgroup.inf_relIndex_right, ← Subgroup.relIndex_subgroupOf hSN]
    exact hrel
  have hconjNotMem : ∀ n : N, n * ⟨z, hzN⟩ * n⁻¹ ∉ N₀.subgroupOf N := by
    intro n hn
    have hback := hN₀.conj_mem' (n * ⟨z, hzN⟩ * n⁻¹) hn n
    have h_eq : n⁻¹ * (n * ⟨z, hzN⟩ * n⁻¹) * n = ⟨z, hzN⟩ := by group
    exact hzH (h_eq ▸ hback)
  obtain ⟨g, hgU⟩ := exists_conj_mem_complement hnonab hS hSidx hUS hU hzS hzU hz
  have hconj : IsConj z (g⁻¹ * z * g) := isConj_iff.2 ⟨g⁻¹, by group⟩
  have hmemN : g⁻¹ * z * g ∈ N := hSN (hUS hgU)
  obtain ⟨n, hnN, hn⟩ := hfus _ hmemN hconj
  exact hconjNotMem ⟨n, hnN⟩ (by
    rw [Subgroup.mem_subgroupOf]
    change n * z * n⁻¹ ∈ N₀
    rw [hn]
    exact (mem_inf.1 hgU).2)

end CFSG.EvenSporadicStandard
