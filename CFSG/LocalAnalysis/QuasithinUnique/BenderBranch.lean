module

public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchONan
public import CFSG.LocalAnalysis.QuasithinUnique.BenderConfined

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

theorem UniqueFusionDatum.escaping_centralizers_excluded {G : Type} [Group G] [Finite G]
    (hrec : LocalComponentRecognition) (hemb : ComponentEmbeddingUnderInvolution)
    {T M U : Subgroup G} {z : G} (hd : UniqueFusionDatum T M U z) :
    ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ M := by
  by_contra hcon
  push Not at hcon
  obtain ⟨u₀, hu₀, hu₀1, hu₀M⟩ := hcon
  obtain ⟨u, L, h⟩ := BenderBranch.exists_maximalEscapingPair hd ⟨u₀, hu₀, hu₀1, hu₀M⟩
  obtain ⟨V, _, _, _, e, ρ, R, A, C, -, -, -, -, hRX, hirr, hnt, hcompl, hA, hC0, hCV, hRs, hRcyc,
    hRfree, hTI, hRnorm, hidx⟩ := hd.maximal_component_ONan_hypotheses hrec hemb h
  have hcard := ONan.onan_irreducible_intransitive_TI ρ.range R hRX hirr hnt A C hcompl hA hC0 hCV
    hRs hRcyc hRfree hTI hRnorm
  rw [hcard] at hidx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : ¬ 2 ∣ T.index := by
    simpa only [index_subgroupOf_top] using hd.setting.sylow.2.2
  let T' : Sylow 2 G := hd.setting.isPGroup.toSylow hT2
  have hfusion : ∀ x : G, x ∈ M → (∃ n : ℕ, orderOf x = 2 ^ n) →
      ∀ g : G, g⁻¹ * x * g ∈ M → ∃ m ∈ M, g⁻¹ * x * g = m⁻¹ * x * m := by
    rintro x hx ⟨n, hn⟩ g hg
    exact hd.control x hx ⟨n, by rw [← hn]; exact pow_orderOf_eq_one x⟩ g hg
  obtain ⟨N, hNn, hN2⟩ := CFSG.ShultStronglyClosedTI.element_fusion_index_two_transfer T' M
    hd.setting.le hfusion _ inf_le_left hidx
  have hsimple := hd.setting.simple
  have : N.Normal := hNn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · rw [hbot, Subgroup.index_bot] at hN2
    have : IsMulCommutative G := (isCyclic_of_prime_card hN2).isMulCommutative
    obtain ⟨a, b, hab⟩ := hd.setting.nonabelian
    exact hab (mul_comm a b)
  · rw [htop, Subgroup.index_top] at hN2
    omega

theorem benderBranch_of_interfaces
    (hrec : LocalComponentRecognition)
    (hemb : ComponentEmbeddingUnderInvolution) : BenderBranch := by
  intro G _ _ T M h hδ
  obtain ⟨U, z, hd⟩ := exists_uniqueFusionDatum h hδ
  exact hd.fusionIsBenderGroup_of_centralizer_le (hd.escaping_centralizers_excluded hrec hemb)

end CFSG.QuasithinUnique
