module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbAltLambda
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVAltBlockCore

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace D1IbAltConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem zbar_mem_block (hc : D1IbAltConfig p P M H R Rbar K z) (hB : D1IbAltInputs)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∈ barM M L :=
  hc.data.zbar_mem_block_of hc.elt hc.phase hc.cz_le
    (fun hΛp hΛC hΛn => hc.le_zpowers_zbar hB.hΓ hΛp hΛC hΛn) hL (hc.zbar_mem_sup hB hL)
    hc.orderOf_zbar (hc.zbar_not_mem_centralizer hL)

theorem uniq (hc : D1IbAltConfig p P M H R Rbar K z) (hB : D1IbAltInputs) {L₁ L₂ : Subgroup G}
    (hL₁ : IsWeakSBlock M (pCoreOf 2 H) L₁) (hL₂ : IsWeakSBlock M (pCoreOf 2 H) L₂) :
    barM M L₁ = barM M L₂ := by
  by_contra hne
  exact hc.zbar_not_mem_centralizer hL₂
    (le_centralizer_of_component_ne hL₁.component hL₂.component hne (hc.zbar_mem_block hB hL₁))

theorem mem_normalizer_of_mem (hc : D1IbAltConfig p P M H R Rbar K z) (hB : D1IbAltInputs)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {n : G} (hnH : n ∈ H) (hnM : n ∈ M) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨n, hnM⟩ ∈
      Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hnS : n ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
    rw [hc.phase.normalizer_twoCore_H]
    exact hnH
  have heq := hc.uniq hB (hL.map_conj hnM hnS) hL
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨m, hm, rfl⟩ := hx
  rw [← heq]
  have hmem : ⟨n, hnM⟩ * m * ⟨n, hnM⟩⁻¹ ∈
      (L.map (MulAut.conj n).toMonoidHom).subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr ⟨(m : G), Subgroup.mem_subgroupOf.mp hm,
      by simp [MulAut.conj_apply]⟩
  exact ⟨_, hmem, by simp only [map_mul, map_inv]⟩

theorem mem_normalizer_of_commute (hc : D1IbAltConfig p P M H R Rbar K z) (hB : D1IbAltInputs)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {y : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hy : y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ * y) :
    y ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hp := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  have hzMp : IsPGroup p (Subgroup.zpowers (⟨z, hc.mem_M⟩ : ↥M)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one, ← Subgroup.orderOf_coe]
    exact hc.elt.2.1
  obtain ⟨g, hg, hgy⟩ := exists_mem_centralizer_mk_eq hp (CFSG.pCore 2 ↥M) hc.coprime_twoCore
    hzMp (Subgroup.mem_centralizer_singleton_iff.mpr hy)
  have hgz : (g : G) ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg))
  rw [← hgy]
  exact hc.mem_normalizer_of_mem hB hL (hc.cz_le hgz) g.2


end D1IbAltConfig

end CFSG.AGLEmbedding
