module

public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4Defs
public import CFSG.LocalAnalysis.AGLEmbedding.G28InSituAux
public import CFSG.LocalAnalysis.AGLEmbedding.A9MSideOneAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Aux2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_blockCentralizer' {M L : Subgroup G} {t : G} (htM : t ∈ M)
    (hLbar : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩ ∈
      Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    t ∈ Subgroup.normalizer (blockCentralizer M L : Set G) := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Cb := Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCb
  have hNC : Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      Subgroup.normalizer (Cb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  have htN : mk ⟨t, htM⟩ ∈ Subgroup.normalizer (Cb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := hNC hLbar
  have key : ∀ (g : M), mk g ∈ Subgroup.normalizer (Cb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      ∀ c ∈ blockCentralizer M L, (g : G) * c * (g : G)⁻¹ ∈ blockCentralizer M L := by
    rintro g hg _ ⟨m, hm, rfl⟩
    refine ⟨g * m * g⁻¹, ?_, by simp⟩
    show mk (g * m * g⁻¹) ∈ Cb
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp hm
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key ⟨t, htM⟩ htN c, fun hc => ?_⟩
  have h1 := key (⟨t, htM⟩)⁻¹ (by rw [map_inv]; exact Subgroup.inv_mem _ htN) _ hc
  simpa [mul_assoc] using h1

theorem D1ReeF4Data.coprime_of_perfect {P : Sylow 5 G} {M H R X : Subgroup G}
    (h : D1ReeF4Data P M H R X) {W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hW : W ≤ barM M (H ⊓ M)) (hWW : ⁅W, W⁆ = W) : Nat.Coprime 5 (Nat.card W) := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Q₀ := (H ⊓ M).subgroupOf M ⊓ W.comap mk with hQ₀
  have hQmap : Q₀.map mk = W := by
    apply le_antisymm
    · exact (Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le _ _)
    · intro w hw
      obtain ⟨k, hk, rfl⟩ := hW hw
      exact ⟨k, ⟨hk, hw⟩, rfl⟩
  obtain ⟨P', hP'Q, hP'P, hP'map⟩ := exists_perfect_le_map_eq' mk hQmap hWW
  have hP'K : P'.map M.subtype ≤ H ⊓ M := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hP'Q hx).1
  have hP'N := h.perfect_le _ hP'K (by rw [← Subgroup.map_commutator, hP'P])
  have hWN : W ≤ barM M (GLBPrimeCore 5 H) := by
    rw [← hP'map]
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hP'N ⟨x, hx, rfl⟩))
  exact Nat.Coprime.coprime_dvd_right ((Subgroup.card_dvd_of_le hWN).trans
    (card_barM_dvd h.surv.ph3.primeCore_le)) (glbPrimeCore_coprime 5 H)

end Aux2

end CFSG.AGLEmbedding
