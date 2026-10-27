module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenThreeCfg

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem AGL81CfgData.false_of_comm_jZero (hS : Setting G) {p : ℕ} {P : Sylow p G}
    {M H Q : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hd : AGL81CfgData p P M H Q K) (hCGT : AschbacherLocalCGTBlock) (hD2 : NoXBlockFor G)
    (h1033 : AGL81TenThreeThreeCfg G) (hXM : d1PlusCore p H K ≤ M) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hLn : (L.subgroupOf M).Normal) {R : Subgroup G}
    (hR : IsMaxInvariantTwoIn Q R (d1PlusCore p H K)) (hR1 : R ≠ ⊥)
    (hQJ : ∀ b ∈ Q, ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L)) : False := by
  have hev := hd.two_dvd_relIndex_jZero_of_step hS hCGT hD2 h1033 hXM hL hLn hR hR1
    fun _ _ hn => hn hQJ
  obtain ⟨-, hRmax⟩ := hd.star R hR hR1
  have hMn : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.le).mp hLn
  have hNHL : ∀ B : Subgroup G, B ≤ H → B ≤ M →
      B ≤ Subgroup.normalizer ((H ⊓ L : Subgroup G) : Set G) := fun B hBH hBM b hb => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hBH hb)) y
    have h2 := Subgroup.mem_normalizer_iff.mp (hMn (hBM hb)) y
    exact ⟨fun hy => ⟨h1.mp hy.1, h2.mp hy.2⟩, fun hy => ⟨h1.mpr hy.1, h2.mpr hy.2⟩⟩
  have hRH : R ≤ H := hR.1.trans (Subgroup.map_subtype_le _)
  have hRM : R ≤ M := hR.1.trans hXM
  have hRJ : R ≤ Subgroup.normalizer (jZero H L : Set G) :=
    (hNHL R hRH hRM).trans (le_normalizer_jZero H L)
  have hQJ₀ : Q ≤ Subgroup.normalizer (jZero H L : Set G) :=
    (hNHL Q hd.le_H hd.base.1).trans (le_normalizer_jZero H L)
  have hJO := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (jZero H L)
  have hOR : pCoreOf 2 (jZero H L) ≤ R :=
    TwoRest3A6.le_of_isMaxInvariantTwo hRmax (pCoreOf_isPGroup 2 _) (hRJ.trans hJO)
      (hQJ₀.trans hJO)
  exact TwoRest3A6.not_two_dvd_index_inf_of_isMaxInvariantTwo hRmax hOR hRJ hQJ hev

theorem AGL81CfgData.false_of_comm_jZero_of_b3 (hS : Setting G) {p : ℕ} {P : Sylow p G}
    {M H Q : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hd : AGL81CfgData p P M H Q K) (hCGT : AschbacherLocalCGTBlock) (hD2 : NoXBlockFor G)
    (h1033 : AGL81TenThreeThreeCfg G) (hXM : d1PlusCore p H K ≤ M) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hLn : (L.subgroupOf M).Normal)
    (hQJ : ∀ b ∈ Q, ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L)) : False := by
  have hQS : Q ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hd.le_H.trans (localGroup_le_normalizer_pCoreOf 2 H)
  obtain ⟨R, hSR, hR⟩ := TwoRest3A6.exists_isMaxInvariantTwoIn_ge
    (hd.b3 _ (pCoreOf_isPGroup 2 H) (pCoreOf_le 2 H) hQS) (pCoreOf_isPGroup 2 H) hQS
  have hR1 : R ≠ ⊥ := fun h0 => pCoreOf_two_ne_bot hd.maxH.1 (le_bot_iff.mp (h0 ▸ hSR))
  exact hd.false_of_comm_jZero hS hCGT hD2 h1033 hXM hL hLn hR hR1 hQJ

end CFSG.LocalAnalysis.RankThreeTheoremC
