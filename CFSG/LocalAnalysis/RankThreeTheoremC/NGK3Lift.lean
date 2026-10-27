module

import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_of_top_le_aschCore_quotient {P : Sylow 3 G} {M H : Subgroup G}
    (hPH : (P : Subgroup G) ≤ H) (O : Subgroup H) [O.Normal] (hO : (3 : ℕ).Coprime (Nat.card O))
    (hOM : O.map H.subtype ≤ M) (hPM : (P : Subgroup G) ≤ M)
    (hM : ∀ Y : Subgroup G, Y ≤ (P : Subgroup G) → 2 ≤ CFSG.Open.pRank 3 Y →
      3 ≤ CFSG.Open.pRank 3 (Y ⊔ ((P : Subgroup G) ⊓ centralizer (Y : Set G))) →
        normalizer (Y : Set G) ≤ M)
    (Pbar : Sylow 3 (H ⧸ O))
    (hPbar : (Pbar : Subgroup (H ⧸ O)) =
      ((P : Subgroup G).subgroupOf H).map (QuotientGroup.mk' O))
    (hgen : ⊤ ≤ rankThreeAschCore 2 3 (Pbar : Subgroup (H ⧸ O))) : H ≤ M := by
  have _ := hPM
  have hWM : GLBWeakCore 3 (P : Subgroup G) ≤ M :=
    (CFSG.PreuniquenessRankFour.Helpers.weakCore_le_iff 3 _ _).mpr hM
  have hOM' : O ≤ (H ⊓ M).subgroupOf H := fun o ho =>
    Subgroup.mem_subgroupOf.mpr ⟨o.property, hOM (Subgroup.mem_map_of_mem _ ho)⟩
  have key := CFSG.AGLEmbedding.weakCore_map_le_map_inf_of_coprime Nat.prime_three P hWM
    (le_refl _) hPH O hO hOM'
  rw [← hPbar] at key
  have htop : (⊤ : Subgroup (H ⧸ O)) ≤ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' O) :=
    hgen.trans key
  intro h hh
  obtain ⟨m, hm, hmh⟩ := htop (Subgroup.mem_top (QuotientGroup.mk' O ⟨h, hh⟩))
  have hker : (⟨h, hh⟩ : H) * m⁻¹ ∈ O := by
    have h1 : (⟨h, hh⟩ : H) * m⁻¹ ∈ (QuotientGroup.mk' O).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hmh, mul_inv_cancel]
    rwa [QuotientGroup.ker_mk'] at h1
  have hom : ((⟨h, hh⟩ * m⁻¹ : H) : G) ∈ M := hOM ⟨_, hker, rfl⟩
  have hmM : (m : G) ∈ M := (Subgroup.mem_subgroupOf.mp hm).2
  have hh' : h = ((⟨h, hh⟩ * m⁻¹ : H) : G) * (m : G) := by simp
  rw [hh']
  exact M.mul_mem hom hmM

end CFSG.LocalAnalysis.RankThreeTheoremC
