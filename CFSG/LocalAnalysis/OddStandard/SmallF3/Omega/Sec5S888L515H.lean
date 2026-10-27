module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888L515A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888L515B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Conj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem sec5_exists_hctx_of_pair (h52a : Asc82Lemma52a) (h52b : Asc82Lemma52b)
    (h56 : Asc82Lemma56) (hZ : Asc82ZExists) (hB : Asc82Sec5FactB5) (h512b : Asc82Lemma512b)
    (h512K : Asc82Lemma512K) (h512H : Asc82Lemma512H) (tab : Asc82Tab5) {d : G} {I : Subgroup G}
    (hs : Sec5Setting G d I) {z : G} (hz2 : orderOf z = 2) (hzd : z ≠ d) {K₁ K₂ : Subgroup G}
    (hp : Sec5Pair K₁ K₂ z) (hle : K₁ ⊔ K₂ ≤ I) :
    ∃ (S'' : Subgroup G) (r'' : G) (B'' A'' P₁ P₂ : Subgroup G) (h'' : G),
      Sec5HCtx G d I S'' z r'' B'' A'' P₁ P₂ h'' := by
  obtain ⟨-, hcent, -, -, S', z', r', B', A', hR⟩ :=
    sec5_setting_data h52a h52b h56 hZ hB h512b hs
  obtain ⟨-, g, hgI, hzg⟩ := sec5_pair_eq_twoRes tab h512K hs hcent hR hz2 hzd hp hle
  obtain ⟨K₁', K₂', hK⟩ := h512K G d I S' z' r' B' A' hR hcent
  obtain ⟨h', hH⟩ := h512H G d I S' z' r' B' A' K₁' K₂' hK
  have hconj := sec5HCtx_conj hH g
  have hd_comm : d * g = g * d :=
    (sec5_mem_centerIn_iff.mp (by rw [hcent]; exact Subgroup.mem_zpowers d)).2 g hgI
  have hgd : g⁻¹ * d * g = d := by
    calc g⁻¹ * d * g = g⁻¹ * (d * g) := by group
      _ = g⁻¹ * (g * d) := by rw [hd_comm]
      _ = d := by group
  have hI : CFSG.conjugate I g = I :=
    sec5b513_conjugate_eq_iff.mpr (Subgroup.le_normalizer hgI)
  rw [hgd, hI, ← hzg] at hconj
  exact ⟨CFSG.conjugate S' g, g⁻¹ * r' * g, CFSG.conjugate B' g, CFSG.conjugate A' g,
    CFSG.conjugate K₁' g, CFSG.conjugate K₂' g, g⁻¹ * h' * g, hconj⟩

end CFSG.OddStandard.SmallF3.Omega
