module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ICitedHyp111K
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def PGroupLemmaFiveOneFive (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (M : Subgroup G) (V : Sylow p G), (V : Subgroup G) ≤ M →
    3 ≤ Open.pRank p (V : Subgroup G) → GLBWeakCore p (V : Subgroup G) ≤ M →
    (∀ E : Subgroup G, E ≤ M → IsElemAbelian p E → Nat.card E = p ^ 2 →
      3 ≤ Open.pRank p (Subgroup.centralizer (E : Set G) ⊓ M)) →
    rankThreeGamma 2 p (V : Subgroup G) ≤ M

theorem exists_mem_eq_map_conj_of_sylow_le {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (P V : Sylow p G) (hP : (P : Subgroup G) ≤ M) (hV : (V : Subgroup G) ≤ M) :
    ∃ m ∈ M, (V : Subgroup G) = (P : Subgroup G).map (MulAut.conj m).toMonoidHom := by
  let P' : Sylow p M := P.subtype hP
  obtain ⟨g, hg⟩ := exists_conj_of_sylow (T₀ := (P' : Subgroup M)) P'.isPGroup'
    P'.not_dvd_index (V.subtype hV)
  refine ⟨g, g.2, ?_⟩
  ext x
  constructor
  · intro hx
    have h1 := (hg ⟨x, hV hx⟩).1 (by
      rw [Sylow.coe_subtype]; exact Subgroup.mem_subgroupOf.mpr hx)
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at h1
    refine ⟨(g : G)⁻¹ * x * g, ?_, ?_⟩
    · simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at h1
      exact h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨y, hy, rfl⟩
    have hyM : (g : G) * y * (g : G)⁻¹ ∈ M := M.mul_mem (M.mul_mem g.2 (hP hy)) (M.inv_mem g.2)
    have h1 := (hg ⟨(g : G) * y * (g : G)⁻¹, hyM⟩).2 (by
      rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      convert hy using 1
      group
      rfl)
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at h1
    simpa [MulAut.conj_apply] using h1

theorem agl81ElevenNineGammaFive_of (h : PGroupLemmaFiveOneFive G) :
    AGL81ElevenNineGammaFive G := by
  intro _hS P M H Q K L W a₀ hd h25 V hVM
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨H₁, R₁, hesc⟩ := hd.data.escape
  obtain ⟨m, hm, hVeq⟩ := exists_mem_eq_map_conj_of_sylow_le P V hesc.sylow_le hVM
  have hW : GLBWeakCore 5 (V : Subgroup G) ≤ M := by
    rw [hVeq]; exact weakCore_conj_le (by norm_num) hesc.weakCore_le hm
  have h3 : 3 ≤ Open.pRank 5 (V : Subgroup G) := by
    rw [← sylow_pRank_eq 5 (by norm_num) P V]
    exact hesc.three_le_pRank.trans (CFSG.SectionRank.pRank_mono (by norm_num) hesc.le_P)
  exact h 5 (by norm_num) (by norm_num) M V hVM h3 hW h25

end CFSG.LocalAnalysis.RankThreeTheoremC
