module

public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.UniqueMax
import CFSG.LocalAnalysis.WeakClosure81.FiveSixPart
import CFSG.Quasithin.Background.SmithC27Setup

public section

namespace CFSG.GroupTheory.GomiThm45Counterexample

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {Ω : Type} [Group Ω] [Finite Ω] {c : GNPairChoice Ω} {G S : Subgroup Ω}

private theorem normalizer_inf_lt_g45lc (h : GomiThm45Counterexample c G S) :
    G ⊓ Subgroup.normalizer (S : Set Ω) < G := by
  refine lt_of_le_of_ne inf_le_left ?_
  intro hNG
  have hnorm : G ≤ Subgroup.normalizer (S : Set Ω) := by
    rw [← hNG]
    exact inf_le_right
  have hSle : S ≤ pCoreOf 2 G :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 h.isSylowTwoOf.1 hnorm
      h.isSylowTwoOf.2.1
  exact h.not_thompsonJ_le_centralizer
    ((CFSG.Quasithin.B6.thompsonJ_le S).trans
      (hSle.trans (CFSG.Quasithin.SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf G)))

theorem exists_sup_map_conj_eq (h : GomiThm45Counterexample c G S)
    {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb) (hg : IsGomiStepG Lb) :
    ∃ g ∈ G, S ⊔ S.map (MulAut.conj g).toMonoidHom = G := by
  obtain ⟨M, hM⟩ := exists_isUniqueMaxOver h hL hg
  obtain ⟨hMmax, hSM, -⟩ := isUniqueMaxOver_iff.mp hM
  have hNM : G ⊓ Subgroup.normalizer (S : Set Ω) ≤ M :=
    CFSG.LocalAnalysis.WeakClosure81.le_of_lt_of_maxOver_eq_singleton hM
      (le_inf h.isSylowTwoOf.1 Subgroup.le_normalizer) (normalizer_inf_lt_g45lc h)
  obtain ⟨g, hgG, hgM⟩ := SetLike.exists_of_lt hMmax.1
  refine ⟨g, hgG, ?_⟩
  let T : Subgroup Ω := S.map (MulAut.conj g).toMonoidHom
  change S ⊔ T = G
  by_contra hHne
  have hconjG : CFSG.Quasithin.B6.conjSub g G = G :=
    CFSG.Quasithin.B6.conjSub_eq_self (Subgroup.le_normalizer hgG)
  have hTG : IsSylowTwoOf T G := by
    have h := CFSG.Quasithin.B6.isSylowTwoOf_conjSub h.isSylowTwoOf g
    rw [hconjG] at h
    simpa [T, CFSG.Quasithin.B6.conjSub] using h
  have hHG : S ⊔ T ≤ G := sup_le h.isSylowTwoOf.1 hTG.1
  have hHlt : S ⊔ T < G := lt_of_le_of_ne hHG hHne
  have hHM : S ⊔ T ≤ M :=
    CFSG.LocalAnalysis.WeakClosure81.le_of_lt_of_maxOver_eq_singleton hM le_sup_left hHlt
  have hTM : T ≤ M := le_sup_right.trans hHM
  have hSsylM : IsSylowTwoOf S M :=
    CFSG.Quasithin.B6.isSylowTwoOf_mono h.isSylowTwoOf hSM hMmax.1.le
  have hTsylM : IsSylowTwoOf T M :=
    CFSG.Quasithin.B6.isSylowTwoOf_mono hTG hTM hMmax.1.le
  obtain ⟨x, hxM, hx⟩ := CFSG.Quasithin.B6.isSylowTwoOf_exists_conj hSsylM hTsylM
  have hgx : CFSG.Quasithin.B6.conjSub g S = CFSG.Quasithin.B6.conjSub x S := by
    simpa [T, CFSG.Quasithin.B6.conjSub] using hx
  have hconj : CFSG.Quasithin.B6.conjSub (x⁻¹ * g) S = S := by
    rw [CFSG.Quasithin.B6.conjSub_mul, hgx, ← CFSG.Quasithin.B6.conjSub_mul,
      inv_mul_cancel, CFSG.Quasithin.B6.conjSub_one]
  have hmem : x⁻¹ * g ∈ G ⊓ Subgroup.normalizer (S : Set Ω) := by
    refine ⟨G.mul_mem (G.inv_mem (hMmax.1.le hxM)) hgG, ?_⟩
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by
      simpa [CFSG.Quasithin.B6.conjSub] using hconj)
  have hgM' : g ∈ M := by
    have hg_eq : g = x * (x⁻¹ * g) := by group
    rw [hg_eq]
    exact M.mul_mem hxM (hNM hmem)
  exact hgM hgM'

end CFSG.GroupTheory.GomiThm45Counterexample
