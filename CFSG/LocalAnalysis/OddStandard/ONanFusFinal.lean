module

public import CFSG.LocalAnalysis.OddStandard.ONanFusNW
public import CFSG.LocalAnalysis.OddStandard.ONanSylowCert
public import CFSG.LocalAnalysis.OddStandard.ONanFusModel
public import CFSG.LocalAnalysis.OddStandard.ONanFusThompson

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

theorem le_two_of_invRep_mem_V {i : Fin 7} (h : invRep v1 v2 v3 s t i ∈ alpV v1 v2 v3) :
    i.val ≤ 2 := by
  rw [← AlpEmb.φ_invE D.E, AlpEmb.alpV_eq_map D.E, Subgroup.mem_map_iff_mem D.E.inj] at h
  exact (invE_d_zero_iff i).1 h

theorem le_two_of_inClass_mem_V {i : Fin 7} {w : G} (hi : D.InClass i w)
    (hw : w ∈ alpV v1 v2 v3) : i.val ≤ 2 := by
  obtain ⟨c, hc, rfl⟩ := hi
  apply D.le_two_of_invRep_mem_V
  have h := AlpEmb.alpV_normal D.E hc hw
  have e : c * (c⁻¹ * invRep v1 v2 v3 s t i * c) * c⁻¹ = invRep v1 v2 v3 s t i := by group
  rwa [e] at h

theorem V_le_centralizer_V : alpV v1 v2 v3 ≤ centralizer (alpV v1 v2 v3 : Set G) := by
  intro x hx
  have h : x ∈ alpP v1 v2 v3 s t ⊓ centralizer (alpV v1 v2 v3 : Set G) := by
    rw [AlpEmb.centralizer_alpV D.E D.hF]
    exact hx
  exact h.2

theorem transitive_W (hAB : D.Fus 0 1) (hAC : D.Fus 0 2) {w : G} (hw : w ∈ alpW v1 v2 v3)
    (hw1 : w ≠ 1) :
    ∃ n ∈ normalizer (alpW v1 v2 v3 : Set G), n * (v1 ^ 2 * v3 ^ 2) * n⁻¹ = w := by
  have hwV : w ∈ alpV v1 v2 v3 := D.W_le_V hw
  have hw2 : w * w = 1 := (D.mem_W_iff.1 hw).2
  obtain ⟨i, hi⟩ := D.exists_inClass (D.V_le_P hwV) hw2 hw1
  have hi2 := D.le_two_of_inClass_mem_V hi hwV
  have hfus : D.Fus 0 i := by
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact Fus.refl D 0
    · exact hAB
    · exact hAC
  obtain ⟨g, hg⟩ := hfus
  obtain ⟨c, -, hc⟩ := hi
  have hconj : ∃ c' : G, c' * (v1 ^ 2 * v3 ^ 2) * c'⁻¹ = w := by
    refine ⟨(g * c)⁻¹, ?_⟩
    rw [← hc, ← hg]
    show (g * c)⁻¹ * invRep v1 v2 v3 s t 0 * (g * c)⁻¹⁻¹ =
      c⁻¹ * (g⁻¹ * invRep v1 v2 v3 s t 0 * g) * c
    group
  have hzC := D.V_le_centralizer_V (D.W_le_V (sq_mul_sq_mem_alpW v1 v2 v3))
  obtain ⟨n, hn, hnw⟩ := D.fuse_V hzC (D.V_le_centralizer_V hwV) hconj
  exact ⟨n⁻¹, D.normalizer_V_le_W (inv_mem hn), by rw [inv_inv]; exact hnw⟩

end FusCtx

noncomputable def FusCtx.ofStage
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a)
    {v1 v2 v3 s t : G} (hfr : AlpFrame v1 v2 v3 s t) (hz : orderOf (v1 ^ 2 * v3 ^ 2) = 2)
    (P : Sylow 2 G) (hP : (P : Subgroup G) = alpP v1 v2 v3 s t) : FusCtx G v1 v2 v3 s t where
  fr := hfr
  E := hfr.emb' hz alpBound_cert
  hF := f2Check_cert
  P := P
  hP := hP
  noIdx := no_normal_index_two_of_simple hna

end CFSG.OddStandard.ONanRec
