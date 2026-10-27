module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7SylowBasic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7CentX
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcJ
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Classes

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction

variable {K : Type} [Field K]

theorem e7FrameX_facts : e7FrameX ≠ [] ∧ e7FrameX.Nodup ∧
    (∀ σ ∈ e7FrameX, IsRoot .E7 σ ∧ 0 < height σ) ∧
      e7FrameX.Pairwise fun σ σ' => iform σ σ' = 0 := by
  obtain ⟨h1, h2, h3⟩ := e7Frames_facts e7FrameX (by simp)
  exact ⟨h1, h2, fun σ hσ => ⟨(isRoot_of_mem_e7Frames σ (by simp_all)).1,
    (isRoot_of_mem_e7Frames σ (by simp_all)).2.2⟩, h3⟩

theorem e7FrameElt_conj_wordX
    [CharP K 2] (d : K) :
    e7WeylRep K ((coxeterSystem .E7).wordProd e7WordX) * e7FrameElt K [highRoot .E7] d *
        (e7WeylRep K ((coxeterSystem .E7).wordProd e7WordX))⁻¹ = e7FrameElt K e7FrameX d := by
  rw [e7FrameElt_conj_word e7WordX (by simpa using isRoot_highRoot .E7), e7WordX_map]

section Certs


theorem sylowData_e7_highRoot [Finite K] [CharP K 2] :
    Exc.SylowData (e7FramePt K [highRoot .E7]) (e7FrameLine K [highRoot .E7]) := by
  intro w _ hconj ⟨k, hk⟩
  have hτ' : Tag.E7 = .D4 ∨ Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 :=
    Or.inr (Or.inr (Or.inl rfl))
  have hθ : pinnedX .E7 K (highRoot .E7) 1 ∈ rootSubgroup .E7 K (highRoot .E7) :=
    subset_closure ⟨1, rfl⟩
  have hcomm : ∀ β, IsRoot .E7 β → 0 < height β → ∀ c : K,
      (w : ModGL .E7 K) * pinnedX .E7 K β c = pinnedX .E7 K β c * (w : ModGL .E7 K) := by
    intro β hβ hpos c
    rcases eq_or_ne c 0 with rfl | hc
    · rw [pinnedX_zero, mul_one, one_mul]
    obtain ⟨b, hb⟩ := exists_conj_highRoot_eq_e7FrameElt hβ hc
    have hβU : pinnedX .E7 K β c ∈ posUnipotent .E7 K :=
      pinnedX_mem_rootSpan (S := {α | IsRoot .E7 α ∧ 0 < height α}) ⟨hβ, hpos⟩ c
    have hβθ := mem_centralizer_iff.1 (posUnipotent_le_centralizer_highRoot K hβU) _ hθ
    have hbC : b * e7FramePt K [highRoot .E7] * b⁻¹ ∈ Exc.cent (e7FramePt K [highRoot .E7]) := by
      rw [hb, Exc.cent, mem_centralizer_singleton_iff]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, coe_e7FrameElt, ← e7FrameElt_one, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact hβθ.symm
    have h1 := hconj b hbC
    rw [hb, Exc.cent, mem_centralizer_singleton_iff] at h1
    have h2 := congrArg Subtype.val h1
    simpa [coe_e7FrameElt] using h2
  have hB : (w : ModGL .E7 K) ∈ borelGroup .E7 K := by
    refine mem_borelGroup_of_normalizes_heightSeries le_rfl
      (simpleDiffTail_E7_5.mono (by norm_num)) w.2 ?_
    intro h' _ x hx
    have hle : heightSeries .E7 K h' ≤
        centralizer ({(w : ModGL .E7 K)} : Set (ModGL .E7 K)) := by
      refine iSup₂_le fun α hα => (closure_le _).2 ?_
      rintro _ ⟨c, rfl⟩
      exact mem_centralizer_singleton_iff.2 (hcomm α hα.1 hα.2.1 c).symm
    have hx' := mem_centralizer_singleton_iff.1 (hle hx)
    rw [← hx', mul_inv_cancel_right]
    exact hx
  have hk' : (w : ModGL .E7 K) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hU := mem_posUnipotent_of_mem_borelGroup_of_pow hB hk'
  have hchk := annListCheck_E7_simple
  have hspan := mem_rootSpan_of_commute_of_annListCheck hτ' hchk hU fun δ hδ =>
    hcomm δ ((annListCheck_sound hchk).1 δ hδ).1 ((annListCheck_sound hchk).1 δ hδ).2 1
  have hroot : rootSpan .E7 K {γ | γ ∈ [highRoot .E7]} ≤ rootSubgroup .E7 K (highRoot .E7) :=
    iSup₂_le fun α hα => by
      rw [Set.mem_ofPred_eq, List.mem_singleton] at hα
      rw [hα]
  obtain ⟨c, hc⟩ := CFSG.Blueprint.Chevalley.mem_rootSubgroup.1 (hroot hspan)
  have hr : ∀ σ ∈ [highRoot .E7], IsRoot .E7 σ := by simpa using isRoot_highRoot .E7
  refine (mem_e7FrameLine hr (List.pairwise_singleton _ _)).2 ⟨c, Subtype.ext ?_⟩
  simpa [coe_e7FrameElt] using hc

theorem sylowData_e7FrameX [Finite K] [CharP K 2] :
    Exc.SylowData (e7FramePt K e7FrameX) (e7FrameLine K e7FrameX) := by
  have h := (sylowData_e7_highRoot (K := K)).conj
    (e7WeylRep K ((coxeterSystem .E7).wordProd e7WordX))
  rwa [← e7FrameElt_one, e7FrameElt_conj_wordX, e7FrameElt_one,
    map_conj_e7FrameLine_of e7FrameElt_conj_wordX] at h

theorem commute_e7FrameLine_X [CharP K 2] :
    ∀ z ∈ e7FrameLine K e7FrameX, ∀ g ∈ Exc.cent (e7FramePt K e7FrameX), z * g = g * z := by
  intro z hz g hg
  have hγ := (e7FrameX_facts.2.2.1 _ (List.mem_singleton_self _)).1
  exact commute_e7FrameLine_root hγ one_ne_zero hg hz

theorem centreData_e7FrameX [Finite K] [CharP K 2] :
    Exc.CentreData (e7FramePt K e7FrameX) (e7FrameLine K e7FrameX) := by
  obtain ⟨hne, hnd, hF, ho⟩ := e7FrameX_facts
  exact centreData_e7FrameLine hne hnd hF ho commute_e7FrameLine_X sylowData_e7FrameX

theorem regular_e7FrameX [Finite K] [CharP K 2] :
    ∃ u, Exc.Regular (e7FrameLine K e7FrameX) u := by
  obtain ⟨hne, hnd, hF, ho⟩ := e7FrameX_facts
  exact regular_e7FrameLine hne hnd hF ho commute_e7FrameLine_X

end Certs

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
