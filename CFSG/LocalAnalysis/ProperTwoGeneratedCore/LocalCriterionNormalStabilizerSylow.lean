module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingConsequences
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.Basic

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.BenderSuzuki CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

theorem local_point_not_mem_normal_subgroup {H M : Subgroup G} [M.Normal] {z : G}
    (h : InvolutionPointLocalEmbedding H z)
    (hgen : involutionPointHull z = ⊤) (hMH : M ≤ H) : z ∉ M := by
  intro hzM
  have hclass : involutionPointClass z ⊆ M := by
    rintro t ⟨g, rfl⟩
    exact (inferInstance : M.Normal).conj_mem' z hzM g
  have htop : (⊤ : Subgroup G) ≤ M := by
    rw [← hgen]
    exact (Subgroup.closure_le _).mpr hclass
  exact h.proper (top_le_iff.mp (htop.trans hMH))

theorem local_point_class_not_mem_normal_subgroup {H M : Subgroup G} [M.Normal] {z : G}
    (h : InvolutionPointLocalEmbedding H z)
    (hgen : involutionPointHull z = ⊤) (hMH : M ≤ H)
    {t : G} (ht : t ∈ involutionPointClass z) : t ∉ M := by
  obtain ⟨g, rfl⟩ := ht
  intro htM
  apply local_point_not_mem_normal_subgroup h hgen hMH
  have hzM := (inferInstance : M.Normal).conj_mem (rightConjugateElem z g) htM g
  simpa [rightConjugateElem, mul_assoc] using hzM

variable [Finite G]

theorem local_point_outside_class_centralizing_normal_sylow
    {H M : Subgroup G} [M.Normal] {z : G}
    (h : InvolutionPointLocalEmbedding H z) (hMH : M ≤ H)
    (T : Sylow 2 G) (hzT : ∀ s ∈ (T : Subgroup G), Commute z s) :
    ∃ t : G, t ∈ involutionPointClass z ∧ t ∉ H ∧
      ∀ s ∈ (T : Subgroup G) ⊓ M, Commute t s := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 M := hallSylowSubgroupOfNormal T M
  let U : Subgroup G := (S : Subgroup M).map M.subtype
  have hU : U = (T : Subgroup G) ⊓ M := by
    dsimp only [U, S]
    rw [hallSylowSubgroupOfNormal_coe, Subgroup.comap_subtype,
      Subgroup.subgroupOf_map_subtype]
  obtain ⟨g, hg⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr h.proper)
  have hgH : g ∉ H := hg.2
  have hgNM : g ∈ Subgroup.normalizer (U : Set G) ⊔ M := by
    rw [S.normalizer_sup_eq_top]
    exact Subgroup.mem_top g
  obtain ⟨n, hn, m, hm, hnm⟩ := Subgroup.mem_sup_of_normal_right.mp hgNM
  have hnH : n ∉ H := by
    intro hnH
    exact hgH (hnm ▸ H.mul_mem hnH (hMH hm))
  refine ⟨rightConjugateElem z n, ⟨n, rfl⟩,
    fun htH => hnH ((pointClass_conjugate_mem_iff h n).mp htH), ?_⟩
  intro s hs
  have hsU : s ∈ U := hU.symm ▸ hs
  have hnsU : n * s * n⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp hn s).mp hsU
  have hcomm := hzT (n * s * n⁻¹) ((hU ▸ hnsU).1)
  have hmap := hcomm.map (MulAut.conj n⁻¹).toMonoidHom
  simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    rightConjugateElem, mul_assoc] using hmap

end CFSG.ProperTwoGeneratedCore
