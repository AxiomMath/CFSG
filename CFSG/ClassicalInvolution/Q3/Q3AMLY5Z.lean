module

public import CFSG.ClassicalInvolution.Q3.Q3AMLY5Stmt

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap

section Vertex


theorem e3zY_proved : Q3AM.VertexZLeafY := by
  intro G _ _ _ Ω K J S R T W z t h s hs
  have hbad := h.bad
  have hstd := hbad.std
  have hΩu : HypOmegaModU (.sl2 3 1) Ω := hstd.stand.modU
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hstd.stand.trans hstd.noTwins hM
  have hs3 : Q3.Disc3.AscStand3 Ω K := hstd.stand.toStand3
  have hBelow := Q3T7.cit3Below_of_stand3 hs3
  have hc2 : IsPGroup 2 (Subgroup.zpowers z) :=
    ExactLayer.isPGroup_zpowers_of_sq_eq_one hstd.hz.sq
  obtain ⟨J₁, hJ₁, hu₁⟩ := hs.nbr₁
  obtain ⟨J₂, hJ₂, hu₂⟩ := hs.nbr₂
  have mem : ∀ {M : Subgroup G} {x : G}, M ∈ omegaNbr Ω K → IsUniqueInvolution M x →
      Q3NL.IsSectionMember3 (Subgroup.centralizer ({z} : Set G)) (Q3NL.exactCore3 z M) x := by
    intro M x hM hx
    have hMt := mem_tqMembers3_of_omegaNbr hΩ hnt hstd.hz hM hx
    exact Q3NL.isSectionMember3_exactCore3 (isClassicalMember3_of_uniqueInvolution hΩu hM.1 hx)
      hc2 hMt.2
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hstd.hz hstd.hJ hstd.ht
  have hne : z ≠ t := fun e => by
    have : IsUniqueInvolution J z := e ▸ hstd.ht
    exact hstd.hJ.2.1 (hnt K hstd.stand.mem J ⟨hstd.hJ.1, z, hstd.hz, this⟩)
  have helem := T8T.isElemAbelian_closure_three hstd.hz.sq hstd.ht.sq hs.sq hzt hs.comm_z
    hs.comm_t
  have hts : t ≠ s := fun e => hs.indep (e ▸ Subgroup.subset_closure (by simp))
  have hsz : s ≠ z := fun e => hs.indep (e ▸ Subgroup.subset_closure (by simp))
  have htsz : t * s ≠ z := fun e => by
    apply hs.indep
    have h1 : s = t * z := by
      calc s = t * (t * s) := by rw [← mul_assoc, hstd.ht.sq, one_mul]
        _ = t * z := by rw [e]
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  have hset : ({z, t, s} : Set G) = {t, s, z} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  exact Q3CH.hyp51At_of_layers' hbad.nonabelian hBelow helem
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp)) (by rw [hset]) hstd.hz.ne_one hstd.ht.ne_one hs.ne_one
    hts hne.symm hsz htsz (mem hstd.hJ hstd.ht) (mem hJ₁ hu₁) (mem hJ₂ hu₂)

end Vertex

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
