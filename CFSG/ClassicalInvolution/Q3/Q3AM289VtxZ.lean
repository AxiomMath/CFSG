module

public import CFSG.ClassicalInvolution.Q3.Q3CHHyp51
public import CFSG.ClassicalInvolution.Q3.Q3T8B04

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open scoped commutatorElement MatrixGroups

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Q3.Q3T8.AF
  CFSG.ClassicalInvolution.Balance.Bootstrap

section VertexZ

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t s : G}

theorem hyp51At_z_of_three_members [IsSimpleGroup G] (hbad : BadStd8 Ω K J S R T W z t)
    {J₁ J₂ : Subgroup G} (hJ₁ : J₁ ∈ omegaNbr Ω K) (hu₁ : IsUniqueInvolution J₁ s)
    (hJ₂ : J₂ ∈ omegaNbr Ω K) (hu₂ : IsUniqueInvolution J₂ (t * s)) (hcz : z * s = s * z)
    (hct : t * s = s * t) (hind : s ∉ Subgroup.closure ({z, t} : Set G)) :
    Hyp51At (Subgroup.closure ({z, t, s} : Set G)) z := by
  have hstd := hbad.std
  have hΩu : HypOmegaModU (.sl2 3 1) Ω := hstd.stand.modU
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hstd.stand.trans hstd.noTwins hM
  have hs3 : Q3.Disc3.AscStand3 Ω K := hstd.stand.toStand3
  have hBelow := Q3T7.cit3Below_of_stand3 hs3
  have hc2 : IsPGroup 2 (Subgroup.zpowers z) :=
    ExactLayer.isPGroup_zpowers_of_sq_eq_one hstd.hz.sq
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
  have helem := T8T.isElemAbelian_closure_three hstd.hz.sq hstd.ht.sq hu₁.sq hzt hcz hct
  have hts : t ≠ s := fun e => hind (e ▸ Subgroup.subset_closure (by simp))
  have hsz : s ≠ z := fun e => hind (e ▸ Subgroup.subset_closure (by simp))
  have htsz : t * s ≠ z := fun e => by
    apply hind
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
    (Subgroup.subset_closure (by simp)) (by rw [hset]) hstd.hz.ne_one hstd.ht.ne_one hu₁.ne_one
    hts hne.symm hsz htsz (mem hstd.hJ hstd.ht) (mem hJ₁ hu₁) (mem hJ₂ hu₂)

end VertexZ

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
