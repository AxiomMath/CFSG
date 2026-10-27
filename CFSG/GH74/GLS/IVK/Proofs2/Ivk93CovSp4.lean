module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovArith
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OneComp
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Classify

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open scoped MatrixGroups

theorem ivk93cov_psp_four {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    {x : StatedProj (StatedSp 2 F)} {n : ℕ} {B : Subgroup (StatedProj (StatedSp 2 F))}
    (h : Ivk93Cov x n B) : False := by
  classical
  have h2 := CatFactsSp4.two_ne_zero_of_odd_card hodd
  obtain ⟨g, hg⟩ := CatFactsSp4.exists_conj_of_orderOf_eq_two hodd h.ord
  set φ : StatedProj (StatedSp 2 F) ≃* StatedProj (StatedSp 2 F) := MulAut.conj g⁻¹ with hφ
  have hφx : φ x = g⁻¹ * x * g := by simp [hφ]
  have h' := h.of_equiv φ
  rw [hφx] at h'
  have eK : ↥B ≃* ↥(B.map φ.toMonoidHom) := B.equivMapOfInjective _ φ.injective
  rcases hg with hg | hg
  · rw [hg] at h'
    obtain ⟨hcases, h5⟩ := CatFactsSp4.pComponent_centralizer_u1 hodd h'.le h'.comp.2
    rcases hcases with h'' | h''
    · exact h.false_of_equiv_sl2 hodd h5
        ((CatFactsSp4.E1Equiv h2).trans ((MulEquiv.subgroupCongr h''.symm).trans eK.symm))
    · exact h.false_of_equiv_sl2 hodd h5
        ((CatFactsSp4.E2Equiv h2).trans ((MulEquiv.subgroupCongr h''.symm).trans eK.symm))
  · rw [hg] at h'
    obtain ⟨hL, h5⟩ := CatFactsSp4.pComponent_centralizer_u2 hodd h'.le h'.comp.2
    have hsimple : IsSimpleGroup ↥B :=
      ((eK.trans (MulEquiv.subgroupCongr hL)).isSimpleGroup_congr).2
        (CatFactsSp4.isSimpleGroup_Lsub (by omega))
    exact h.false_of_isSimpleGroup hsimple

theorem ivk93cov_sp4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk93CovEmpty (fun X _ => LieModel X .PSp 2 p f) := by
  intro p f hp hp2 hf
  refine ivk93cov_empty_of_cfg fun J _ _ hJ x _ n B hc => ?_
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hJ
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hp.odd_of_ne_two hp2).pow
  exact ivk93cov_psp_four hodd (hc.of_equiv e)

end CFSG.GH74.GLS.IVK.Proofs2
