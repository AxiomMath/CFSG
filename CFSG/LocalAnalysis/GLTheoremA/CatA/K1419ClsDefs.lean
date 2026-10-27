module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1419Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FamLin FamUni FamSymp FamOrth FamExc InnDiagKind fam_cover)

@[expose] def K1419ClsAt (Fam : GLALabel → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (α : MulAut S) (J : Subgroup S) (labK : GLALabel),
    Fam labK → Subgroup.center S = ⊥ → α ^ 3 = 1 → α ≠ 1 → InnDiagKind S labK α →
      GLAPComponent 3 (fixSubgroup α) J → catalogIs (PSimple 3 J) l3u3Index →
      Subgroup.center (PQuot 3 J) = ⊥ → False

@[expose] def K1419ClsLinFact : Prop := K1419ClsAt FamLin

@[expose] def K1419ClsUniFact : Prop := K1419ClsAt FamUni

@[expose] def K1419ClsSympFact : Prop := K1419ClsAt FamSymp

@[expose] def K1419ClsOrthFact : Prop := K1419ClsAt FamOrth

@[expose] noncomputable def K1419ClsAlpha {Q : Type} [Group Q] [Finite Q] (β : MulAut Q) :
    MulAut (PQ Q ⧸ Subgroup.center (PQ Q)) :=
  CFSG.LocalAnalysis.GLTheoremA.Y10F.centerQuotAut (PQ Q) (H1419.betaBar β)

@[expose] def K1419ClsTransJFact : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (β : MulAut Q) (J : Subgroup Q), β ^ 3 = 1 →
    GLAPComponent 3 (fixSubgroup β) J → Subgroup.center (PQuot 3 J) = ⊥ →
      ∃ J' : Subgroup (PQ Q ⧸ Subgroup.center (PQ Q)),
        GLAPComponent 3 (fixSubgroup (K1419ClsAlpha β)) J' ∧ Nonempty (PQuot 3 J ≃* PQuot 3 J')

@[expose] def K1419ClsTransAutFact : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (β : MulAut Q), CFSG.Open.IsQuasisimple (PQ Q) →
    I1419Nontriv β → I1419Inn β →
      ∃ labK : GLALabel, HasLabel (PQ Q) (fun l : GLALabel => l = labK) ∧ K1419ClsAlpha β ≠ 1 ∧
        InnDiagKind (PQ Q ⧸ Subgroup.center (PQ Q)) labK (K1419ClsAlpha β)

@[expose] def K1419ClsL3U3LabelFact : Prop :=
  ∀ (X : Type) [Group X], CFSG.Open.IsQuasisimple X →
    catalogIs (X ⧸ Subgroup.center X) l3u3Index →
      ∃ n : ℕ,
        (HasLabel X (fun l : GLALabel => l = ⟨.A, 2, n⟩) ∧ (n % 6 = 2 ∨ n % 6 = 4)) ∨
        (HasLabel X (fun l : GLALabel => l = ⟨.twA, 2, n⟩) ∧ (n % 6 = 1 ∨ n % 6 = 5))

@[expose] def K1419ClsClassLabelFact : Prop :=
  ∀ (X : Type) [Group X], CFSG.Open.IsQuasisimple X →
    catalogIs (X ⧸ Subgroup.center X) I1419Classical2 →
      ∃ lab : GLALabel, HasLabel X (fun l : GLALabel => l = lab) ∧ ¬ FamExc lab

@[expose] def K1419ClsExcOutFact : Prop :=
  ∀ (X : Type) [Group X] (labK : GLALabel), CFSG.Open.IsQuasisimple X →
    HasLabel X (fun l : GLALabel => l = labK) →
      catalogIs (X ⧸ Subgroup.center X) I1419Classical2 → ¬ FamExc labK

theorem i1419ClassFact_of_families (hJ : K1419ClsTransJFact) (hA : K1419ClsTransAutFact)
    (hE : K1419ClsExcOutFact) (hL : K1419ClsLinFact) (hU : K1419ClsUniFact)
    (hSp : K1419ClsSympFact) (hO : K1419ClsOrthFact) : I1419ClassFact := by
  intro Q _ _ β J hQ hβ3 hNt hInn hJc hcat hZ hcl
  obtain ⟨J', hJ', ⟨e⟩⟩ := hJ Q β J hβ3 hJc hZ
  obtain ⟨labK, hlab, hα1, hInnD⟩ := hA Q β hQ hNt hInn
  have hα3 : K1419ClsAlpha β ^ 3 = 1 := by
    rw [K1419ClsAlpha, ← map_pow, H1419.betaBar_pow_three β hβ3, map_one]
  have f : PSimple 3 J ≃* PSimple 3 J' := QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  have hcat' : catalogIs (PSimple 3 J') l3u3Index := (catalogIs_congr f).1 hcat
  have hZ' : Subgroup.center (PQuot 3 J') = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have h2 : e.symm x ∈ Subgroup.center (PQuot 3 J) := by
      rw [← Subgroup.map_center_eq e.symm]
      exact Subgroup.mem_map_of_mem _ hx
    rw [hZ, Subgroup.mem_bot] at h2
    exact e.symm.injective (by rw [h2, map_one])
  have hS : Subgroup.center (PQ Q ⧸ Subgroup.center (PQ Q)) = ⊥ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.center_centerQuot_eq_bot hQ
  rcases fam_cover labK with h | h | h | h | h
  · exact hL _ (K1419ClsAlpha β) J' labK h hS hα3 hα1 hInnD hJ' hcat' hZ'
  · exact hU _ (K1419ClsAlpha β) J' labK h hS hα3 hα1 hInnD hJ' hcat' hZ'
  · exact hSp _ (K1419ClsAlpha β) J' labK h hS hα3 hα1 hInnD hJ' hcat' hZ'
  · exact hO _ (K1419ClsAlpha β) J' labK h hS hα3 hα1 hInnD hJ' hcat' hZ'
  · exact hE (PQ Q) labK hQ hlab hcl h

end CFSG.LocalAnalysis.GLTheoremA.K1419
