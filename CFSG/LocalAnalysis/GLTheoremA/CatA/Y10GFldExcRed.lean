module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcGap
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcChev
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcOrd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.Assembly CFSG.StandardType CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.YS09Field
open CFSG.LocalAnalysis.GLTheoremA

theorem solvable_no_perfect {X : Type} [Group X] {C Q : Subgroup X} (hC : Group.IsSolvable ↥C)
    (hQC : Q ≤ C) (hperf : ⁅Q, Q⁆ = Q) (hne : Q ≠ ⊥) : False := by
  haveI : Group.IsSolvable ↥C := hC
  have hsol : Group.IsSolvable ↥Q :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hQC)
      (Subgroup.inclusion_injective hQC)
  haveI : Group.IsSolvable ↥Q := hsol
  haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hne
  have hcomm : commutator ↥Q = ⊤ := by
    rw [← CFSG.StandardType.ggCommutator_subgroupOf Q, hperf, Subgroup.subgroupOf_self]
  have hlt : commutator ↥Q < ⊤ := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥Q
  rw [hcomm] at hlt
  exact lt_irrefl _ hlt

theorem fldExc_core_or {S : Type} [Group S] [Finite S] (hRig : GGLabelRigidInput) {p : ℕ}
    (hp : p.Prime) (hcen : Subgroup.center S = ⊥) {α : MulAut S} (hα : α ^ p = 1)
    {J : Subgroup S} {labK labJ : GLALabel}
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hJ : GLAPComponent p (fixSubgroup α) J) (hcanK : canonLabel labK = labK)
    {R : Type} [Group R] {I F : Set (MulAut R)} (θ : S ⧸ Subgroup.center S ≃* R)
    (hs : IsSimpleGroup R) (hna : ∃ a b : R, a * b ≠ b * a)
    {i f : MulAut R} (hi : i ∈ I) (hf : f ∈ F)
    (hind : LargeEvenInduces θ (fun s s' => s' = α s) (i * f))
    (hout : ¬ ∃ i ∈ I, LargeEvenInduces θ (fun s s' => s' = α s) i)
    (hconj : GGRawFieldConj p R I F)
    (hfix : ∀ f' ∈ F, orderOf f' = p → p ∣ labK.n ∧
      (Group.IsSolvable ↥(ggFixSub f') ∨ ∃ (R₀ : Type) (_ : Group R₀) (lab' : LargeEvenLabel),
        IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ LargeEvenInLambda2 lab' ∧
        canonLabel lab' = ⟨labK.tag, labK.rank, labK.n / p⟩ ∧ GGHasLabel lab' R₀ ∧
        Nonempty (ggFixDer f' ≃* R₀))) :
    (canonLabel labK).n = p * (canonLabel labJ).n ∧ (canonLabel labK).tag = (canonLabel labJ).tag ∧
      (canonLabel labK).rank = (canonLabel labJ).rank := by
  let eS : S ≃* S ⧸ Subgroup.center S :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm
  let e : S ≃* R := eS.trans θ
  have hkey : ∀ s : S, (i * f) (e s) = e (α s) := fun s => hind s (α s) rfl
  have hαe : MulAut.congr e α = i * f := by
    ext r
    have h := hkey (e.symm r)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hpow : (i * f) ^ p = 1 := by rw [← hαe, ← map_pow, hα, map_one]
  have hnot : i * f ∉ I := fun h => hout ⟨i * f, h, hind⟩
  obtain ⟨f', hf', u', hu', hord', hdec⟩ :=
    hconj hs hna i hi f (Subgroup.subset_closure hf) hnot hpow
  let e' : S ≃* R := e.trans (u'⁻¹ : MulAut R)
  have hfe : MulAut.congr e' α = f' := by
    ext r
    have h1 : (i * f) (u' r) = e (α (e.symm (u' r))) := by
      rw [← hkey (e.symm (u' r)), MulEquiv.apply_symm_apply]
    have h2 : (i * f) (u' r) = u' (f' r) := by
      rw [hdec]
      simp [MulAut.mul_apply, mul_assoc]
    have h3 : e' (α (e'.symm r)) = u'⁻¹ (e (α (e.symm (u' r)))) := by
      have hs' : e'.symm r = e.symm (u' r) := by
        rw [MulEquiv.symm_apply_eq]
        show r = u'⁻¹ (e (e.symm (u' r)))
        rw [MulEquiv.apply_symm_apply]
        simp
      rw [hs']
      rfl
    show e' (α (e'.symm r)) = f' r
    rw [h3, ← h1, h2]
    simp
  have hJ' : GLAPComponent p (fixSubgroup f') (J.map e'.toMonoidHom) := by
    rw [← hfe, ← Y10F.fixSubgroup_map_congr]
    exact (Y10F.glaPComponent_map_iff hp e'.injective).mpr hJ
  haveI : Finite R := Finite.of_equiv (S ⧸ Subgroup.center S) θ.toEquiv
  obtain ⟨hpn, hsolv | ⟨R₀, _, lab', hs0, hna0, hlam', hcan', hGH, ⟨θ₀⟩⟩⟩ := hfix f' hf' hord'
  ·
    exfalso
    have hperf : ⁅J.map e'.toMonoidHom, J.map e'.toMonoidHom⁆ = J.map e'.toMonoidHom :=
      CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ'
    have hle : J.map e'.toMonoidHom ≤ ggFixSub f' := by
      have h2 := Subgroup.map_mono (f := e'.toMonoidHom) (hJ.1 : J ≤ fixSubgroup α)
      rw [Y10F.fixSubgroup_map_congr e' α, hfe] at h2
      exact h2
    exact solvable_no_perfect hsolv hle hperf
      (CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hJ')
  haveI : IsSimpleGroup R₀ := hs0
  have hsub : fixSubgroup f' = ggFixSub f' := rfl
  have hJeq : J.map e'.toMonoidHom = ggFixDer f' := by
    rw [hsub] at hJ'
    exact pComp_eq_commutator hJ' (θ₀.isSimpleGroup)
  let eJ : ↥J ≃* R₀ :=
    ((Subgroup.equivMapOfInjective J e'.toMonoidHom e'.injective).trans
      (MulEquiv.subgroupCongr hJeq)).trans θ₀
  haveI : IsSimpleGroup ↥J := eJ.isSimpleGroup
  haveI : Group.IsPerfect ↥J :=
    Subgroup.isPerfect_iff.mpr (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ)
  obtain ⟨eQ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLinFld.nonempty_quotCenter_equiv eJ
  have hGJ : GGHasLabel lab' (↥J ⧸ Subgroup.center ↥J) := ggHasLabel_congr hGH eQ.symm
  obtain ⟨hlamJ, -, hGlabJ⟩ := Y10GInnLin.ggHasLabel_of_hasLabel hlabJ
  have hiso : GGLabelIso labJ lab' := hRig labJ lab' (↥J ⧸ Subgroup.center ↥J) hlamJ hlam' hGlabJ hGJ
  have hC : canonLabel labJ = ⟨labK.tag, labK.rank, labK.n / p⟩ := by
    rw [Y10GInnLin.canonLabel_eq_of_ggLabelIso hiso, hcan']
  rw [hcanK, hC]
  refine ⟨?_, rfl, rfl⟩
  exact (Nat.mul_div_cancel' hpn).symm

end CFSG.LocalAnalysis.GLTheoremA.Y10GField

end
