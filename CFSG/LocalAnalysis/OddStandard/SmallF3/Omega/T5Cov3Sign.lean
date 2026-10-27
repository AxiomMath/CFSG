module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Frame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesInvol

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem NFrame.commSp_signChange_three {c : ZMod 3} (fr : NFrame Q ι c) (J : Finset ι) :
    commSp (fr.signChange J) = Submodule.span (ZMod 3) (fr.b '' (J : Set ι)) := by
  ext v
  rw [mem_commSp_iff (fr.signChange_mul_self J), Module.Basis.mem_span_image]
  constructor
  · intro hv i hi
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hi
    by_contra hiJ
    have h1 : fr.b.repr (((fr.signChange J : OGroup Q) : V ≃ₗ[ZMod 3] V) v) i =
        fr.b.repr (-v) i := by rw [hv]
    rw [fr.repr_signChange J v i, map_neg, Finsupp.neg_apply,
      if_neg (by simpa only [Finset.mem_coe] using hiJ)] at h1
    have h2 : (2 : ZMod 3) * fr.b.repr v i = 0 := by
      rw [two_mul]
      exact eq_neg_iff_add_eq_zero.mp h1
    exact hi ((mul_eq_zero.mp h2).resolve_left (by decide))
  · intro hsupp
    apply fr.b.repr.injective
    ext i
    rw [fr.repr_signChange J v i, map_neg, Finsupp.neg_apply]
    by_cases hiJ : i ∈ J
    · simp [hiJ]
    · have h0 : fr.b.repr v i = 0 := by
        by_contra hne
        have hmem : i ∈ ↑(fr.b.repr v).support :=
          Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hne)
        exact hiJ (by simpa only [Finset.mem_coe] using hsupp hmem)
      simp [hiJ, h0]

private theorem NFrame.finrank_span_frame_three {c : ZMod 3} (fr : NFrame Q ι c)
    (J : Finset ι) :
    Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (fr.b '' (J : Set ι))) = J.card := by
  have hli : LinearIndependent (ZMod 3) (fun i : J => fr.b (i : ι)) :=
    fr.b.linearIndependent.comp _ Subtype.val_injective
  have hrange : Set.range (fun i : J => fr.b (i : ι)) = fr.b '' (J : Set ι) := by
    rw [show Set.range (fun i : J => fr.b (i : ι)) = Set.range (fr.b ∘ Subtype.val) from rfl,
      Set.range_comp, Subtype.range_coe]
  rw [← hrange, finrank_span_eq_card hli, Fintype.card_coe]

private theorem NFrame.quadSign_span_frame_three {c : (ZMod 3)ˣ} (fr : NFrame Q ι (c : ZMod 3))
    (J : Finset ι)
    (hnd : (Q.restrict (Submodule.span (ZMod 3) (fr.b '' (J : Set ι)))).Nondegenerate) :
    quadSign (Q.restrict (Submodule.span (ZMod 3) (fr.b '' (J : Set ι)))) =
      toSign c ^ J.card * (-1) ^ (J.card / 2) := by
  rcases J.eq_empty_or_nonempty with rfl | hne
  · rw [Finset.coe_empty, Set.image_empty, Submodule.span_empty]
    haveI : Subsingleton (⊥ : Submodule (ZMod 3) V) := by
      rw [Submodule.subsingleton_iff_eq_bot]
    rw [quadSign_of_subsingleton]
    simp
  · have hli : LinearIndependent (ZMod 3) (fun i : J => fr.b (i : ι)) :=
      fr.b.linearIndependent.comp _ Subtype.val_injective
    have hrange : Set.range (fun i : J => fr.b (i : ι)) = fr.b '' (J : Set ι) := by
      rw [show Set.range (fun i : J => fr.b (i : ι)) = Set.range (fr.b ∘ Subtype.val) from rfl,
        Set.range_comp, Subtype.range_coe]
    rw [← hrange]
    set N := Submodule.span (ZMod 3) (Set.range (fun i : J => fr.b (i : ι))) with hN
    let B : Module.Basis J (ZMod 3) N := Module.Basis.span hli
    have hnd' : (Q.restrict N).Nondegenerate := by
      rw [hN, hrange]
      exact hnd
    have hv : (QuadraticMap.associated (R := ZMod 3) (Q.restrict N)).IsOrthoᵢ B := by
      intro i j hij
      show QuadraticMap.associated (R := ZMod 3) (Q.restrict N) (B i) (B j) = 0
      have hi : ((B i : N) : V) = fr.b (i : ι) := Module.Basis.coe_span_apply hli i
      have hj : ((B j : N) : V) = fr.b (j : ι) := Module.Basis.coe_span_apply hli j
      have hinner : (Q.restrict N) (B i + B j) - (Q.restrict N) (B i) -
          (Q.restrict N) (B j) = 0 := by
        simp only [QuadraticMap.restrict_apply]
        rw [Submodule.coe_add, hi, hj,
          CFSG.RankThree.OrthogonalInvolutions.map_add_eq Q (fr.b (i : ι)) (fr.b (j : ι)),
          fr.orth (i : ι) (j : ι) (Subtype.val_injective.ne hij), add_zero]
        abel
      rw [QuadraticMap.associated_apply, hinner, smul_zero]
    have hw : (fun i : J => (Q.restrict N) (B i)) = fun _ : J => (c : ZMod 3) := by
      funext i
      rw [QuadraticMap.restrict_apply, Module.Basis.coe_span_apply hli i]
      exact fr.norm (i : ι)
    have hrepr : (Q.restrict N).basisRepr B =
        QuadraticMap.weightedSumSquares (ZMod 3) (fun _ : J => (c : ZMod 3)) := by
      rw [QuadraticMap.basisRepr_eq_of_iIsOrtho _ B hv, hw]
    have h1 : quadSign (Q.restrict N) =
        quadSign (QuadraticMap.weightedSumSquares (ZMod 3) (fun _ : J => (c : ZMod 3))) := by
      rw [← hrepr]
      exact quadSign_congr hnd' ⟨QuadraticMap.isometryEquivBasisRepr _ B⟩
    have hndw : (QuadraticMap.weightedSumSquares (ZMod 3)
        (fun _ : J => (c : ZMod 3))).Nondegenerate :=
      QuadraticMap.nondegenerate_weightedSumSquares (fun _ => isRegular_iff_ne_zero.mpr c.ne_zero)
    have heq : QuadraticMap.weightedSumSquares (ZMod 3) (fun _ : Fin J.card => (c : ZMod 3)) =
        TauCeti.presentedForm ⟨J.card, fun _ : Fin J.card => c⟩ := by
      rw [TauCeti.presentedForm_eq_weightedSumSquares_coe]
    have h2 : quadSign (QuadraticMap.weightedSumSquares (ZMod 3) (fun _ : J => (c : ZMod 3))) =
        quadSign (TauCeti.presentedForm ⟨J.card, fun _ : Fin J.card => c⟩) := by
      rw [← heq]
      exact quadSign_congr hndw ⟨QuadraticForm.isometryEquivWeightedSumSquaresReindex
        (w := fun _ : J => (c : ZMod 3)) (e := (Finset.equivFin J).symm)⟩
    rw [h1, h2, quadSign_eq_signOf _ (TauCeti.nondegenerate_presentedForm _),
      TauCeti.formClass_presentedForm, signOf_mk_diag]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem toSign_neg_one_three : toSign (-1 : (ZMod 3)ˣ) = -1 := by
  simp [toSign, show (-1 : (ZMod 3)ˣ) ≠ 1 by decide]

theorem exists_nframe_six_unit (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hs : quadSign Q = -1) (c : (ZMod 3)ˣ) : Nonempty (NFrame Q (Fin 6) (c : ZMod 3)) := by
  let Q₀ : QuadraticForm (ZMod 3) (Fin 6 → ZMod 3) :=
    QuadraticMap.weightedSumSquares (ZMod 3) fun _ : Fin 6 => (c : ZMod 3)
  have hQ₀ : Q₀.Nondegenerate := by
    refine QuadraticMap.nondegenerate_weightedSumSquares fun _ => ?_
    rw [isRegular_iff_ne_zero]
    exact c.ne_zero
  have hdim₀ : Module.finrank (ZMod 3) (Fin 6 → ZMod 3) = 6 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hbasis : ∀ i : Fin 6, Q₀ (Pi.single i 1) = (c : ZMod 3) := by
    intro i
    change QuadraticMap.weightedSumSquares (ZMod 3) (fun _ : Fin 6 => (c : ZMod 3))
      (Pi.single i 1) = (c : ZMod 3)
    rw [QuadraticMap.weightedSumSquares_apply]
    rw [Finset.sum_eq_single i
      (fun j _ hji => by rw [Pi.single_eq_of_ne hji, mul_zero, smul_zero])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    rw [Pi.single_eq_same, mul_one, smul_eq_mul, mul_one]
  have hpolar : ∀ i j : Fin 6, i ≠ j →
      QuadraticMap.polar Q₀ (Pi.single i 1) (Pi.single j 1) = 0 := by
    intro i j hij
    rw [← QuadraticMap.polarBilin_apply_apply]
    have h2 : (2 : ZMod 3) • QuadraticMap.associated (R := ZMod 3) Q₀
        (Pi.single i 1) (Pi.single j 1) =
        QuadraticMap.polarBilin Q₀ (Pi.single i 1) (Pi.single j 1) := by
      have h := DFunLike.congr_fun (DFunLike.congr_fun
        (QuadraticMap.two_nsmul_associated (S := ZMod 3) Q₀)
        (Pi.single i 1)) (Pi.single j 1)
      simp only [LinearMap.smul_apply, Pi.smul_apply, nsmul_eq_mul] at h
      have hcast : (↑(2 : ℕ) : ZMod 3) = 2 := by norm_num
      rw [hcast] at h
      simpa only [smul_eq_mul] using h
    rw [← h2]
    change (2 : ZMod 3) • QuadraticMap.associated (R := ZMod 3)
      (QuadraticMap.weightedSumSquares (ZMod 3) (fun _ : Fin 6 => (c : ZMod 3)))
      (Pi.single i 1) (Pi.single j 1) = 0
    rw [QuadraticMap.associated_weightedSumSquares]
    have hsum : (∑ m : Fin 6, (c : ZMod 3) *
        ((Pi.single i (1 : ZMod 3) : Fin 6 → ZMod 3) m *
          (Pi.single j (1 : ZMod 3) : Fin 6 → ZMod 3) m)) = 0 := by
      apply Finset.sum_eq_zero
      intro m _
      by_cases hmi : m = i
      · subst hmi
        rw [Pi.single_eq_same, Pi.single_eq_of_ne hij, mul_zero, mul_zero]
      · rw [Pi.single_eq_of_ne hmi, zero_mul, mul_zero]
    rw [hsum, smul_zero]
  have hsign₀ : quadSign Q₀ = -1 := by
    have heq : Q₀ = TauCeti.presentedForm ⟨6, fun _ : Fin 6 => c⟩ :=
      (TauCeti.presentedForm_eq_weightedSumSquares_coe (fun _ : Fin 6 => c)).symm
    rw [heq, quadSign_eq_signOf _ (TauCeti.nondegenerate_presentedForm _),
      TauCeti.formClass_presentedForm, signOf_mk_diag]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rcases Int.units_eq_one_or (toSign c) with h | h <;> rw [h] <;> decide
  obtain ⟨e⟩ := equivalent_of_quadSign_eq hQ hQ₀ (hdim.trans hdim₀.symm) (hs.trans hsign₀.symm)
  let b : Module.Basis (Fin 6) (ZMod 3) V :=
    (Pi.basisFun (ZMod 3) (Fin 6)).map e.symm.toLinearEquiv
  refine ⟨⟨b, ?_, ?_⟩⟩
  · intro i
    rw [Module.Basis.map_apply, Pi.basisFun_apply]
    change Q (e.symm (Pi.single i 1)) = (c : ZMod 3)
    rw [e.symm.map_app]
    exact hbasis i
  · intro i j hij
    rw [Module.Basis.map_apply, Module.Basis.map_apply, Pi.basisFun_apply, Pi.basisFun_apply]
    change polar Q (e.symm (Pi.single i 1)) (e.symm (Pi.single j 1)) = 0
    rw [e.symm.polar_apply]
    exact hpolar i j hij

theorem NFrame.invType_signChange_three (hQ : Q.Nondegenerate) {c : (ZMod 3)ˣ}
    (fr : NFrame Q ι (c : ZMod 3)) {J : Finset ι} (hJ : J.card = 3) :
    invType (fr.signChange J) = (3, -toSign c) := by
  have hcomm := fr.commSp_signChange_three J
  have hdim : invDim (fr.signChange J) = J.card := by
    simp only [invDim]
    rw [hcomm]
    exact fr.finrank_span_frame_three J
  have hsign' : invSign (fr.signChange J) = toSign c ^ J.card * (-1) ^ (J.card / 2) := by
    simp only [invSign]
    have hnd : (Q.restrict (Submodule.span (ZMod 3) (fr.b '' (J : Set ι)))).Nondegenerate :=
      hcomm ▸ nondegenerate_restrict_commSp hQ (fr.signChange_mul_self J)
    exact (congrArg (fun M => quadSign (Q.restrict M)) hcomm).trans
      (fr.quadSign_span_frame_three J hnd)
  have hsign : invSign (fr.signChange J) = -toSign c := by
    rw [hsign', hJ]
    rcases Int.units_eq_one_or (toSign c) with h | h <;> rw [h] <;> decide
  simp only [invType]
  rw [hdim, hsign, hJ]

theorem exists_signChange_three_type (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) (α : ℤˣ) :
    ∃ (c : ZMod 3) (fr : NFrame Q (Fin 6) c), invType (fr.signChange {0, 1, 2}) = (3, α) := by
  obtain ⟨c, hc⟩ : ∃ c : (ZMod 3)ˣ, -toSign c = α := by
    rcases Int.units_eq_one_or α with h | h
    · exact ⟨-1, by rw [h, toSign_neg_one_three]; decide⟩
    · exact ⟨1, by rw [h, map_one]⟩
  obtain ⟨fr⟩ := exists_nframe_six_unit hQ hdim hs c
  exact ⟨(c : ZMod 3), fr, by
    rw [fr.invType_signChange_three (J := {0, 1, 2}) hQ
      (by decide : ({0, 1, 2} : Finset (Fin 6)).card = 3), hc]⟩

end CFSG.OddStandard.SmallF3.Omega
