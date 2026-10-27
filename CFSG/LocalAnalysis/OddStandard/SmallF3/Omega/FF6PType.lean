module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PPerm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesInvol

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem ffC_ne_zero (i : Option (Fin 5)) : ffC i ≠ 0 := by
  cases i with
  | none => decide
  | some k => exact one_ne_zero

private def ffC' : Option (Fin 5) → (ZMod 3)ˣ :=
  fun i => Units.mk0 (ffC i) (ffC_ne_zero i)

private theorem ffC'_none : ffC' none = -1 := Units.ext rfl

private theorem ffC'_some (i : Fin 5) : ffC' (some i) = 1 := Units.ext rfl

private theorem toSign_neg_one_ff : toSign (-1 : (ZMod 3)ˣ) = -1 := by decide

private theorem PFrame.commSp_signChange_opt (fr : PFrame Q (Option (Fin 5)) ffC)
    (J : Finset (Option (Fin 5))) :
    commSp (fr.signChange J) = Submodule.span (ZMod 3) (fr.b '' (J : Set (Option (Fin 5)))) := by
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

private theorem PFrame.finrank_span_frame_opt (fr : PFrame Q (Option (Fin 5)) ffC)
    (J : Finset (Option (Fin 5))) :
    Module.finrank (ZMod 3)
      (Submodule.span (ZMod 3) (fr.b '' (J : Set (Option (Fin 5))))) = J.card := by
  have hli : LinearIndependent (ZMod 3) (fun i : J => fr.b (i : Option (Fin 5))) :=
    fr.b.linearIndependent.comp _ Subtype.val_injective
  have hrange : Set.range (fun i : J => fr.b (i : Option (Fin 5))) =
      fr.b '' (J : Set (Option (Fin 5))) := by
    rw [show Set.range (fun i : J => fr.b (i : Option (Fin 5))) =
        Set.range (fr.b ∘ Subtype.val) from rfl, Set.range_comp, Subtype.range_coe]
  rw [← hrange, finrank_span_eq_card hli, Fintype.card_coe]

private theorem PFrame.prod_toSign_ffC (J : Finset (Option (Fin 5))) :
    (∏ i : J, toSign (ffC' (i : Option (Fin 5)))) =
      (if none ∈ J then (-1 : ℤˣ) else 1) := by
  rw [Finset.prod_coe_sort (s := J) (f := fun i : Option (Fin 5) => toSign (ffC' i))]
  by_cases hnone : none ∈ J
  · rw [if_pos hnone]
    calc ∏ b ∈ J, toSign (ffC' b) = toSign (ffC' none) :=
          Finset.prod_eq_single none
            (fun b _ hne => by
              cases b with
              | none => exact absurd rfl hne
              | some j => rw [ffC'_some j, map_one])
            (fun hnot => absurd hnone hnot)
      _ = -1 := by rw [ffC'_none, toSign_neg_one_ff]
  · rw [if_neg hnone]
    apply Finset.prod_eq_one
    intro b hb
    have hne : b ≠ none := fun h => hnone (h ▸ hb)
    cases b with
    | none => exact absurd rfl hne
    | some j => rw [ffC'_some j, map_one]

private theorem PFrame.quadSign_span_frame_opt (fr : PFrame Q (Option (Fin 5)) ffC)
    (J : Finset (Option (Fin 5)))
    (hnd : (Q.restrict (Submodule.span (ZMod 3)
      (fr.b '' (J : Set (Option (Fin 5)))))).Nondegenerate) :
    quadSign (Q.restrict (Submodule.span (ZMod 3)
        (fr.b '' (J : Set (Option (Fin 5)))))) =
      (if none ∈ J then (-1 : ℤˣ) else 1) * (-1) ^ (J.card / 2) := by
  rcases J.eq_empty_or_nonempty with rfl | hne
  · rw [Finset.coe_empty, Set.image_empty, Submodule.span_empty]
    haveI : Subsingleton (⊥ : Submodule (ZMod 3) V) := by
      rw [Submodule.subsingleton_iff_eq_bot]
    rw [quadSign_of_subsingleton]
    simp
  · have hli : LinearIndependent (ZMod 3) (fun i : J => fr.b (i : Option (Fin 5))) :=
      fr.b.linearIndependent.comp _ Subtype.val_injective
    have hrange : Set.range (fun i : J => fr.b (i : Option (Fin 5))) =
        fr.b '' (J : Set (Option (Fin 5))) := by
      rw [show Set.range (fun i : J => fr.b (i : Option (Fin 5))) =
          Set.range (fr.b ∘ Subtype.val) from rfl, Set.range_comp, Subtype.range_coe]
    rw [← hrange]
    set N := Submodule.span (ZMod 3)
      (Set.range (fun i : J => fr.b (i : Option (Fin 5)))) with hN
    let B : Module.Basis J (ZMod 3) N := Module.Basis.span hli
    have hnd' : (Q.restrict N).Nondegenerate := by
      rw [hN, hrange]; exact hnd
    have hv : (QuadraticMap.associated (R := ZMod 3) (Q.restrict N)).IsOrthoᵢ B := by
      intro i j hij
      show QuadraticMap.associated (R := ZMod 3) (Q.restrict N) (B i) (B j) = 0
      have hi : ((B i : N) : V) = fr.b (i : Option (Fin 5)) :=
        Module.Basis.coe_span_apply hli i
      have hj : ((B j : N) : V) = fr.b (j : Option (Fin 5)) :=
        Module.Basis.coe_span_apply hli j
      have hinner : (Q.restrict N) (B i + B j) - (Q.restrict N) (B i) -
          (Q.restrict N) (B j) = 0 := by
        simp only [QuadraticMap.restrict_apply]
        rw [Submodule.coe_add, hi, hj,
          CFSG.RankThree.OrthogonalInvolutions.map_add_eq Q
            (fr.b (i : Option (Fin 5))) (fr.b (j : Option (Fin 5))),
          fr.orth (i : Option (Fin 5)) (j : Option (Fin 5))
            (Subtype.val_injective.ne hij), add_zero]
        abel
      rw [QuadraticMap.associated_apply, hinner, smul_zero]
    have hw : (fun i : J => (Q.restrict N) (B i)) =
        fun i : J => ffC (i : Option (Fin 5)) := by
      funext i
      rw [QuadraticMap.restrict_apply, Module.Basis.coe_span_apply hli i]
      exact fr.norm (i : Option (Fin 5))
    have hrepr : (Q.restrict N).basisRepr B =
        QuadraticMap.weightedSumSquares (ZMod 3)
          (fun i : J => ffC (i : Option (Fin 5))) := by
      rw [QuadraticMap.basisRepr_eq_of_iIsOrtho _ B hv, hw]
    have h1 : quadSign (Q.restrict N) =
        quadSign (QuadraticMap.weightedSumSquares (ZMod 3)
          (fun i : J => ffC (i : Option (Fin 5)))) := by
      rw [← hrepr]
      exact quadSign_congr hnd' ⟨QuadraticMap.isometryEquivBasisRepr _ B⟩
    have hndw : (QuadraticMap.weightedSumSquares (ZMod 3)
        (fun i : J => ffC (i : Option (Fin 5)))).Nondegenerate :=
      QuadraticMap.nondegenerate_weightedSumSquares (fun i => by
        rw [isRegular_iff_ne_zero]
        exact ffC_ne_zero (i : Option (Fin 5)))
    have heq : QuadraticMap.weightedSumSquares (ZMod 3)
        (fun k : Fin J.card => ffC ((Finset.equivFin J).symm k : Option (Fin 5))) =
        TauCeti.presentedForm ⟨J.card,
          fun k : Fin J.card => ffC' ((Finset.equivFin J).symm k)⟩ :=
      (TauCeti.presentedForm_eq_weightedSumSquares_coe
        (w := fun k : Fin J.card => ffC' ((Finset.equivFin J).symm k))).symm
    have h2 : quadSign (QuadraticMap.weightedSumSquares (ZMod 3)
        (fun i : J => ffC (i : Option (Fin 5)))) =
        quadSign (TauCeti.presentedForm ⟨J.card,
          fun k : Fin J.card => ffC' ((Finset.equivFin J).symm k)⟩) := by
      rw [← heq]
      exact quadSign_congr hndw ⟨QuadraticForm.isometryEquivWeightedSumSquaresReindex
        (w := fun i : J => ffC (i : Option (Fin 5))) (e := (Finset.equivFin J).symm)⟩
    rw [h1, h2, quadSign_eq_signOf _ (TauCeti.nondegenerate_presentedForm _),
      TauCeti.formClass_presentedForm, signOf_mk_diag]
    rw [← PFrame.prod_toSign_ffC J]
    congr 1
    exact (Fintype.prod_equiv (Finset.equivFin J)
      (fun i : J => toSign (ffC' (i : Option (Fin 5))))
      (fun k : Fin J.card => toSign (ffC' ((Finset.equivFin J).symm k)))
      (fun x => by simp)).symm

theorem exists_pframe_six_plus (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hs : quadSign Q = 1) : Nonempty (PFrame Q (Option (Fin 5)) ffC) := by
  let Q₀ : QuadraticForm (ZMod 3) (Option (Fin 5) → ZMod 3) :=
    QuadraticMap.weightedSumSquares (ZMod 3) ffC
  have hQ₀ : Q₀.Nondegenerate := by
    refine QuadraticMap.nondegenerate_weightedSumSquares (fun i => ?_)
    rw [isRegular_iff_ne_zero]
    exact ffC_ne_zero i
  have hdim₀ : Module.finrank (ZMod 3) (Option (Fin 5) → ZMod 3) = 6 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_option, Fintype.card_fin]
  have hsign₀ : quadSign Q₀ = 1 := by
    let e6 : Option (Fin 5) ≃ Fin 6 :=
      Fintype.equivFinOfCardEq (α := Option (Fin 5)) (n := 6) (by
        rw [Fintype.card_option, Fintype.card_fin])
    have h1a : quadSign Q₀ =
        quadSign (QuadraticMap.weightedSumSquares (ZMod 3)
          (fun k : Fin 6 => ffC (e6.symm k))) :=
      quadSign_congr hQ₀ ⟨QuadraticForm.isometryEquivWeightedSumSquaresReindex
        (w := ffC) (e := e6.symm)⟩
    have h1b : quadSign (QuadraticMap.weightedSumSquares (ZMod 3)
          (fun k : Fin 6 => ffC (e6.symm k))) =
        quadSign (TauCeti.presentedForm ⟨6, fun k : Fin 6 => ffC' (e6.symm k)⟩) :=
      congrArg quadSign (TauCeti.presentedForm_eq_weightedSumSquares_coe
        (w := fun k : Fin 6 => ffC' (e6.symm k))).symm
    have hprod : (∏ k : Fin 6, toSign (ffC' (e6.symm k))) = -1 := by
      rw [Equiv.prod_comp e6.symm (fun i : Option (Fin 5) => toSign (ffC' i))]
      rw [Fintype.prod_option]
      have hsome : (∏ i : Fin 5, toSign (ffC' (some i))) = 1 := by
        apply Finset.prod_eq_one
        intro i _
        rw [ffC'_some i, map_one]
      rw [hsome, ffC'_none, toSign_neg_one_ff, mul_one]
    rw [h1a, h1b, quadSign_eq_signOf _ (TauCeti.nondegenerate_presentedForm _),
      TauCeti.formClass_presentedForm, signOf_mk_diag, hprod]
    decide
  obtain ⟨e⟩ := equivalent_of_quadSign_eq hQ hQ₀ (hdim.trans hdim₀.symm) (hs.trans hsign₀.symm)
  let b : Module.Basis (Option (Fin 5)) (ZMod 3) V :=
    (Pi.basisFun (ZMod 3) (Option (Fin 5))).map e.symm.toLinearEquiv
  refine ⟨⟨b, ?_, ?_⟩⟩
  · intro i
    rw [Module.Basis.map_apply, Pi.basisFun_apply]
    change Q (e.symm (Pi.single i (1 : ZMod 3))) = ffC i
    rw [e.symm.map_app]
    change QuadraticMap.weightedSumSquares (ZMod 3) ffC
      (Pi.single i (1 : ZMod 3)) = ffC i
    rw [QuadraticMap.weightedSumSquares_apply]
    rw [Finset.sum_eq_single i
      (fun j _ hji => by rw [Pi.single_eq_of_ne hji, mul_zero, smul_zero])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    rw [Pi.single_eq_same, mul_one, smul_eq_mul, mul_one]
  · intro i j hij
    rw [Module.Basis.map_apply, Module.Basis.map_apply, Pi.basisFun_apply, Pi.basisFun_apply]
    change polar Q (e.symm (Pi.single i (1 : ZMod 3)))
        (e.symm (Pi.single j (1 : ZMod 3))) = 0
    rw [e.symm.polar_apply]
    change QuadraticMap.polar (QuadraticMap.weightedSumSquares (ZMod 3) ffC)
      (Pi.single i (1 : ZMod 3)) (Pi.single j (1 : ZMod 3)) = 0
    rw [← QuadraticMap.polarBilin_apply_apply]
    have h2 : (2 : ZMod 3) • QuadraticMap.associated (R := ZMod 3)
        (QuadraticMap.weightedSumSquares (ZMod 3) ffC)
        (Pi.single i (1 : ZMod 3)) (Pi.single j (1 : ZMod 3)) =
        QuadraticMap.polarBilin (QuadraticMap.weightedSumSquares (ZMod 3) ffC)
          (Pi.single i (1 : ZMod 3)) (Pi.single j (1 : ZMod 3)) := by
      have h := DFunLike.congr_fun (DFunLike.congr_fun
        (QuadraticMap.two_nsmul_associated (S := ZMod 3)
          (QuadraticMap.weightedSumSquares (ZMod 3) ffC))
        (Pi.single i (1 : ZMod 3))) (Pi.single j (1 : ZMod 3))
      simp only [LinearMap.smul_apply, Pi.smul_apply, nsmul_eq_mul] at h
      have hcast : (↑(2 : ℕ) : ZMod 3) = 2 := by norm_num
      rw [hcast] at h
      simpa only [smul_eq_mul] using h
    rw [← h2, QuadraticMap.associated_weightedSumSquares]
    have hsum : (∑ m : Option (Fin 5), ffC m *
        ((Pi.single i (1 : ZMod 3) : Option (Fin 5) → ZMod 3) m *
          (Pi.single j (1 : ZMod 3) : Option (Fin 5) → ZMod 3) m)) = 0 := by
      apply Finset.sum_eq_zero
      intro m _
      by_cases hmi : m = i
      · subst hmi
        rw [Pi.single_eq_same, Pi.single_eq_of_ne hij, mul_zero, mul_zero]
      · rw [Pi.single_eq_of_ne hmi, zero_mul, mul_zero]
    rw [hsum, smul_zero]

theorem PFrame.invType_signChange (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    (J : Finset (Option (Fin 5))) :
    invType (fr.signChange J) =
      (J.card, (if none ∈ J then (-1 : ℤˣ) else 1) * (-1) ^ (J.card / 2)) := by
  have hcomm := PFrame.commSp_signChange_opt fr J
  have hdim : invDim (fr.signChange J) = J.card := by
    simp only [invDim]
    rw [hcomm]
    exact PFrame.finrank_span_frame_opt fr J
  have hsign : invSign (fr.signChange J) =
      (if none ∈ J then (-1 : ℤˣ) else 1) * (-1) ^ (J.card / 2) := by
    simp only [invSign]
    have hnd : (Q.restrict (Submodule.span (ZMod 3)
        (fr.b '' (J : Set (Option (Fin 5)))))).Nondegenerate :=
      hcomm ▸ nondegenerate_restrict_commSp hQ (fr.signChange_mul_self J)
    exact (congrArg (fun M => quadSign (Q.restrict M)) hcomm).trans
      (PFrame.quadSign_span_frame_opt fr J hnd)
  simp only [invType]
  rw [hdim, hsign]

end CFSG.OddStandard.SmallF3.Omega
