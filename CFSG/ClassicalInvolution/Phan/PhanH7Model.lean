module

public import CFSG.ClassicalInvolution.Phan.PhanH6Fix

public section

namespace CFSG.ClassicalInvolution.PhanB3.H

open CliffordAlgebra QuadraticMap CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution
open CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras CFSG.ClassicalInvolution.WeakCT
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.LieType.Steinberg.Sp (blockMat)
open CFSG.ClassicalInvolution.Asc77.B3C (twShort Pel kron2 kronMat Pmat mat_Pel mat_kron2
  twShort_apply)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair Su B12 B23)
open scoped MatrixGroups commutatorElement

section Lifts

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {m : ℕ}

theorem longSL2_spec (F₀ : HypFrame Q m) {i j : Fin m} (hij : i ≠ j) (s t : Bool)
    (h4 : 4 ≤ Nat.card K) :
    (F₀.longSL2 hij s t).range.map (spinAction Q) = (F₀.toFrame hij s t).La.range ∧
      ⁅(F₀.longSL2 hij s t).range, (F₀.longSL2 hij s t).range⁆ = (F₀.longSL2 hij s t).range ∧
      ∀ r ∈ (F₀.longSL2 hij s t).range, spinAction Q r = 1 → r = 1 := by
  refine ⟨map_longSL2_range F₀ hij s t, ?_, ?_⟩
  · have hperf : Group.IsPerfect SL(2, K) := sl2_isPerfect h4
    exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.range _)
  · rintro r ⟨A, rfl⟩ hr
    have hθ := DFunLike.congr_fun (spinAction_comp_longSL2 F₀ hij s t) A
    have h1 : (F₀.toFrame hij s t).La A = 1 := by rw [← hθ]; exact hr
    have : A = 1 := (F₀.toFrame hij s t).La_injective (h1.trans (map_one _).symm)
    subst this
    simp

end Lifts

section Odd

variable {p e : ℕ} [Fact p.Prime]

theorem exists_lift_frame_odd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (fr : Frame (quadOdd 3 (GaloisField p e))) :
    ∃ R ∈ longestFundamental (oddDatum 3 (GaloisField p e)),
      R.map (spinAction (quadOdd 3 (GaloisField p e))) = fr.La.range ∧ ⁅R, R⁆ = R ∧
        ∀ r ∈ R, spinAction (quadOdd 3 (GaloisField p e)) r = 1 → r = 1 := by
  obtain ⟨hodd, h4⟩ := card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_galoisField e hp2
  have hk : (0 : ℕ) + 1 < 3 := by omega
  set k₀ : Fin 3 := ⟨0, by omega⟩ with hk₀
  set j₀ : Fin 3 := ⟨0 + 1, hk⟩ with hj₀
  have hij : k₀ ≠ j₀ := Fin.ne_of_val_ne (by simp [hk₀, hj₀])
  set fr₀ := (oddFrame 3 (GaloisField p e)).toHypFrame.toFrame hij true false with hfr₀
  have hdim : Module.finrank (GaloisField p e) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p e) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
  have hperp : 2 ≤ Module.finrank (GaloisField p e) fr₀.perp := by
    have := finrank_perp_add_four fr₀
    omega
  have : Invertible (2 : GaloisField p e) := invertibleOfNonzero h2
  obtain ⟨x, hx⟩ := exists_spin_conj hodd (nondegenerate_polarBilin_quadOdd 3 _ h2) fr₀ fr hperp
  have hlong : Generic.IsLongestRoot (oddDatum 3 (GaloisField p e)) (Pi.single k₀ 1) :=
    isLongest_single_cartanB (m := 3) (by omega) rfl _ (by show 0 + 1 < 3; omega)
  have hR : CFSG.LieType.CurtisTits.rankOne (oddRootGroup 3 (GaloisField p e)) k₀ =
      (rankOneB (GaloisField p e) k₀).range :=
    le_antisymm (OddCT.rankOne_le_range k₀) (by
      rintro _ ⟨M, rfl⟩
      exact OddCT.rankOneB_mem_rankOne k₀ M)
  rw [rankOneB_of_lt (GaloisField p e) hk rfl hij] at hR
  obtain ⟨hmap, hperf, hinj⟩ := longSL2_spec (oddFrame 3 (GaloisField p e)).toHypFrame hij true
    false h4
  refine ⟨((oddFrame 3 (GaloisField p e)).toHypFrame.longSL2 hij true false).range.map
      (MulAut.conj x).toMonoidHom, ⟨x, Pi.single k₀ 1, hlong, ?_⟩, ?_, ?_, ?_⟩
  · exact congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hR.symm
  · rw [map_conj_map, hmap, La_range_eq_map_conj hx]
  · rw [← Subgroup.map_commutator, hperf]
  · rintro r ⟨r', hr', rfl⟩ hr
    have h2' : spinAction (quadOdd 3 (GaloisField p e)) x *
        spinAction (quadOdd 3 (GaloisField p e)) r' *
        (spinAction (quadOdd 3 (GaloisField p e)) x)⁻¹ = 1 := by
      simpa [MulAut.conj_apply, map_mul, map_inv] using hr
    have h3 : spinAction (quadOdd 3 (GaloisField p e)) r' = 1 := by
      have := congrArg (fun y => (spinAction (quadOdd 3 (GaloisField p e)) x)⁻¹ * y *
        spinAction (quadOdd 3 (GaloisField p e)) x) h2'
      simpa [mul_assoc] using this
    have := hinj r' hr' h3
    subst this
    simp

end Odd

section Disjoint

variable {F : Type} [Field F]

theorem B12_inf_B23_su {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] :
    B12 K p f ⊓ B23 K p f = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨A, rfl⟩, ⟨A', hA'⟩⟩
  rw [Subgroup.mem_bot]
  have h' := congrArg (fun g : Su K p f 3 => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hA'
  simp only [CFSG.LieType.Steinberg.coe_embSUid] at h'
  have e00 := congrFun (congrFun h' 0) 0
  have e01 := congrFun (congrFun h' 0) 1
  have e10 := congrFun (congrFun h' 1) 0
  simp [CFSG.LieType.Steinberg.embPair] at e00 e01 e10
  have hdet := A.2.1
  rw [Matrix.det_fin_two] at hdet
  have e11 : ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    rw [← e00, ← e01, ← e10] at hdet
    simpa using hdet
  have hA1 : A = 1 := by
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    fin_cases i <;> fin_cases j <;> simp [← e00, ← e01, ← e10, e11]
  rw [hA1, map_one]

theorem La_eq_one_of_fix {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (fr : Frame Q) {A : SL(2, K)}
    (h : ∀ x ∈ fr.span, fr.La A x = x) : A = 1 := by
  have h1 := h (fr.incl 1) (LinearMap.mem_range_self _ _)
  rw [Frame.La_apply_incl] at h1
  have h2 := Frame.incl_injective fr h1
  exact Subtype.ext (by simpa using h2)

theorem longBlock_inf_twShort (h2 : (2 : F) ≠ 0) :
    (longBlock F 2 1).range ⊓ (twShort h2).range = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨A, rfl⟩, ⟨A', hA'⟩⟩
  rw [Subgroup.mem_bot]
  have hPi : Pmat F * mat 2 F ((Pel h2)⁻¹) = 1 := by
    rw [← mat_Pel h2, ← map_mul, mul_inv_cancel, map_one]
  have h1 : mat 2 F (twShort h2 A') = mat 2 F (longBlock F 2 1 A) := by rw [hA']
  rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.mat_longBlock, twShort_apply, map_mul,
    map_mul, mat_kron2, mat_Pel] at h1
  have key : Pmat F * blockMat (Sum.inl (1 : Fin 2)) (Sum.inr (1 : Fin 2))
      (A : Matrix (Fin 2) (Fin 2) F) = kronMat (A' : Matrix (Fin 2) (Fin 2) F) * Pmat F := by
    rw [← h1]
    calc Pmat F * (mat 2 F ((Pel h2)⁻¹) * kronMat (A' : Matrix (Fin 2) (Fin 2) F) * Pmat F)
        = (Pmat F * mat 2 F ((Pel h2)⁻¹)) * kronMat (A' : Matrix (Fin 2) (Fin 2) F) * Pmat F := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPi, Matrix.one_mul]
  have e00 := congrFun (congrFun key (.inl 0)) (.inl 0)
  have e02 := congrFun (congrFun key (.inl 0)) (.inr 0)
  have e20 := congrFun (congrFun key (.inr 0)) (.inl 0)
  have e30 := congrFun (congrFun key (.inr 1)) (.inl 0)
  simp [Pmat, kronMat, blockMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
    Matrix.fromBlocks, Matrix.one_apply] at e00 e02 e20 e30
  have e02' : (A' : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := e02.resolve_right h2
  have hA1 : A' = 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;>
      first | exact e00.symm | exact e02' | exact e20.symm | exact e30.symm
  rw [← hA', hA1, map_one]

end Disjoint

section Model

variable {p f : ℕ} [Fact p.Prime]

theorem not_isSquare_neg_one (hmod : p ^ f % 4 = 3) : ¬ IsSquare (-1 : GaloisField p f) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hmod
  have hK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have : Fintype (GaloisField p f) := Fintype.ofFinite _
  rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hK]
  omega

structure ModelB3 (p f : ℕ) [Fact p.Prime] (h2 : (2 : GaloisField p f) ≠ 0) where
  D : ThetaData (GaloisField p f) h2
  R₀ : Subgroup (spinGroup (quadOdd 3 (GaloisField p f)))
  mem_longest : R₀ ∈ longestFundamental (oddDatum 3 (GaloisField p f))
  map_eq : R₀.map (spinAction (quadOdd 3 (GaloisField p f))) = (fr0 h2).La.range
  perfect : ⁅R₀, R₀⁆ = R₀
  inj : ∀ r ∈ R₀, spinAction (quadOdd 3 (GaloisField p f)) r = 1 → r = 1
  comm : Commutes R₀ ((twShort h2).range.map D.θ)
  unitary : ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W R₀
    ((longBlock (GaloisField p f) 2 1).range.map D.θ)
  disj01 : R₀ ⊓ (longBlock (GaloisField p f) 2 1).range.map D.θ = ⊥
  disj02 : R₀ ⊓ (twShort h2).range.map D.θ = ⊥
  disj12 : (longBlock (GaloisField p f) 2 1).range.map D.θ ⊓ (twShort h2).range.map D.θ = ⊥

variable {h2 : (2 : GaloisField p f) ≠ 0}

@[expose] noncomputable def ModelB3.U (M : ModelB3 p f h2) :
    Fin 3 → Subgroup (spinGroup (quadOdd 3 (GaloisField p f))) :=
  ![M.R₀, (longBlock (GaloisField p f) 2 1).range.map M.D.θ, (twShort h2).range.map M.D.θ]

theorem exists_modelB3 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hmod : p ^ f % 4 = 3)
    (h2 : (2 : GaloisField p f) ≠ 0) : Nonempty (ModelB3 p f h2) := by
  classical
  obtain ⟨hodd, h4⟩ := card_galoisField_facts hp2 hq
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have hK' : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := card_galoisField_two_mul p f hf
  let _ : Algebra (GaloisField p f) (GaloisField p (2 * f)) :=
    Classical.choice (Aniso.nonempty_algebra hK hK')
  have hn1 : ¬ IsSquare (-1 : GaloisField p f) := not_isSquare_neg_one hmod
  obtain ⟨D⟩ := exists_thetaData (F := GaloisField p f) h4 h2
  obtain ⟨R₀, hmem, himg, hperf, hinj⟩ := exists_lift_frame_odd hp2 hq (fr0 h2)
  obtain ⟨hU1map, hU1perf, hU1inj⟩ := longSL2_spec (hyp1 h2) (i := 0) (j := 1) (by decide) true
    false h4
  have hU1eq : (longBlock (GaloisField p f) 2 1).range.map D.θ =
      ((hyp1 h2).longSL2 (i := 0) (j := 1) (by decide) true false).range := by
    rw [← MonoidHom.range_comp, ← spBlock_one_eq_longBlock,
      theta_comp_spBlock_one h2 D.isLevi D.coe_θ]
  set U₁ := (longBlock (GaloisField p f) 2 1).range.map D.θ with hU₁
  have hU1map' : U₁.map (spinAction (quadOdd 3 (GaloisField p f))) = (fr1 h2).La.range := by
    rw [hU1eq]
    exact hU1map
  have hU1perf' : ⁅U₁, U₁⁆ = U₁ := by rw [hU1eq]; exact hU1perf
  have hU1inj' : ∀ r ∈ U₁, spinAction (quadOdd 3 (GaloisField p f)) r = 1 → r = 1 := by
    rw [hU1eq]; exact hU1inj
  obtain ⟨θs, hθinj, -, hθU, hθV⟩ := Frame.exists_hom_of_not_hasSingularVector
    (K' := GaloisField p (2 * f)) (p := p) (f := f) hK hK' hodd (F₁ := fr0 h2) (F₂ := fr1 h2)
    (fr1_comm_fr0 h2).symm (finrank_inf_fr h2) (not_hasSingularVector_inf_fr h2 hn1)
  have hker : θs.ker ≤ Subgroup.center (Su (GaloisField p (2 * f)) p f 3) := by
    rw [(MonoidHom.ker_eq_bot_iff θs).mpr hθinj]
    exact bot_le
  let R : Fin 2 → Subgroup (spinGroup (quadOdd 3 (GaloisField p f))) := ![R₀, U₁]
  let fr : Fin 2 → Frame (quadOdd 3 (GaloisField p f)) := ![fr0 h2, fr1 h2]
  have hRspec : ∀ k, (R k).map (spinAction (quadOdd 3 (GaloisField p f))) = (fr k).La.range ∧
      ⁅R k, R k⁆ = R k ∧
      ∀ r ∈ R k, spinAction (quadOdd 3 (GaloisField p f)) r = 1 → r = 1 := by
    intro k
    fin_cases k
    · exact ⟨himg, hperf, hinj⟩
    · exact ⟨hU1map', hU1perf', hU1inj'⟩
  have hfinite : Finite (spinGroup (quadOdd 3 (GaloisField p f))) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  have S : SpinCtx p f (quadOdd 3 (GaloisField p f)) (Set.range R) :=
    { hp2 := hp2
      hq := hq
      hQ := nondegenerate_polarBilin_quadOdd 3 (GaloisField p f) h2
      fin := hfinite
      hker2 := OrthAut.odd_hker2 h2 3
      hC := RouteD.Gaps.not_dvd_card_center_odd hp2 (le_refl 3)
      perf := by
        rintro _ ⟨k, rfl⟩
        exact (hRspec k).2.1
      inj := by
        rintro _ ⟨k, rfl⟩
        exact (hRspec k).2.2
      map := by
        rintro _ ⟨k, rfl⟩
        exact ⟨_, fr k, (hRspec k).1, rfl⟩ }
  have hunit : ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W R₀ U₁ :=
    S.unitary_of_map (R₁ := R₀) (R₂ := U₁) ⟨0, rfl⟩ ⟨1, rfl⟩ ⟨θs.range,
      Models.unitaryBlockStandardPair_of_normalized hker rfl (by rw [himg]; exact hθU)
        (by rw [hU1map']; exact hθV)⟩
  have hmapinf : ∀ A B : Subgroup (spinGroup (quadOdd 3 (GaloisField p f))),
      (∀ r ∈ A, spinAction (quadOdd 3 (GaloisField p f)) r = 1 → r = 1) →
      A.map (spinAction (quadOdd 3 (GaloisField p f))) ⊓
        B.map (spinAction (quadOdd 3 (GaloisField p f))) = ⊥ → A ⊓ B = ⊥ := by
    intro A B hA h
    rw [eq_bot_iff]
    rintro g ⟨hgA, hgB⟩
    have : spinAction (quadOdd 3 (GaloisField p f)) g ∈
        A.map (spinAction (quadOdd 3 (GaloisField p f))) ⊓
          B.map (spinAction (quadOdd 3 (GaloisField p f))) :=
      ⟨⟨g, hgA, rfl⟩, ⟨g, hgB, rfl⟩⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (hA g hgA this)
  have d01 : R₀ ⊓ U₁ = ⊥ := by
    refine hmapinf _ _ hinj ?_
    rw [himg, hU1map', ← hθU, ← hθV, ← Subgroup.map_inf _ _ θs hθinj, B12_inf_B23_su,
      Subgroup.map_bot]
  have d02 : R₀ ⊓ (twShort h2).range.map D.θ = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hg0, y, ⟨B, rfl⟩, hy⟩
    rw [Subgroup.mem_bot]
    apply hinj g hg0
    obtain ⟨A, hA⟩ : spinAction (quadOdd 3 (GaloisField p f)) g ∈ (fr0 h2).La.range := by
      rw [← himg]
      exact ⟨g, hg0, rfl⟩
    have hfix : ∀ x ∈ (fr0 h2).span, (fr0 h2).La A x = x := by
      intro x hx
      rw [hA, ← hy]
      exact theta_twShort_fix_span D.isLevi D.nat D.fix h2 B hx
    rw [← hA, La_eq_one_of_fix (fr0 h2) hfix, map_one]
  have d12 : U₁ ⊓ (twShort h2).range.map D.θ = ⊥ := by
    rw [hU₁, ← Subgroup.map_inf _ _ D.θ D.θ_inj, longBlock_inf_twShort h2, Subgroup.map_bot]
  exact ⟨⟨D, R₀, hmem, himg, hperf, hinj,
    commutes_of_lift h2 D.isLevi D.nat D.fix hperf himg, hunit, d01, d02, d12⟩⟩

end Model

end CFSG.ClassicalInvolution.PhanB3.H
