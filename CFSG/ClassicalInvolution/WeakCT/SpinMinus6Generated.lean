module

public import CFSG.ClassicalInvolution.WeakCT.TwistedSpinModel

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CliffordAlgebra QuadraticMap CFSG.LieType.RootSystem CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.CurtisTits CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
open scoped MatrixGroups

section Generation

variable {F : Type} [Field F] {b c : F}

theorem range_spinAction_quadMinus_three [Finite F] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    (spinAction (quadMinus 3 F b c)).range = elementaryGroup (quadMinus 3 F b c) :=
  range_spinAction_eq_elementaryGroup (nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr)
    (by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
        Fintype.card_fin]
      omega)
    (minusPair_orth (K := F) (b := b) (c := c) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
      (by simp))

omit [Field F] in
theorem eq_top_of_ker_le_of_range_le_map {G M : Type*} [Group G] [Group M] (φ : G →* M)
    {R : Subgroup G} (hker : φ.ker ≤ R) (hR : φ.range ≤ R.map φ) : R = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨r, hr, hrg⟩ := Subgroup.mem_map.mp (hR (MonoidHom.mem_range.mpr ⟨g, rfl⟩))
  have h : r⁻¹ * g ∈ R := hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hrg, inv_mul_cancel])
  have := R.mul_mem hr h
  rwa [mul_inv_cancel_left] at this

theorem spinAction_eq_one_of_fixes {n : ℕ} {g : spinGroup (quadMinus n F b c)}
    (he : ∀ j, spinAction (quadMinus n F b c) g (eVec n j) = eVec n j)
    (hf : ∀ j, spinAction (quadMinus n F b c) g (fVec n j) = fVec n j)
    (hp : ∀ w, spinAction (quadMinus n F b c) g (planeVec n w) = planeVec n w) :
    spinAction (quadMinus n F b c) g = 1 := by
  refine LinearEquiv.ext fun v => ?_
  have key : ((spinAction (quadMinus n F b c) g : Vm n F ≃ₗ[F] Vm n F) : Vm n F →ₗ[F] Vm n F) =
      LinearMap.id := by
    refine LinearMap.pi_ext fun i x => ?_
    have hx : (Pi.single i x : Vm n F) = x • (Pi.single i 1 : Vm n F) := by
      rw [← Pi.single_smul]
      simp
    rw [hx]
    rcases i with j | j | t
    · rw [LinearMap.map_smul]
      exact congrArg (x • ·) (he j)
    · rw [LinearMap.map_smul]
      exact congrArg (x • ·) (hf j)
    · have hs : (Pi.single (.inr (.inr t)) 1 : Vm n F) = planeVec n (Pi.single t 1) := by
        funext y
        rcases y with k | k | t' <;> simp [planeVec, Pi.single_apply]
      rw [LinearMap.map_smul]
      exact congrArg (x • ·) (by rw [hs]; exact hp _)
  exact LinearMap.congr_fun key v

theorem spinAction_shortTorusElt_neg_planeOne (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (n : ℕ)
    (k : Fin (n - 1)) :
    spinAction (quadMinus n F b c) (shortTorusElt n hirr k (-planeOne)) = 1 := by
  have ha : (-planeOne : Fin 2 → F) ≠ 0 := neg_ne_zero.mpr planeOne_ne_zero
  have hN : planeNorm b c (-planeOne : Fin 2 → F) = 1 := by
    rw [planeNorm_neg, planeNorm_planeOne]
  refine spinAction_eq_one_of_fixes (fun j => ?_) (fun j => ?_) (fun w => ?_)
  · by_cases hj : j = k
    · subst hj
      rw [spinAction_shortTorusElt_eVec n hirr j ha, hN, one_smul]
    · exact spinAction_shortTorusElt_eVec_of_ne n hirr hj _
  · by_cases hj : j = k
    · subst hj
      rw [spinAction_shortTorusElt_fVec n hirr j ha, hN, inv_one, one_smul]
    · exact spinAction_shortTorusElt_fVec_of_ne n hirr hj _
  · rw [spinAction_shortTorusElt_planeVec n hirr k ha, planeRefl_neg,
      planeRefl_planeRefl planeNorm_planeOne_ne_zero]

theorem ker_spinAction_le_of_short_mem [Finite F] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (h2 : (2 : F) ≠ 0) {R : Subgroup (spinGroup (quadMinus 3 F b c))}
    (hR : haveI := fact_shortField hirr
      shortBlock hirr 3 finOne (torusHom (ShortField b c) (-1)) ∈ R) :
    (spinAction (quadMinus 3 F b c)).ker ≤ R := by
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  set h := shortBlock hirr 3 finOne (torusHom (ShortField b c) (-1)) with hh
  have hfc : fieldCoord (((-1 : (ShortField b c)ˣ)) : ShortField b c) = -planeOne := by
    ext j
    fin_cases j <;> simp [fieldCoord, planeOne, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have hker : h ∈ (spinAction (quadMinus 3 F b c)).ker := by
    rw [MonoidHom.mem_ker, hh, shortBlock_torus, hfc]
    exact spinAction_shortTorusElt_neg_planeOne hirr 3 finOne
  have hne : h ≠ 1 := by
    intro h1
    have hinj := shortBlock_injective hirr h2 3 finOne
    have h1' : torusHom (ShortField b c) (-1) = 1 := hinj (h1.trans (map_one _).symm)
    have := congrArg (fun M : SL(2, ShortField b c) => (M : Matrix (Fin 2) (Fin 2) (ShortField b c)) 0 0) h1'
    simp [coe_torusHom] at this
    have h2' : (2 : ShortField b c) ≠ 0 := by
      intro h0
      apply h2
      have h3 : algebraMap F (ShortField b c) 2 = algebraMap F (ShortField b c) 0 := by
        rw [map_ofNat, map_zero]
        exact h0
      exact (algebraMap F (ShortField b c)).injective h3
    exact h2' (by linear_combination -this)
  have hcent := isCentral_cliffordAlgebra_quadMinus 3 b c hirr
  have hh1 : (h : CliffordAlgebra (quadMinus 3 F b c)) = -1 :=
    ((mem_ker_spinAction_iff_of_isCentral _ h).1 hker).resolve_left hne
  intro x hx
  rcases (mem_ker_spinAction_iff_of_isCentral _ x).1 hx with rfl | hx1
  · exact R.one_mem
  · have : x = h := Subtype.ext (hx1.trans hh1.symm)
    rw [this]
    exact hR

end Generation

section Datum

variable {F : Type} [Field F] [Finite F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

omit [Finite F] in
theorem elementaryGroup_le_map_iSup_three :
    elementaryGroup (quadMinus 3 F b c) ≤
      (⨆ γ ∈ roots (isFiniteType_cartanB (3 - 1)) ∅, minusRootGroup 3 hirr γ).map
        (spinAction (quadMinus 3 F b c)) := by
  refine (minusFrame 3 b c).toHypFrame.elementaryGroup_le_map_spinAction ?_ ?_ ?_
  · intro i j hij s t x
    have hγ := mem_roots_of_toStdB_eq_long 3 hij s t
      (toStdB_ofStdB (3 - 1) (Pi.single i (boolSign s) + Pi.single j (boolSign t)))
    exact Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem hγ
      (longRoot_mem_minusRootGroup 3 hirr hij s t (toStdB_ofStdB (3 - 1) _) x))
  · intro i s v hv
    rw [eq_planeVec_of_polar_minusVec 3 b c hv, minusFrame_vec,
      ← spinAction_twShortRoot_eq_eichler 3 hirr i s]
    have hγ := mem_roots_of_toStdB_eq_short 3 i s
      (toStdB_ofStdB (3 - 1) (Pi.single i (boolSign s)))
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem hγ
      (twShortRoot_mem_minusRootGroup 3 hirr i s (toStdB_ofStdB (3 - 1) _) _)))
  · intro v hv hQ
    rw [eq_planeVec_of_polar_minusVec 3 b c hv] at hQ ⊢
    rw [quadMinus_planeVec'] at hQ
    by_contra h0
    refine planeNorm_ne_zero hirr (fun hw => h0 ?_) hQ
    rw [hw, planeVec_zero]

theorem minusDatum_iSup_eq_top_three (h2 : (2 : F) ≠ 0) :
    ⨆ γ ∈ roots (isFiniteType_cartanB (3 - 1)) ∅, minusRootGroup 3 hirr γ = ⊤ := by
  have := fact_shortField hirr
  refine eq_top_of_ker_le_of_range_le_map (spinAction (quadMinus 3 F b c)) ?_ ?_
  · refine ker_spinAction_le_of_short_mem hirr h2 ?_
    have hk : ¬ (finOne : Fin (3 - 1)).val + 1 < 3 - 1 := by decide
    have hα := mem_roots_of_toStdB_eq_short 3 finOne true (toStdB_single_of_not_lt' 3 hk)
    have hα' := mem_roots_of_toStdB_eq_short 3 finOne false (toStdB_neg_single_of_not_lt' 3 hk)
    have hle : rankOne (minusDatum 3 hirr).rootGroup finOne ≤
        ⨆ γ ∈ roots (isFiniteType_cartanB (3 - 1)) ∅, minusRootGroup 3 hirr γ :=
      sup_le (le_iSup₂_of_le (f := fun γ _ => minusRootGroup 3 hirr γ) _ hα le_rfl)
        (le_iSup₂_of_le (f := fun γ _ => minusRootGroup 3 hirr γ) _ hα' le_rfl)
    rw [rankOne_minusDatum_short hirr hk] at hle
    exact hle ⟨_, rfl⟩
  · rw [range_spinAction_quadMinus_three hirr]
    exact elementaryGroup_le_map_iSup_three hirr

theorem minusDatum_isCTGroupDatum_three (h2 : (2 : F) ≠ 0) :
    IsCTGroupDatum (coxeterMatrix (minusDatum 3 hirr).isFiniteType).toCoxeterSystem
      (weylAction (minusDatum 3 hirr).isFiniteType) (minusDatum 3 hirr).roots
      (minusDatum 3 hirr).rootGroup (minusWeyl 3 hirr) (minusTorus 3 hirr) where
  n_mem := minusDatum_n_mem 3 hirr
  conj_mem := minusDatum_conj_mem 3 hirr
  braid := minusDatum_braid 3 hirr
  H_le := minusDatum_H_le 3 hirr
  sq_mem := minusDatum_sq_mem 3 hirr
  H_conj_mem := minusDatum_H_conj_mem 3 hirr
  conj_H_mem := minusDatum_conj_H_mem 3 hirr
  le_rankOne := minusDatum_le_rankOne 3 hirr
  iSup_eq_top := minusDatum_iSup_eq_top_three hirr h2

theorem iSup_rankOne_minusDatum_three (h2 : (2 : F) ≠ 0) :
    ⨆ k : Fin (minusDatum 3 hirr).rank, rankOne (minusDatum 3 hirr).rootGroup k = ⊤ :=
  iSup_rankOne_eq_top_of_ct (D := minusDatum 3 hirr) (minusDatum_isCTGroupDatum_three hirr h2) rfl

theorem spinMinus6_blocks_sup_eq_top (h2 : (2 : F) ≠ 0) :
    haveI := fact_shortField hirr
    (minusLongBlock b c).range ⊔ (shortBlock hirr 3 finOne).range = ⊤ := by
  have := fact_shortField hirr
  rw [eq_top_iff, ← iSup_rankOne_minusDatum_three hirr h2]
  refine iSup_le fun k => ?_
  obtain ⟨k, hk⟩ := k
  have hk2 : k = 0 ∨ k = 1 := by
    change k < 3 - 1 at hk
    omega
  rcases hk2 with rfl | rfl
  · have hk0 : (0 : ℕ) + 1 < 3 - 1 := by norm_num
    exact (rankOne_minusDatum_long hirr (n := 3) (k := ⟨0, hk⟩) hk0).le.trans le_sup_left
  · have hk1 : ¬ (1 : ℕ) + 1 < 3 - 1 := by norm_num
    exact (rankOne_minusDatum_short hirr (n := 3) (k := ⟨1, hk⟩) hk1).le.trans le_sup_right

theorem spinMinusModel_blocks_sup_eq_top (h2 : (2 : F) ≠ 0) :
    haveI := fact_shortField hirr
    (spinMinusModel hirr).lb.range ⊔ (spinMinusModel hirr).sb.range = ⊤ :=
  spinMinus6_blocks_sup_eq_top hirr h2

end Datum

end CFSG.ClassicalInvolution.WeakCT
