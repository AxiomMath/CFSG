module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenTwo
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcCtx
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuNHom
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenUni
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeAOne

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSGen

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
open Matrix
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false


section Frame2

variable {τ : Tag} {L : Type} [Field L]

@[expose] def rankOneSigma (β : Fin τ.rank → ℤ) : Fin 2 → Fin 2 → Fin τ.rank → ℤ :=
  ![![0, β], ![-β, 0]]

theorem frameRoots_rankOneSigma (β : Fin τ.rank → ℤ) :
    frameRoots (rankOneSigma β) = {β, -β} := by
  ext r
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    fin_cases i <;> fin_cases j <;> simp_all [rankOneSigma]
  · rintro (rfl | rfl)
    · exact ⟨0, 1, by decide, by simp [rankOneSigma]⟩
    · exact ⟨1, 0, by decide, by simp [rankOneSigma]⟩

theorem transvection_zero_one_eq_uSL (t : L) :
    Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) t = uSL t := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.transvection_coe, coe_uSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]

theorem transvection_one_zero_eq_vSL (t : L) :
    Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) t = vSL t := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply, vSL]

theorem isSLFrame_rootSL2 {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    IsSLFrame (rootSL2 τ L β) (rankOneSigma β) where
  isRoot i j hij := by
    fin_cases i <;> fin_cases j <;> simp_all [rankOneSigma]
    · exact IsRoot.neg hβ
  neg i j := by
    fin_cases i <;> fin_cases j <;> simp [rankOneSigma]
  add i j k := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [rankOneSigma]
  transv i j hij := by
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · rcases pinnedSign_eq τ β with h | h
      · refine ⟨1, fun t => ?_⟩
        rw [transvection_zero_one_eq_uSL, rootSL2_uSL_eq, h]
        simp [rankOneSigma]
      · refine ⟨-1, fun t => ?_⟩
        rw [transvection_zero_one_eq_uSL, rootSL2_uSL_eq, h]
        simp [rankOneSigma]
    · obtain ⟨ε, hε, h⟩ := exists_rootSL2_vSL_eq (K := L) hβ
      refine ⟨Units.mkOfMulEqOne ε ε hε, fun t => ?_⟩
      rw [transvection_one_zero_eq_vSL, h]
      simp [rankOneSigma]
    · exact absurd rfl hij
  range := by
    rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hβ, frameRoots_rankOneSigma]
    simp only [rootSpan, iSup_insert, iSup_singleton]

end Frame2

section Split

variable {L : Type} [Field L] {ν : ℕ}

@[expose] def conjAround (W : GL (Fin ν) L) (φ : SL(ν, L) →* SL(ν, L)) : SL(ν, L) →* SL(ν, L) :=
  (conjSLn W).comp (φ.comp (conjSLn W⁻¹))

theorem conjAround_conjSLn (W : GL (Fin ν) L) (φ : SL(ν, L) →* SL(ν, L)) (X : SL(ν, L)) :
    conjAround W φ (conjSLn W X) = conjSLn W (φ X) := by
  simp only [conjAround, MonoidHom.comp_apply]
  rw [← conjSLn_mul_apply, inv_mul_cancel, conjSLn_one_apply]

theorem coe_conjAround_map (W : GL (Fin ν) L) (σ : L →+* L) (X : SL(ν, L)) :
    ((conjAround W (Matrix.SpecialLinearGroup.map σ) X : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
      ((W : Matrix (Fin ν) (Fin ν) L) * (↑W⁻¹ : Matrix (Fin ν) (Fin ν) L).map σ) *
        (X : Matrix (Fin ν) (Fin ν) L).map σ *
          ((W : Matrix (Fin ν) (Fin ν) L).map σ * (↑W⁻¹ : Matrix (Fin ν) (Fin ν) L)) := by
  simp only [conjAround, MonoidHom.comp_apply]
  rw [coe_conjSLn, Matrix.SpecialLinearGroup.map_apply_coe, coe_conjSLn, inv_inv,
    RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem conjAround_mul_inv (W : GL (Fin ν) L) (σ : L →+* L) :
    ((W : Matrix (Fin ν) (Fin ν) L) * (↑W⁻¹ : Matrix (Fin ν) (Fin ν) L).map σ) *
      ((W : Matrix (Fin ν) (Fin ν) L).map σ * (↑W⁻¹ : Matrix (Fin ν) (Fin ν) L)) = 1 := by
  have h1 : (↑W⁻¹ : Matrix (Fin ν) (Fin ν) L).map σ * (W : Matrix (Fin ν) (Fin ν) L).map σ = 1 := by
    rw [← Matrix.map_mul, W.inv_mul, Matrix.map_one _ (map_zero σ) (map_one σ)]
  calc ((W : Matrix (Fin ν) (Fin ν) L) * (↑W⁻¹ : Matrix (Fin ν) (Fin ν) L).map σ) *
        ((W : Matrix (Fin ν) (Fin ν) L).map σ * (↑W⁻¹ : Matrix (Fin ν) (Fin ν) L)) =
      (W : Matrix (Fin ν) (Fin ν) L) * ((↑W⁻¹ : Matrix (Fin ν) (Fin ν) L).map σ *
        (W : Matrix (Fin ν) (Fin ν) L).map σ) * (↑W⁻¹ : Matrix (Fin ν) (Fin ν) L) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_one]; exact W.mul_inv

theorem conjAround_inv_mul (W : GL (Fin ν) L) (σ : L →+* L) :
    ((W : Matrix (Fin ν) (Fin ν) L).map σ * (↑W⁻¹ : Matrix (Fin ν) (Fin ν) L)) *
      ((W : Matrix (Fin ν) (Fin ν) L) * (↑W⁻¹ : Matrix (Fin ν) (Fin ν) L).map σ) = 1 := by
  have h1 : (W : Matrix (Fin ν) (Fin ν) L).map σ * (↑W⁻¹ : Matrix (Fin ν) (Fin ν) L).map σ = 1 := by
    rw [← Matrix.map_mul, W.mul_inv, Matrix.map_one _ (map_zero σ) (map_one σ)]
  calc ((W : Matrix (Fin ν) (Fin ν) L).map σ * (↑W⁻¹ : Matrix (Fin ν) (Fin ν) L)) *
        ((W : Matrix (Fin ν) (Fin ν) L) * (↑W⁻¹ : Matrix (Fin ν) (Fin ν) L).map σ) =
      (W : Matrix (Fin ν) (Fin ν) L).map σ * ((↑W⁻¹ : Matrix (Fin ν) (Fin ν) L) *
        (W : Matrix (Fin ν) (Fin ν) L)) * (↑W⁻¹ : Matrix (Fin ν) (Fin ν) L).map σ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [W.inv_mul, Matrix.mul_one]; exact h1

theorem lang_diagSL_split [IsAlgClosed L] [NeZero ν] {Q : ℕ} (hQ : 2 ≤ Q) (σ : L →+* L)
    (hσ : ∀ c, σ c = c ^ Q) {C C' : Matrix (Fin ν) (Fin ν) L} {F' : SL(ν, L) →* SL(ν, L)}
    (hF' : ∀ X : SL(ν, L), (F' X : Matrix (Fin ν) (Fin ν) L) =
      C * (X : Matrix (Fin ν) (Fin ν) L).map σ * C') {ρ : Equiv.Perm (Fin ν)}
    (hρ : ∀ v : Fin ν → L, C * Matrix.diagonal v * C' = Matrix.diagonal (fun k => v (ρ k))) :
    ∀ δ ∈ diagSL ν L, ∃ δ' ∈ diagSL ν L, F' δ' * δ'⁻¹ = δ := by
  intro δ hδ
  obtain ⟨w, hw, rfl⟩ := exists_units_of_mem_diagSL hδ
  haveI : Nonempty (Fin ν) := ⟨0⟩
  have hw' : ∏ i, w i = 1 := hw
  obtain ⟨y, hy, hyw⟩ := exists_lang_monomial ρ (e := -(Q : ℤ)) (by simpa using hQ) w hw'
  set x : Fin ν → Lˣ := fun k => (y k)⁻¹ with hxdef
  have hx : ∏ i, x i = 1 := by rw [hxdef, Finset.prod_inv_distrib, hy, inv_one]
  refine ⟨diagSLOf x hx, diagSLOf_mem _ _, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [hF', Matrix.SpecialLinearGroup.coe_mul, coe_diagSLOf, coe_diagSLOf]
  have h1 : (Matrix.diagonal (fun k => (x k : L))).map σ =
      Matrix.diagonal (fun k => σ (x k : L)) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · simp [Matrix.diagonal_apply_ne _ hab]
  rw [h1, hρ, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  have h2 := hyw k
  have h3 : (y k : L) * (y (ρ k) : L) ^ (-(Q : ℤ)) = (w k : L) := by
    have := congrArg (fun u : Lˣ => (u : L)) h2
    simpa using this
  rw [hσ]
  have hyk : (y k : L) ≠ 0 := Units.ne_zero _
  have hyρ : (y (ρ k) : L) ≠ 0 := Units.ne_zero _
  simp only [hxdef, Units.val_inv_eq_inv_val, inv_pow]
  rw [_root_.zpow_neg, zpow_natCast] at h3
  field_simp at h3 ⊢
  linear_combination h3

section Fixed

variable {L : Type} [Field L]

theorem commutator_fix_map_two {σ : L ≃+* L} (hfin : Finite (fixSubfield σ))
    (h4 : 4 ≤ Nat.card (fixSubfield σ)) :
    ⁅(Matrix.SpecialLinearGroup.map σ.toRingHom : SL(2, L) →* SL(2, L)).eqLocus (MonoidHom.id _),
      (Matrix.SpecialLinearGroup.map σ.toRingHom : SL(2, L) →* SL(2, L)).eqLocus
        (MonoidHom.id _)⁆ =
      (Matrix.SpecialLinearGroup.map σ.toRingHom : SL(2, L) →* SL(2, L)).eqLocus
        (MonoidHom.id _) := by
  classical
  haveI := Fintype.ofFinite (fixSubfield σ)
  have h4' : ∃ s : Finset (fixSubfield σ), s.card = 4 := by
    have hle : 4 ≤ (Finset.univ : Finset (fixSubfield σ)).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact h4
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq hle
    exact ⟨t, ht⟩
  haveI hperf : Group.IsPerfect SL(2, fixSubfield σ) :=
    CFSG.LinearGroups.special_linear_isPerfect le_rfl (Or.inr h4')
  let ι : SL(2, fixSubfield σ) →* SL(2, L) :=
    Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype
  have hrange : ι.range = (Matrix.SpecialLinearGroup.map σ.toRingHom : SL(2, L) →* SL(2, L)).eqLocus
      (MonoidHom.id _) := by
    ext X
    constructor
    · rintro ⟨Y, rfl⟩
      apply Subtype.ext
      ext i j
      simp only [ι, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply, MonoidHom.id_apply]
      exact (Y i j).2
    · intro hX
      have hent : ∀ i j, σ ((X : Matrix (Fin 2) (Fin 2) L) i j) =
          (X : Matrix (Fin 2) (Fin 2) L) i j := by
        intro i j
        have := congrArg (fun A : SL(2, L) => (A : Matrix (Fin 2) (Fin 2) L) i j) hX
        simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] using this
      obtain ⟨Y, hY⟩ := exists_map_eq_of_forall_mem_range (ψ := (fixSubfield σ).subtype)
        (Subfield.subtype_injective _) X (fun i j => ⟨⟨_, hent i j⟩, rfl⟩)
      exact ⟨Y, hY⟩
  rw [← hrange]
  exact Subgroup.isPerfect_iff.1 (Group.IsPerfect.range ι)

end Fixed

end Split

section RankOne


variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup Tag.E6 L p)
  {ta : Fin Tag.E6.rank → Lˣ}

theorem rankOne_class_peel (h3 : ((3 : ℕ) : L) ≠ 0) (hT : rootDiagUnit Tag.E6 ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta))
    (h1 : compRank (componentRoots (rootCharHom ta) i) = 1)
    (hn : (componentRoots (rootCharHom ta) i).ncard = 2)
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) = 1)
    {r e : ℕ} (hr : r.Prime) (hchar : CharP L r) (he : 0 < e) (hq : S.D.q = r ^ e)
    (hq4 : 4 ≤ r ^ e) {Q' : Subgroup (ModGL Tag.E6 L)}
    (hFQ' : ∀ q ∈ Q', S.D.step q ∈ Q')
    (hHQ' : torusGroup Tag.E6 L ≤ Subgroup.normalizer (Q' : Set (ModGL Tag.E6 L)))
    (hQQ' : ∀ u ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom ta) i), ∀ b ∈ Q', u * b = b * u)
    {x : ModGL Tag.E6 L}
    (hx : x ∈ torusGroup Tag.E6 L ⊔ (rootSpan Tag.E6 L (componentRoots (rootCharHom ta) i) ⊔ Q'))
    (hFx : S.D.step x = x) :
    ∃ r' ∈ rationalComponent S.ρ S.Γ (rootCharHom ta) i, ∃ x' ∈ torusGroup Tag.E6 L ⊔ Q',
      S.D.step x' = x' ∧ x = r' * x' := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  obtain ⟨β, hβ, hΨ⟩ := exists_pair_of_rank_one i hn
  have hψ := isSLFrame_rootSL2 (L := L) hβ
  set ψ : SL(2, L) →* ModGL Tag.E6 L := rootSL2 Tag.E6 L β with hψdef
  have hΨ' : componentRoots (rootCharHom ta) i = frameRoots (rankOneSigma β) := by
    rw [hΨ, frameRoots_rankOneSigma]
  have hrange : ψ.range = rootSpan Tag.E6 L (componentRoots (rootCharHom ta) i) := by
    rw [hψ.range, ← hΨ']
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  have hstab : ∀ γ ∈ componentRoots (rootCharHom ta) i,
      S.ρ γ ∈ componentRoots (rootCharHom ta) i := by
    intro γ hγ
    rw [hs1] at hs
    have : S.ρ γ ∈ (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[1] '' componentRoots (rootCharHom ta) i :=
      ⟨γ, hγ, rfl⟩
    rwa [hs] at this
  have hinner : twistInner (componentRoots (rootCharHom ta) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[1]) := by
    rw [← hs1]
    have hkind : twistKind S.ρ (rootCharHom ta) i = .inner := by
      by_cases hin : twistInner (componentRoots (rootCharHom ta) i)
          ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom ta) i)])
      · unfold twistKind
        rw [if_pos hin]
      · unfold twistKind
        rw [if_neg hin, if_neg (by rintro (⟨h, _⟩ | ⟨h, _⟩) <;> omega),
          if_neg (fun h => by omega), if_neg (fun h => by omega)]
    exact twistInner_of_twistKind_eq_innerT S rootAutIsWeyl_holds hT i hkind
  obtain ⟨σ, z, hσ, hzmem, -, hz⟩ := exists_untwistT_Z S hT i (s := 1) one_pos hinner
  have hσc : ∀ c, σ c = c ^ S.D.q := fun c => by rw [hσ, pow_one]
  have hz' : ∀ g ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom ta) i),
      S.D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹ := fun g hg => by
    have := hz g hg
    simpa [iterHom_eq_iterate] using this
  obtain ⟨W, hW⟩ := mem_actsOn.1 (torusSup_le_actsOn hψ (by norm_num : 0 < 2) i hΨ' hzmem)
  set φ : SL(2, L) →* SL(2, L) := Matrix.SpecialLinearGroup.map σ.toRingHom with hφ
  set F' : SL(2, L) →* SL(2, L) := conjAround W φ with hF'
  have hψS : ∀ X, ψ X ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom ta) i) := fun X => by
    rw [← hrange]
    exact ⟨X, rfl⟩
  have hψA : ∀ X, ψ X ∈ adjointGroup Tag.E6 L := fun X => hψ.range_le_adjointGroup ⟨X, rfl⟩
  have hψF : ∀ X, S.D.step (ψ X) = ψ (F' X) := by
    intro X
    have hX : ψ X = z * ψ (conjSLn W⁻¹ X) * z⁻¹ := by
      rw [hW, ← conjSLn_mul_apply, mul_inv_cancel, conjSLn_one_apply]
    calc S.D.step (ψ X) = S.D.step (z * ψ (conjSLn W⁻¹ X) * z⁻¹) := by rw [← hX]
      _ = z * frobGL σ (ψ (conjSLn W⁻¹ X)) * z⁻¹ := hz' _ (hψS _)
      _ = z * ψ (φ (conjSLn W⁻¹ X)) * z⁻¹ := by rw [hψdef, frobGL_rootSL2 σ hβ]
      _ = ψ (conjSLn W (φ (conjSLn W⁻¹ X))) := hW _
      _ = ψ (F' X) := rfl
  have hinj : Function.Injective ψ := CFSG.RankThree.Chevalley.rootSL2_injective_of_field β
  have hker : ψ.ker ≤ Subgroup.center SL(2, L) := by
    rw [(MonoidHom.ker_eq_bot_iff ψ).2 hinj]
    exact bot_le
  have hψD : ∀ δ ∈ diagSL 2 L, ψ δ ∈ torusGroup Tag.E6 L := fun δ hδ =>
    frame_diag_mem_torusGroup h3 (by norm_num) hψ hδ
  have hFD : ∀ δ ∈ diagSL 2 L, F' δ ∈ diagSL 2 L := fun δ hδ =>
    frame_hc2 hker (fun δ' hδ' => by
      rw [← hψF]
      exact torusGroup_comm (step_mem_torusGroup S hq (hψD δ hδ)) (hψD δ' hδ'))
  set Cm : Matrix (Fin 2) (Fin 2) L :=
    (W : Matrix (Fin 2) (Fin 2) L) * (↑W⁻¹ : Matrix (Fin 2) (Fin 2) L).map σ with hCm
  set Cm' : Matrix (Fin 2) (Fin 2) L :=
    (W : Matrix (Fin 2) (Fin 2) L).map σ * (↑W⁻¹ : Matrix (Fin 2) (Fin 2) L) with hCm'
  have hF'mat : ∀ X : SL(2, L), (F' X : Matrix (Fin 2) (Fin 2) L) =
      Cm * (X : Matrix (Fin 2) (Fin 2) L).map σ * Cm' := fun X =>
    coe_conjAround_map W σ.toRingHom X
  have hCC : Cm * Cm' = 1 := conjAround_mul_inv W σ.toRingHom
  have hCC' : Cm' * Cm = 1 := conjAround_inv_mul W σ.toRingHom
  have hq2 : 2 ≤ S.D.q := S.hqpow.1.one_lt
  obtain ⟨s, hs2⟩ := exists_unit_pow_ne_one (L := L) (n := 2 * S.D.q) (by omega)
  have hprod : ∏ k, (![s, s⁻¹] : Fin 2 → Lˣ) k = 1 := by simp [Fin.prod_univ_two]
  have hFδ₀ := hFD (diagSLOf ![s, s⁻¹] hprod) (diagSLOf_mem _ _)
  have hmat : Cm * Matrix.diagonal ![σ (s : L), (σ (s : L))⁻¹] * Cm' =
      ((F' (diagSLOf ![s, s⁻¹] hprod) : SL(2, L)) : Matrix (Fin 2) (Fin 2) L) := by
    rw [hF'mat, coe_diagSLOf]
    congr 2
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.diagonal_apply]
  have hσs : (σ (s : L)) ≠ (σ (s : L))⁻¹ := by
    intro h
    apply hs2
    apply Units.ext
    have h0 : (σ (s : L)) ≠ 0 := (map_ne_zero σ).2 (Units.ne_zero s)
    have h2 : (σ (s : L)) ^ 2 = 1 := by
      field_simp at h
      linear_combination h
    rw [hσc, ← pow_mul, mul_comm] at h2
    simpa [pow_mul] using h2
  obtain ⟨ρ, hρ⟩ := exists_perm_conj_diag_two hCC hCC' ((map_ne_zero σ).2 (Units.ne_zero s)) hσs
    (by rw [hmat]; exact hFδ₀ 0 1 (by decide)) (by rw [hmat]; exact hFδ₀ 1 0 (by decide))
  haveI : NeZero 2 := ⟨by norm_num⟩
  have hLang := lang_diagSL_split hq2 σ.toRingHom (fun c => hσc c) hF'mat hρ
  obtain ⟨y, hy, x', hx'mem, hFx', hxeq⟩ := exists_peel_frame S.D.step F' ψ hψF
    (D := diagSL 2 L) (fun a ha b hb => torusGroup_comm ha hb)
    (fun t ht => step_mem_torusGroup S hq ht) hFQ'
    (by
      rw [hrange]
      exact CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan
        (fun γ hγ => isRoot_of_mem_componentRoots hγ))
    hHQ' (by rw [hrange]; exact hQQ') hLang hψD
    (fun κ hκ => by
      have := hinj (hκ.trans (map_one ψ).symm)
      rw [this]
      exact one_mem _)
    (fun κ hκ y => by
      have := hinj (hκ.trans (map_one ψ).symm)
      rw [this]
      simp)
    (fun y hy => frame_hc2 hker hy) (by rw [hrange]; exact hx) hFx
  refine ⟨ψ y, ?_, x', hx'mem, hFx', hxeq⟩
  have hσ' : ∀ c, σ c = c ^ (r ^ e) := fun c => by rw [hσc, hq]
  obtain ⟨hfin, hcard⟩ := finite_card_fixSubfield he σ hσ'
  have hCperf := commutator_fix_map_two (σ := σ) hfin (by rw [hcard]; exact hq4)
  have hWφ : ∀ X, F' (conjSLn W X) = conjSLn W (φ X) := conjAround_conjSLn W φ
  have hKperf := commutator_fix_of_conj (K := F'.eqLocus (MonoidHom.id _)) W hWφ
    (C := φ.eqLocus (MonoidHom.id _)) (fun X => Iff.rfl) (fun Y => Iff.rfl) hCperf
  exact map_fix_le_rationalComponent S i hstab ψ hψS hψA F' hψF (F'.eqLocus (MonoidHom.id _))
    (fun y hy => hy) hKperf y hy

theorem rankOne_class_quasisimple (hT : rootDiagUnit Tag.E6 ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta))
    (h1 : compRank (componentRoots (rootCharHom ta) i) = 1)
    (hn : (componentRoots (rootCharHom ta) i).ncard = 2)
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) = 1)
    {r e : ℕ} (hr : r.Prime) (hchar : CharP L r) (he : 0 < e) (hq : S.D.q = r ^ e)
    (hq4 : 4 ≤ r ^ e) :
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨β, hβ, hΨ⟩ := exists_pair_of_rank_one i hn
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  have : NeZero s := ⟨hs0.ne'⟩
  have hinner : twistInner (componentRoots (rootCharHom ta) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s]) := by
    have hkind : twistKind S.ρ (rootCharHom ta) i = .inner := by
      by_cases hin : twistInner (componentRoots (rootCharHom ta) i)
          ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom ta) i)])
      · unfold twistKind
        rw [if_pos hin]
      · unfold twistKind
        rw [if_neg hin, if_neg (by rintro (⟨h, _⟩ | ⟨h, _⟩) <;> omega),
          if_neg (fun h => by omega), if_neg (fun h => by omega)]
    exact twistInner_of_twistKind_eq_innerT S rootAutIsWeyl_holds hT i hkind
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i hs0 hinner
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hq, ← pow_mul]
  obtain ⟨hfinK, hKcard⟩ := finite_card_fixSubfield (L := L) (r := r) (n := e * s)
    (Nat.mul_pos he hs0) σ hσ'
  have hsL : ∃ u : Lˣ, u ^ 2 ≠ 1 := by
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset L)
    have hc0 : c ≠ 0 := fun h => hc (by simp [h])
    refine ⟨Units.mk0 c hc0, fun h => hc ?_⟩
    have h2 : c ^ 2 = 1 := by simpa using congrArg (fun x : Lˣ => (x : L)) h
    have h3 : (c - 1) * (c + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · simp [sub_eq_zero.1 h]
    · simp [eq_neg_of_add_eq_zero_left h]
  obtain ⟨f, hf1, hker, hf2⟩ :=
    rationalComponent_eq_range_componentRootSpanT S hT i hs hmin σ z hnorm hz hsL
  have hC : componentRootSpan (fixSubfield σ) (rootCharHom ta) i =
      (CFSG.LieType.Chevalley.rootSL2 Tag.E6 (fixSubfield σ) β).range := by
    rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hβ]
    show rootSpan Tag.E6 (fixSubfield σ) (componentRoots (rootCharHom ta) i) = _
    rw [hΨ]
    simp only [rootSpan, iSup_insert, iSup_singleton]
  let eSL : SL(2, ↥(fixSubfield σ)) ≃*
      ↥(componentRootSpan (fixSubfield σ) (rootCharHom ta) i) :=
    (MonoidHom.ofInjective (CFSG.RankThree.Chevalley.rootSL2_injective_of_field
      (K := ↥(fixSubfield σ)) β)).trans (MulEquiv.subgroupCongr hC.symm)
  have hker' := ker_comp_mulEquiv_le_center eSL f hker
  have hQ4 : 4 ≤ r ^ (e * s) := by rw [hs1, Nat.mul_one]; exact hq4
  obtain ⟨t, ht⟩ := exists_unit_sq_ne_one (L := L) σ hσ' (Nat.mul_pos he hs0) hQ4
  have hperfC := isPerfect_componentRootSpan_of_sq_ne_one (K := fixSubfield σ)
    (χ := rootCharHom ta) ht i
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i :=
    le_antisymm (hf2 (Subgroup.isPerfect_iff.1 hperfC)) hf1
  have hf₀ : (f.comp eSL.toMonoidHom).range = rationalComponent S.ρ S.Γ (rootCharHom ta) i := by
    rw [← hRf]
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨eSL c, rfl⟩
    · rintro ⟨c, rfl⟩
      obtain ⟨c', rfl⟩ := eSL.surjective c
      exact ⟨c', rfl⟩
  haveI := Fintype.ofFinite (fixSubfield σ)
  have h4 : ∃ u : Finset (fixSubfield σ), u.card = 4 := by
    have hle : 4 ≤ (Finset.univ : Finset (fixSubfield σ)).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hKcard]
      exact hQ4
    obtain ⟨u, -, hu⟩ := Finset.exists_subset_card_eq hle
    exact ⟨u, hu⟩
  rw [← hf₀]
  exact CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_range_of_ker_le_center
    (CFSG.RankThree.Classical.isQuasisimple_SL2 h4) _ hker'

end RankOne

end KSGen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
