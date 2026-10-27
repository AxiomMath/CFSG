module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClSpSplit
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpThree
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33OCSpHom

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.ClSp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff
  lam coe_lam pairMat pairMat_mul pairMat_one sl2Diag coe_sl2Diag)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (invSMulOp)
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.Sp
open scoped commutatorElement MatrixGroups

variable {r : ℕ} {K : Type} [Field K] [Finite K] {i : MulAut (StatedProj (StatedSp r K))}
  {R : Subgroup (MulAut (StatedProj (StatedSp r K)))}

omit [Finite K] in
theorem mem_closure_fix [Finite K] (hK : ringChar K ≠ 2) (θ : SL(2, K) →* StatedProj (StatedSp r K))
    (hθ : ∀ e, i (θ e) = θ e) (X : SL(2, K)) :
    θ X ∈ closure {s | i s = s ∧ Odd (orderOf s)} := by
  obtain ⟨hS, hSo⟩ := HarrisLit.L33.OC.elementary_closure_odd hK 2 (K := K)
  have hX : X ∈ closure (LinearGroups.elementarySet 2 K) := by rw [hS]; exact mem_top X
  have hle : (closure (LinearGroups.elementarySet 2 K)).map θ ≤
      closure {s | i s = s ∧ Odd (orderOf s)} := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨e, he, rfl⟩
    exact subset_closure ⟨hθ e, Odd.of_dvd_nat (hSo e he) (orderOf_map_dvd θ e)⟩
  exact hle ⟨X, hX, rfl⟩

omit [Finite K] in
theorem exists_odd_pow_commutator_fix
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    (hRodd : Odd (Nat.card R))
    (hRc : ∀ s, i s = s → Odd (orderOf s) → ∀ y ∈ R,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R) {D : gsp r K} (hy : conjAut r K D ∈ R)
    {g : StatedSp r K} (hg : proj r K g ∈ closure {s | i s = s ∧ Odd (orderOf s)}) :
    ∃ k, Odd k ∧
      (conjSp r K D g * g⁻¹) ^ k ∈ (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K) := by
  have hodd := odd_orderOf_of_mem hRodd (commutator_mem hRc hg hy)
  change Odd (orderOf (conjAut r K D * conjProjH (StatedSp r K) g * (conjAut r K D)⁻¹ *
    (conjProjH (StatedSp r K) g)⁻¹)) at hodd
  refine ⟨_, hodd, ?_⟩
  have e : conjAut r K D * conjProjH (StatedSp r K) g * (conjAut r K D)⁻¹ *
      (conjProjH (StatedSp r K) g)⁻¹ = conjProjH (StatedSp r K) (conjSp r K D g * g⁻¹) := by
    rw [conjAut_mul_conjProjH, map_mul, map_inv]
  rw [e] at hodd ⊢
  have h1 : conjProjH (StatedSp r K) ((conjSp r K D g * g⁻¹) ^
      orderOf (conjProjH (StatedSp r K) (conjSp r K D g * g⁻¹))) = 1 := by
    rw [map_pow, pow_orderOf_eq_one]
  exact (QuotientGroup.eq_one_iff _).1 (hinj (by rw [map_one]; exact h1))

theorem lrPair_scalar_three_fix (h3 : Nat.card K = 3) (hr : 2 ≤ r)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    (hRodd : Odd (Nat.card R))
    (hRc : ∀ s, i s = s → Odd (orderOf s) → ∀ y ∈ R,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R) {D : gsp r K} (hy : conjAut r K D ∈ R)
    (j : Fin r)
    (hD : BlockDiag (lrPair j)
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    (ht : ∀ X : SL(2, K), proj r K (lam j X) ∈ closure {s | i s = s ∧ Odd (orderOf s)}) :
    ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
        (Sum.inl j) (Sum.inr j) = 0 ∧
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
        (Sum.inr j) (Sum.inl j) = 0 ∧
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
        (Sum.inl j) (Sum.inl j) =
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
        (Sum.inr j) (Sum.inr j) := by
  obtain ⟨j', hj'⟩ := exists_ne_index hr j
  have hx : (Sum.inl j' : Fin r ⊕ Fin r) ∉ lrPair j := by simp [hj']
  set M := ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  set Mi := (((D : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hMi
  have hMMi : M * Mi = 1 := by rw [hM, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMiM : Mi * M = 1 := by rw [hM, hMi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine three_pair_scalar h3 Sum.inl_ne_inr hMMi hMiM hD fun X Xi hX hXXi => ?_
  obtain ⟨x, hxX⟩ : ∃ x : SL(2, K), (x : Matrix (Fin 2) (Fin 2) K) = X := ⟨⟨X, hX⟩, rfl⟩
  have hxi : ((x⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = Xi := by
    have h1 : X * ((x⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← hxX, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have h2 : Xi * X = 1 := by
      have : X⁻¹ = Xi := Matrix.inv_eq_right_inv hXXi
      rw [← this, Matrix.nonsing_inv_mul _ (by rw [hX]; exact isUnit_one)]
    calc ((x⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
        (Xi * X) * ((x⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := by rw [h2, Matrix.one_mul]
      _ = Xi := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  obtain ⟨k, hk, hz⟩ := exists_odd_pow_commutator_fix hinj hRodd hRc hy (ht x)
  refine ⟨k, hk, ?_⟩
  obtain ⟨c, hc⟩ := hz
  have hmat : (((conjSp r K D (lam j x) * (lam j x)⁻¹) ^ k : StatedSp r K) :
      GL (Fin r ⊕ Fin r) K).val = (M * pairMat (Sum.inl j) (Sum.inr j) X * Mi *
        pairMat (Sum.inl j) (Sum.inr j) Xi) ^ k := by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_mul, Units.val_mul, coe_conjSp,
      Units.val_mul, Units.val_mul, coe_lam, ← map_inv, coe_lam, hxX, hxi]
  have hS : PairSupp (lrPair j) ((M * pairMat (Sum.inl j) (Sum.inr j) X * Mi *
      pairMat (Sum.inl j) (Sum.inr j) Xi) ^ k) :=
    pairSupp_pow (pairSupp_mul (pairSupp_conj hMMi hMiM hD (pairSupp_pairMat Sum.inl_ne_inr X))
      (pairSupp_pairMat Sum.inl_ne_inr Xi)) k
  have hc' : (GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c : GL (Fin r ⊕ Fin r) K).val =
      (M * pairMat (Sum.inl j) (Sum.inr j) X * Mi * pairMat (Sum.inl j) (Sum.inr j) Xi) ^ k := by
    rw [← hmat]
    exact congrArg Units.val hc
  rw [GeneralLinearGroup.coe_scalar, scalar_apply, ← Matrix.smul_one_eq_diagonal] at hc'
  rw [← hc'] at hS ⊢
  rw [eq_one_of_scalar_pairSupp hx hS, one_smul]

theorem eq_one_lrInv_three (h3 : Nat.card K = 3) (hr : 2 ≤ r)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    (i₀ : Fin r) (hRodd : Odd (Nat.card R))
    (hRi : ∀ y ∈ R, y * conjAut r K (lrInvGsp r K i₀) = conjAut r K (lrInvGsp r K i₀) * y)
    (hRc : ∀ s, conjAut r K (lrInvGsp r K i₀) s = s → Odd (orderOf s) → ∀ y ∈ R,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R) {y} (hy : y ∈ R) : y = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hp3 : (Nat.card K).Prime := by rw [h3]; norm_num
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_three h3
  have hK : ringChar K ≠ 2 := fun h => h2 (by
    have := ringChar.spec K 2
    exact_mod_cast (this.2 (by rw [h])))
  set U := ((lrInvGsp r K i₀ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    with hU
  have hUU : U * U = ((1 : K) ^ 2) • 1 := by
    rw [one_pow, one_smul]
    change (((lrInv K i₀ * lrInv K i₀ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1
    rw [lrInv_mul_self]
    rfl
  have hUJ : Uᵀ * formJ r K * U = ((1 : K) ^ 2) • formJ r K := by
    rw [one_pow, one_smul]
    exact mem_statedSp_iff.1 (lrInv K i₀).2
  obtain ⟨j₀, hj₀⟩ := exists_ne_index hr i₀
  have hAns : ∀ c : Kˣ, (lrInvGsp r K i₀ : GL (Fin r ⊕ Fin r) K) ≠
      GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
    intro c hc
    have e1 := congrArg (fun g : GL (Fin r ⊕ Fin r) K => (g : Matrix (Fin r ⊕ Fin r)
      (Fin r ⊕ Fin r) K) (Sum.inl i₀) (Sum.inl i₀)) hc
    have e2 := congrArg (fun g : GL (Fin r ⊕ Fin r) K => (g : Matrix (Fin r ⊕ Fin r)
      (Fin r ⊕ Fin r) K) (Sum.inl j₀) (Sum.inl j₀)) hc
    simp only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq] at e1 e2
    change (((lrInv K i₀ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (Sum.inl i₀) (Sum.inl i₀) = _ at e1
    change (((lrInv K i₀ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (Sum.inl j₀) (Sum.inl j₀) = _ at e2
    rw [lrInv_apply_inl] at e1 e2
    simp only [hj₀, ↓reduceIte] at e1 e2
    exact h2 (by linear_combination e2 - e1)
  have hcent : ∀ j : Fin r, (∀ X : SL(2, K), lam j X * lrInv K i₀ = lrInv K i₀ * lam j X) →
      ∀ X : SL(2, K), proj r K (lam j X) ∈ closure {s | conjAut r K (lrInvGsp r K i₀) s = s ∧
        Odd (orderOf s)} :=
    fun j hj X => mem_closure_fix hK ((proj r K).comp (lam j)) (fun e => by
      rw [MonoidHom.comp_apply, conjAut_proj]
      congr 1
      apply statedSp_ext
      rw [coe_conjSp]
      exact congrArg Units.val (by
        rw [mul_inv_eq_iff_eq_mul]
        exact congrArg Subtype.val (hj e).symm)) X
  have hoddy := odd_orderOf_of_mem hRodd hy
  have hyt := hRi y hy
  obtain ⟨D, τ, rfl⟩ := CatalogueBSymplecticRepresentation.automorphism_standard hK hr y
  have hτ : τ = 1 := ringEquiv_eq_one_of_prime_card hp3 τ
  subst hτ
  rw [map_one, mul_one] at hy hoddy hyt ⊢
  obtain ⟨D', -, hD'D, hD'U⟩ := exists_commute_of_odd (by omega) one_ne_zero
    (by rw [← hU]; simpa using hUU) hyt hoddy
  rw [← hD'D] at hy hoddy ⊢
  set Dm := ((D' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hDm
  have hbd : BlockDiag (lrPair i₀) Dm := blockDiag_of_commute_lrInv h2 i₀ hD'U
  obtain ⟨p1, p2, p3⟩ := lrPair_scalar_three_fix h3 hr hinj hRodd hRc hy i₀ hbd
    (hcent i₀ fun X => longRoot_commute i₀ _ ⟨X, rfl⟩)
  have hMe : ∀ v ∈ VMl (lrInvGsp r K i₀) 1, ∃ μ : K, Dm *ᵥ v = μ • v := fun v hv =>
    ⟨_, mulVec_eq_of_pairBlock Sum.inl_ne_inr hbd p1 p2 p3 ((mem_VMl_lrInv h2 i₀).1 hv)⟩
  have hPe : ∀ v ∈ VPl (lrInvGsp r K i₀) 1, ∃ μ : K, Dm *ᵥ v = μ • v := by
    rcases Nat.lt_or_ge r 3 with hr3 | hr3
    ·
      have hcompl : ∀ x : Fin r ⊕ Fin r, x ∈ lrPair j₀ ↔ x ∉ lrPair i₀ := by
        have hk : ∀ k : Fin r, k = i₀ ∨ k = j₀ := by
          intro k
          by_contra h
          push Not at h
          have h1 := Fin.val_ne_of_ne h.1
          have h2' := Fin.val_ne_of_ne h.2
          have h3' := Fin.val_ne_of_ne hj₀
          have := k.2
          have := i₀.2
          have := j₀.2
          omega
        intro x
        rcases x with k | k <;> rcases hk k with rfl | rfl <;> simp [lrPair, hj₀, Ne.symm hj₀]
      have hbd' : BlockDiag (lrPair j₀) Dm := by
        rw [blockDiag_iff] at hbd ⊢
        intro x y hxy
        exact hbd x y (by rw [hcompl, hcompl] at hxy; tauto)
      obtain ⟨q1, q2, q3⟩ := lrPair_scalar_three_fix h3 hr hinj hRodd hRc hy j₀ hbd'
        (hcent j₀ fun X => lam_commute_lrInv hj₀ X)
      intro v hv
      refine ⟨_, mulVec_eq_of_pairBlock Sum.inl_ne_inr hbd' q1 q2 q3 fun x hx => ?_⟩
      exact (mem_VPl_lrInv h2 i₀).1 hv x (by rw [hcompl] at hx; tauto)
    ·
      have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
      have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
      have hJA : Uᵀ * formJ r K = formJ r K * U :=
        transpose_mul_formJ (by norm_num) hUJ hUU
      have hAA' := linA_mul_self hUU
      have hTB : ∀ v w, pairedSympForm K r (invSMulOp 1 ((linA (lrInvGsp r K i₀) :
          LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
            Module.End K (Fin r ⊕ Fin r → K)) v)
          (invSMulOp 1 ((linA (lrInvGsp r K i₀) : LinearMap.GeneralLinearGroup K
            (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) w) =
            pairedSympForm K r v w := by
        intro v w
        simp only [invSMulOp, inv_one, one_smul, linA_apply]
        rw [form_similitude hUJ, one_pow, one_mul]
      have hAns' : ∀ c : K, ((linA (lrInvGsp r K i₀) : LinearMap.GeneralLinearGroup K
          (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) ≠ c • 1 :=
        CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns
      obtain ⟨hPne, -⟩ := UnitaryHigher.eigen_ne_bot h2 one_ne_zero hAA' hAns'
      obtain ⟨horth, haltP, -, hndP, -, e, he⟩ := UnitaryHigher.exists_bilin_split_equiv h2
        pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate one_ne_zero hAA' hTB
      set Ψ := (spCentEquiv (lrInvGsp r K i₀)).trans e with hΨ
      have hres : ∀ g : spCent r K (lrInvGsp r K i₀), (Ψ g).2 = 1 ↔
          ∀ v ∈ VMl (lrInvGsp r K i₀) 1, (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
            Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v = v := by
        intro g
        change (e (spCentEquiv _ g)).2 = 1 ↔ _
        rw [← OneMemClass.coe_eq_one, glW_eq_one_iff (he (spCentEquiv _ g)).2]
        simp only [spCentEquiv_apply]
      have hc := UnitaryHigher.isCompl_ker_sub_one_ker_add_one h2
        (UnitaryHigher.invSMulOp_mul_self one_ne_zero hAA')
      have hsum : Module.finrank K (VPl (lrInvGsp r K i₀) 1) +
          Module.finrank K (VMl (lrInvGsp r K i₀) 1) = 2 * r := by
        have := Submodule.finrank_add_eq_of_isCompl hc
        rw [finrank_standard] at this
        exact this
      have hMle : Module.finrank K (VMl (lrInvGsp r K i₀) 1) ≤ 2 := by
        set b : Fin 2 → (Fin r ⊕ Fin r → K) :=
          ![Pi.single (Sum.inl i₀) 1, Pi.single (Sum.inr i₀) 1] with hb
        have hle : VMl (lrInvGsp r K i₀) 1 ≤ Submodule.span K (Set.range b) := by
          intro v hv
          have hv' := (mem_VMl_lrInv h2 i₀).1 hv
          have hvs : v = v (Sum.inl i₀) • b 0 + v (Sum.inr i₀) • b 1 := by
            ext x
            simp only [hb, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply,
              Pi.smul_apply, smul_eq_mul, Pi.single_apply]
            by_cases hxa : x = Sum.inl i₀
            · subst hxa
              simp
            · by_cases hxb : x = Sum.inr i₀
              · subst hxb
                simp
              · rw [hv' x (by simp [lrPair, hxa, hxb])]
                simp [hxa, hxb]
          rw [hvs]
          exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
            (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
        calc Module.finrank K (VMl (lrInvGsp r K i₀) 1) ≤
            Module.finrank K (Submodule.span K (Set.range b)) := Submodule.finrank_mono hle
          _ ≤ Fintype.card (Fin 2) := finrank_range_le_card b
          _ = 2 := Fintype.card_fin 2
      have hPx : Module.finrank K (VPl (lrInvGsp r K i₀) 1) ≠ 2 ∨ Nat.card K ≠ 3 := by
        left
        omega
      have hqP : IsQuasisimple (fixSub r K (lrInvGsp r K i₀) (VMl (lrInvGsp r K i₀) 1)) :=
        isQuasisimple_fixSub_of_equiv Ψ hres
          (LocalCores.isQuasisimple_of_mulEquiv
            (CatalogueBSymplecticB.sesqUnitaryIsometryEquiv _).symm
            (CatalogueBAlternatingIsometry.isometry_quasisimple _ haltP hndP
              (CatalogueBSymplecticB.two_le_finrank_of_ne_bot hPne _ haltP hndP) hodd hPx))
      have hTP : ∀ v ∈ VPl (lrInvGsp r K i₀) 1, ∀ c,
          transvSp v c ∈ fixSub r K (lrInvGsp r K i₀) (VMl (lrInvGsp r K i₀) 1) := by
        intro v hv c
        refine ⟨transvSp_mem_spCent hJA ((mem_eigenPlus one_ne_zero).1 hv) c, fun w hw => ?_⟩
        rw [coe_transvSp, add_mulVec, one_mulVec, smul_mulVec, transvN_mulVec, horth v hv w hw,
          zero_smul, smul_zero, add_zero]
      have hy' : conjAut r K D' * fieldAut r K 1 ∈ R := by
        rw [map_one, mul_one]
        exact hy
      exact (eigen_of_fix hqP hTP fun g hg => fix_of_spCent hinj hRodd hRi hRc rfl (fixSub_le _ _)
        (fun f hf q hq => conj_mem_fixSub (fun g hg v hv => mulVec_mem_VMl one_ne_zero hg hv) hf
          hq) hqP hy' hg).2
  exact splitSelf_conclude hK hr hAns one_ne_zero hUU hUJ hoddy hPe hMe

end CFSG.ComponentClassification.Foote5.OddLieCore.ClSp
