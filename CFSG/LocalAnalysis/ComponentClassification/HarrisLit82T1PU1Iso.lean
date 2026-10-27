module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1POddOut
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBOFrame
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Basic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU1Grp
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RO

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
open scoped MatrixGroups commutatorElement Matrix

section Similitude

theorem det_sq_eq_pow_card_of_similitude {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*}
    [Field K] (Q : QuadraticForm K (ι → K)) (hnd : (polarBilin Q).Nondegenerate)
    (g : Matrix ι ι K) (μ : K) (hg : ∀ v, Q (g *ᵥ v) = μ * Q v) :
    g.det ^ 2 = μ ^ Fintype.card ι := by
  obtain ⟨J, hpol, -, hJ⟩ := CFSG.RankThree.PartOne.AUTSL.exists_polar_matrix Q hnd
  have h := congrArg Matrix.det (gram_of_similitude Q J hpol g μ hg)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul] at h
  have hJ0 : J.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det J).1 hJ).ne_zero
  apply mul_right_cancel₀ hJ0
  linear_combination h

variable {K : Type} [Field K]

theorem exists_isometry_involution (h2 : (2 : K) ≠ 0)
    {F : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃+ (Fin 3 ⊕ Fin 3 ⊕ Unit → K)}
    (hF : ∀ (c : K) v, F (c • v) = c • F v) {μ : K}
    (hQF : ∀ v, quadOdd 3 K (F v) = μ * quadOdd 3 K v) {c : K} (hc : c ≠ 0)
    (hFF : ∀ v, F (F v) = c • v) :
    ∃ (T : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) (l : K), l ≠ 0 ∧
      T ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) ∧ (∀ v, T (T v) = v) ∧
        ∀ v, F v = l • T v := by
  classical
  set Fl : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K) := F.toLinearEquiv hF
    with hFl
  have hFlv : ∀ v, Fl v = F v := fun v => rfl
  have hcard : Fintype.card (Fin 3 ⊕ Fin 3 ⊕ Unit) = 7 := by simp
  have hfin : Module.finrank K (Fin 3 ⊕ Fin 3 ⊕ Unit → K) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card, hcard]
  set M := LinearMap.toMatrix'
    (Fl : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) →ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) with hM
  have hMv : ∀ v, M *ᵥ v = F v := fun v => by
    rw [hM, LinearMap.toMatrix'_mulVec]
    rfl
  have h7 : M.det ^ 2 = μ ^ 7 := by
    rw [← hcard]
    exact det_sq_eq_pow_card_of_similitude _ (nondegenerate_polarBilin_quadOdd 3 K h2) M μ
      fun v => by rw [hMv]; exact hQF v
  have hc7 : M.det ^ 2 = c ^ 7 := by
    have hcomp : (Fl : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) →ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) ∘ₗ
        (Fl : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) →ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) =
          c • LinearMap.id := LinearMap.ext fun v => by
      show Fl (Fl v) = (c • LinearMap.id) v
      rw [hFlv, hFlv, hFF]
      rfl
    have := congrArg LinearMap.det hcomp
    rw [LinearMap.det_comp, LinearMap.det_smul, LinearMap.det_id, mul_one, hfin] at this
    rw [hM, LinearMap.det_toMatrix', pow_two]
    exact this
  have hμc2 : μ ^ 2 = c ^ 2 := by
    have h1 := hQF (F (oddZ 3 K))
    rw [hFF, hQF, QuadraticMap.map_smul, quadOdd_oddZ, smul_eq_mul] at h1
    linear_combination -h1
  have hμc : μ = c := by
    have h77 : μ ^ 7 = c ^ 7 := h7.symm.trans hc7
    have h6 : μ * c ^ 6 = c * c ^ 6 := by
      linear_combination (-μ * (c ^ 4 + c ^ 2 * μ ^ 2 + μ ^ 4)) * hμc2 + h77
    exact mul_right_cancel₀ (pow_ne_zero 6 hc) h6
  set l := M.det / c ^ 3 with hl
  have hl2 : l ^ 2 = c := by
    rw [hl, div_pow, hc7]
    field_simp
  have hl0 : l ≠ 0 := by
    intro h0
    rw [h0] at hl2
    exact hc (by rw [← hl2]; ring)
  refine ⟨Fl.trans (LinearEquiv.smulOfNeZero K _ l⁻¹ (inv_ne_zero hl0)), l, hl0, ?_,
    fun v => ?_, fun v => ?_⟩
  · refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
    rw [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply, QuadraticMap.map_smul, hFlv,
      hQF, hμc, ← hl2, smul_eq_mul]
    field_simp
  · rw [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply, LinearEquiv.trans_apply,
      LinearEquiv.smulOfNeZero_apply, map_smul, hFlv, hFlv, hFF, smul_smul, smul_smul, ← hl2]
    have : l⁻¹ * l⁻¹ * l ^ 2 = 1 := by field_simp
    rw [this, one_smul]
  · rw [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply, hFlv, smul_smul,
      mul_inv_cancel₀ hl0, one_smul]

end Similitude

section Split

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def negSpace (T : V ≃ₗ[K] V) : Submodule K V :=
  LinearMap.ker ((T : V →ₗ[K] V) + LinearMap.id)

@[expose] def fixSpace (T : V ≃ₗ[K] V) : Submodule K V :=
  LinearMap.ker ((T : V →ₗ[K] V) - LinearMap.id)

theorem mem_negSpace {T : V ≃ₗ[K] V} {x : V} : x ∈ negSpace T ↔ T x = -x := by
  rw [negSpace, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
    add_eq_zero_iff_eq_neg]

theorem mem_fixSpace {T : V ≃ₗ[K] V} {x : V} : x ∈ fixSpace T ↔ T x = x := by
  rw [fixSpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
    sub_eq_zero]

theorem mem_negSpace_fixSpace_decomp (h2 : (2 : K) ≠ 0) {T : V ≃ₗ[K] V} (hTT : ∀ v, T (T v) = v)
    (v : V) : (2 : K)⁻¹ • (v - T v) ∈ negSpace T ∧ (2 : K)⁻¹ • (v + T v) ∈ fixSpace T ∧
      v = (2 : K)⁻¹ • (v - T v) + (2 : K)⁻¹ • (v + T v) := by
  refine ⟨mem_negSpace.mpr ?_, mem_fixSpace.mpr ?_, ?_⟩
  · rw [map_smul, map_sub, hTT]
    module
  · rw [map_smul, map_add, hTT]
    module
  · have h2' : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
    calc v = ((2 : K)⁻¹ * 2) • v := by rw [h2', one_smul]
      _ = (2 : K)⁻¹ • (v - T v) + (2 : K)⁻¹ • (v + T v) := by module

theorem splitInv_of_involution (h2 : (2 : K) ≠ 0) (hnd : (polarBilin Q).Nondegenerate)
    {T : V ≃ₗ[K] V} (hT : T ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hTT : ∀ v, T (T v) = v) : SplitInv Q (negSpace T) (fixSpace T) T := by
  have horth : ∀ x ∈ negSpace T, ∀ y ∈ fixSpace T, polar Q x y = 0 := by
    intro x hx y hy
    have h := polar_map_of_mem hT x y
    rw [mem_negSpace.mp hx, mem_fixSpace.mp hy, polar_neg_left] at h
    have : (2 : K) * polar Q x y = 0 := by linear_combination -h
    exact (mul_eq_zero.mp this).resolve_left h2
  refine ⟨fun x hx hxS => ?_, fun x hx hxT => ?_, horth, ?_, fun x hx => mem_negSpace.mp hx,
    fun x hx => mem_fixSpace.mp hx⟩
  · apply eq_zero_of_polar_eq_zero hnd
    intro z
    obtain ⟨h1, h1', h3⟩ := mem_negSpace_fixSpace_decomp h2 hTT z
    rw [h3, polar_add_right, hxS _ h1, horth x hx _ h1', add_zero]
  · apply eq_zero_of_polar_eq_zero hnd
    intro z
    obtain ⟨h1, h1', h3⟩ := mem_negSpace_fixSpace_decomp h2 hTT z
    rw [h3, polar_add_right, polar_comm Q x, horth _ h1 x hx, hxT _ h1', zero_add]
  · refine eq_top_iff.mpr fun v _ => ?_
    obtain ⟨h1, h1', h3⟩ := mem_negSpace_fixSpace_decomp h2 hTT v
    rw [h3]
    exact Submodule.add_mem_sup h1 h1'

theorem finrank_add_finrank_of_splitInv [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    {U U' : Submodule K V} {a : V ≃ₗ[K] V} (hsp : SplitInv Q U U' a) :
    Module.finrank K U + Module.finrank K U' = Module.finrank K V := by
  refine Submodule.finrank_add_eq_of_isCompl ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    have h1 := hsp.negS x hx
    rw [hsp.fixT x hx'] at h1
    have : (2 : K) • x = 0 := by
      rw [two_smul]
      nth_rewrite 1 [h1]
      exact neg_add_cancel x
    exact (smul_eq_zero.mp this).resolve_left h2
  · rw [codisjoint_iff]
    exact hsp.top

theorem splitInv_neg {U U' : Submodule K V} {a : V ≃ₗ[K] V} (hsp : SplitInv Q U U' a) :
    SplitInv Q U' U (a.trans (LinearEquiv.neg K)) := by
  refine ⟨hsp.ndT, hsp.ndS, fun x hx y hy => ?_, by rw [sup_comm]; exact hsp.top,
    fun x hx => ?_, fun x hx => ?_⟩
  · rw [polar_comm]
    exact hsp.orth y hy x hx
  · rw [LinearEquiv.trans_apply, LinearEquiv.neg_apply, hsp.fixT x hx]
  · rw [LinearEquiv.trans_apply, LinearEquiv.neg_apply, hsp.negS x hx, neg_neg]

theorem exists_anisotropic_mem {W : Submodule K V} (hW : PolarNondegOn Q W) (hW0 : W ≠ ⊥) :
    ∃ b ∈ W, Q b ≠ 0 := by
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨y, hyW, hxy⟩ := hW.exists_polar_ne_zero hxW hx0
  by_contra hall
  push Not at hall
  apply hxy
  simp only [QuadraticMap.polar]
  rw [hall _ (W.add_mem hxW hyW), hall _ hxW, hall _ hyW, sub_zero, sub_zero]

theorem finrank_le_two_add_finrank_inf_perp [FiniteDimensional K V] {U : Submodule K V}
    (P : HypPair Q) (he : P.e ∈ U) (hf : P.f ∈ U) :
    Module.finrank K U ≤ 2 + Module.finrank K ↥(U ⊓ P.perp) := by
  classical
  have hle : U ≤ Submodule.span K {P.e, P.f} ⊔ (U ⊓ P.perp) := by
    intro x hx
    rw [P.eq_add_proj x]
    refine Submodule.add_mem_sup (Submodule.add_mem _ ?_ ?_) ⟨?_, P.proj_mem_perp x⟩
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · rw [HypPair.proj]
      exact U.sub_mem (U.sub_mem hx (U.smul_mem _ he)) (U.smul_mem _ hf)
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_add_le_finrank_add_finrank (Submodule.span K {P.e, P.f})
    (U ⊓ P.perp)
  have h3 := finrank_span_finset_le_card (R := K) ({P.e, P.f} : Finset V)
  have h4 : ({P.e, P.f} : Finset V).card ≤ 2 := Finset.card_le_two
  rw [Finset.coe_insert, Finset.coe_singleton] at h3
  exact h1.trans (h2.trans (Nat.add_le_add_right (h3.trans h4) _))

end Split

section Inner

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def ambientPair {U : Submodule K V} (P : HypPair (Q.restrict U)) : HypPair Q where
  e := P.e
  f := P.f
  Q_e := P.Q_e
  Q_f := P.Q_f
  polar_ef := by
    rw [← polar_restrict]
    exact P.polar_ef

theorem exists_spin_eq_of_splitInv_four [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    {a : V ≃ₗ[K] V} {U U' : Submodule K V} (hsp : SplitInv Q U U' a)
    (hU4 : Module.finrank K U = 4) (hU' : U' ≠ ⊥) {P P' : HypPair (Q.restrict U)}
    (hPP : P.Orth P') :
    ∃ x : spinGroup Q, orderOf x = 2 ∧ spinAction Q x = a := by
  classical
  set fr : Frame Q := ⟨ambientPair P, ambientPair P',
    ⟨(polar_restrict P.e P'.e).symm.trans hPP.ee, (polar_restrict P.e P'.f).symm.trans hPP.ef,
      (polar_restrict P.f P'.e).symm.trans hPP.fe, (polar_restrict P.f P'.f).symm.trans hPP.ff⟩⟩
    with hfr
  have hmemU : ∀ v ∈ ({fr.e₁, fr.f₁, fr.e₂, fr.f₂} : Set V), v ∈ U := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact P.e.2
    · exact P.f.2
    · exact P'.e.2
    · exact P'.f.2
  obtain ⟨b, hbU', hb⟩ := exists_anisotropic_mem hsp.ndT hU'
  have hperp : polar Q fr.e₁ b = 0 ∧ polar Q fr.f₁ b = 0 ∧ polar Q fr.e₂ b = 0 ∧
      polar Q fr.f₂ b = 0 :=
    ⟨hsp.orth _ (hmemU _ (by simp)) _ hbU', hsp.orth _ (hmemU _ (by simp)) _ hbU',
      hsp.orth _ (hmemU _ (by simp)) _ hbU', hsp.orth _ (hmemU _ (by simp)) _ hbU'⟩
  set F₀ := CFSG.ComponentClassification.Burgoyne.B.frameHyp fr b (isUnit_iff_ne_zero.mpr hb)
    hperp
  refine ⟨F₀.longSL2 (show (0 : Fin 2) ≠ 1 by decide) true true (-1),
    CFSG.LieType.HighestRoot.orderOf_longSL2_neg_one F₀ _ true true h2, ?_⟩
  rw [CFSG.ComponentClassification.Burgoyne.B.spinAction_frameHyp_longSL2]
  have hspanU : fr.span ≤ U := by
    rintro _ ⟨X, rfl⟩
    rw [Frame.incl_apply]
    exact U.add_mem (U.add_mem (U.add_mem (U.smul_mem _ (hmemU _ (by simp)))
      (U.smul_mem _ (hmemU _ (by simp)))) (U.smul_mem _ (hmemU _ (by simp))))
      (U.smul_mem _ (hmemU _ (by simp)))
  have hspan4 : Module.finrank K fr.span = 4 := by
    have hinj : Function.Injective fr.incl := fun X Y hXY => by
      rw [← fr.coords_incl X, hXY, fr.coords_incl]
    rw [Frame.span, LinearMap.finrank_range_of_inj hinj, Module.finrank_matrix]
    simp
  have hspan : fr.span = U := Submodule.eq_of_le_of_finrank_eq hspanU (by rw [hspan4, hU4])
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨s, hs, t, ht, rfl⟩ := hsp.exists_decomp v
  have hct : fr.coords t = 0 := by
    rw [Frame.coords_apply]
    have e1 : polar Q t fr.f₁ = 0 := by
      rw [polar_comm]
      exact hsp.orth _ (hmemU _ (by simp)) _ ht
    have e2 : polar Q t fr.f₂ = 0 := by
      rw [polar_comm]
      exact hsp.orth _ (hmemU _ (by simp)) _ ht
    have e3 : polar Q t fr.e₂ = 0 := by
      rw [polar_comm]
      exact hsp.orth _ (hmemU _ (by simp)) _ ht
    have e4 : polar Q t fr.e₁ = 0 := by
      rw [polar_comm]
      exact hsp.orth _ (hmemU _ (by simp)) _ ht
    rw [e1, e2, e3, e4]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [map_add, map_add, hsp.negS s hs, hsp.fixT t ht,
    (fr.mem_span_iff_inv h2).mp (hspan ▸ hs), fr.La_apply_of_coords_eq_zero (-1) hct]

end Inner

section ElemOn

variable {K : Type} [Field K]

theorem shortSL2_neg_one_eq_negOne {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {n : ℕ} (F : OddFrame Q n) (i : Fin n) (s : Bool) (hQ : Q ≠ 0) :
    F.shortSL2 i s (-1) = CliffordAlgebra.spinGroup.negOne Q hQ := by
  apply Subtype.ext
  rw [OddFrame.coe_shortSL2, CliffordAlgebra.spinGroup.coe_negOne, sl2Pair_toFun_neg_one,
    F.shortPair_X_mul_Y, F.shortPair_Y_mul_X]
  have h : F.numOp i s + F.numOp i (!s) = 1 := by
    simpa only [HypFrame.numOp, Bool.not_not] using F.ι_vec_mul_ι_vec_not_add i s
  rw [h]
  abel

theorem u1_elemOn [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    {α : MulAut (spinGroup (quadOdd 3 K))}
    {a : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)}
    (ha : a ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K))
    {U U' : Submodule K (Fin 3 ⊕ Fin 3 ⊕ Unit → K)} (hsp : SplitInv (quadOdd 3 K) U U' a)
    (hU4 : 4 ≤ Module.finrank K U) (hEq : CFSG.Open.IsQuasisimple ↥(elemOn (quadOdd 3 K) U))
    (hπ : ∀ s, spinAction (quadOdd 3 K) (α s) = a * spinAction (quadOdd 3 K) s * a⁻¹) :
    ∃ J : Subgroup (spinGroup (quadOdd 3 K)), IsTwoComponentIn J (fixedSubgroup α) ∧
      spinZ K ∈ J ∧ ¬ IsSLTwoOver (p ^ f) (↥J ⧸ pPrimeCore 2 ↥J) := by
  classical
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 := two_ne_zero_spin hp hp2 hK
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have := finite_spinSeven h2
  have hQnd : (quadOdd 3 K).Nondegenerate := nondegenerate_quadOdd 3 K
  set π := spinAction (quadOdd 3 K) with hπdef
  set E := elemOn (quadOdd 3 K) U with hEdef
  have hcen : π.ker ≤ center (spinGroup (quadOdd 3 K)) := ker_spinAction_le_center _
  have hker : ∀ s, s ∈ π.ker ↔ s = 1 ∨ s = spinZ K := mem_ker_spinAction_iff _ hQnd
  have hrange : π.range = elementaryGroup (quadOdd 3 K) := by
    rw [hπdef, range_spinAction_quadOdd_eq_commutator h2 (le_refl 3),
      commutator_orthogonalGroup_quadOdd h2 (le_refl 3)]
  have hEr : E ≤ π.range := hrange ▸ elemOn_le_elementaryGroup
  have hπO : ∀ g, π g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) := fun g =>
    elementaryGroup_le_orthogonalGroup _ (hrange ▸ ⟨g, rfl⟩)
  have hEq' : IsQuasisimple ↥E := isQuasisimple_of_openQuasisimple hEq
  have h3U : 3 ≤ Module.finrank K U := by omega
  obtain ⟨P, hPe, hPf⟩ := CFSG.ClassicalInvolution.Asc77.exists_hypPair_le hodd hsp.ndS h3U
  have hW : PolarNondegOn (quadOdd 3 K) (U ⊓ P.perp) := hsp.ndS.inf_perp P hPe hPf
  have hW2 : 2 ≤ Module.finrank K ↥(U ⊓ P.perp) := by
    have := finrank_le_two_add_finrank_inf_perp P hPe hPf
    omega
  obtain ⟨w, hwW, hQw⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_mem_eq_unit hodd
    (QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_restrict hW)) hW2 1
  rw [Units.val_one] at hQw
  have hwU : w ∈ U := hwW.1
  have hwP := HypPair.mem_perp.mp hwW.2
  set F₁ : OddFrame (quadOdd 3 K) 1 :=
    { vec := fun _ s => if s then P.e else P.f
      map_vec := fun _ s => by cases s <;> simp [P.Q_e, P.Q_f]
      polar_vec_of_ne := fun i j hij => absurd (Subsingleton.elim i j) hij
      polar_vec_not := fun _ s => by cases s <;> simp [P.polar_ef, P.polar_fe]
      exists_aux := fun _ _ => ⟨w, by rw [hQw]; exact isUnit_one, fun s => by
        cases s <;> simp [hwP.1, hwP.2]⟩
      z := w
      map_z := hQw
      polar_vec_z := fun _ s => by cases s <;> simp [hwP.1, hwP.2] } with hF₁
  set ψ := F₁.shortSL2 0 true with hψ
  have hψneg : ψ (-1) = spinZ K := shortSL2_neg_one_eq_negOne F₁ 0 true _
  have hψup : ∀ c : K, π (ψ (upperSL2 c)) ∈ E := fun c => by
    rw [hψ, OddFrame.shortSL2_upperSL2, hπdef, OddFrame.spinAction_shortRoot_eq_eichler]
    exact eichler_mem_elemOn hPe (U.smul_mem c hwU)
  have hψlo : ∀ c : K, π (ψ (lowerSL2 c)) ∈ E := fun c => by
    rw [hψ, OddFrame.shortSL2_lowerSL2, hπdef, OddFrame.spinAction_shortRoot_eq_eichler]
    exact eichler_mem_elemOn hPf (U.smul_mem _ hwU)
  set J := E.comap π with hJ
  have hzJJ : spinZ K ∈ ⁅J, J⁆ := by
    obtain ⟨x, y, hy, hxy⟩ := exists_sq_add_sq_eq_neg_one hodd
    have hc := commutatorElement_upperSL2_lowerSL2_eq_neg_one (d := (1 : K)) one_ne_zero hy hxy
    have hmem : ∀ a b c : K, ψ (upperSL2 a * lowerSL2 b * upperSL2 c) ∈ J := fun a b c => by
      rw [map_mul, map_mul]
      exact mul_mem (mul_mem (hψup a) (hψlo b)) (hψup c)
    rw [← hψneg, ← hc, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (hmem _ _ _) (hmem _ _ _)
  have hkerJ : π.ker ≤ ⁅J, J⁆ := fun s hs => by
    rcases (hker s).mp hs with rfl | rfl
    · exact one_mem _
    · exact hzJJ
  have hJq : IsQuasisimple ↥J := isQuasisimple_comap_of_le π hEq' hEr hcen hkerJ
  have hJp : ⁅J, J⁆ = J :=
    commutator_comap_eq_of_le π (Subgroup.isPerfect_iff.mp hEq'.1) hEr hkerJ
  have hzJ : spinZ K ∈ J := by
    have : spinZ K ∈ π.ker := (hker _).mpr (Or.inr rfl)
    show π (spinZ K) ∈ E
    rw [MonoidHom.mem_ker.mp this]
    exact one_mem _
  obtain ⟨hzz, hz1, -⟩ := spinZ_facts hp hp2 hK
  have hZE : ∀ g ∈ E, (∀ h ∈ E, g * h = h * g) → g * g = 1 := by
    intro g hg hcomm
    have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) :=
      elementaryGroup_le_orthogonalGroup _ (elemOn_le_elementaryGroup hg)
    obtain ⟨hgU, hgfix⟩ := support_of_mem_elemOn hg
    obtain ⟨c', hc'⟩ := exists_smul_of_commute_elemOn hodd hsp.ndS h3U hgO hgU
      fun h hh => hcomm h hh
    have hu0 : quadOdd 3 K (P.e + P.f) = 1 := by
      rw [QuadraticMap.map_add (quadOdd 3 K) P.e P.f, P.Q_e, P.Q_f, P.polar_ef]
      ring
    have hc2 : c' * c' = 1 := by
      have h1 := map_of_mem hgO (P.e + P.f)
      rw [hc' _ (U.add_mem hPe hPf), QuadraticMap.map_smul, hu0, smul_eq_mul, mul_one] at h1
      exact h1
    refine eq_of_agree_on (nondegenerate_polarBilin_restrict hsp.ndS) (fun x hx => ?_)
      (fun z hz => ?_) fun z _ => rfl
    · rw [LinearEquiv.mul_apply, hc' x hx, map_smul, hc' x hx, smul_smul, hc2, one_smul]
      rfl
    · rw [LinearEquiv.mul_apply, hgfix z hz, hgfix z hz]
  have hker2 : ∀ s ∈ π.ker, s * s = 1 := fun s hs => by
    rcases (hker s).mp hs with rfl | rfl
    · exact one_mul 1
    · exact hzz
  have hO : pPrimeCore 2 ↥J = ⊥ := pPrimeCore_comap_eq_bot π hJq hEr hZE hker2 hzJ hz1 hzz
  have hfix : ∀ s ∈ J, α s = s := by
    refine apply_eq_of_map_apply_eq π hcen hJp α fun s hs => ?_
    have hcomm := comm_of_scalar_elemOn ha (ε := -1) (by norm_num)
      (fun x hx => by rw [hsp.negS x hx, neg_one_smul]) (show π s ∈ E from hs)
    rw [hπ s, hcomm, mul_inv_cancel_right]
  have hJC : J ≤ fixedSubgroup α := fun s hs => mem_fixedSubgroup.mpr (hfix s hs)
  have hnorm : (J.subgroupOf (fixedSubgroup α)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hga : ∀ x, π g (a x) = a (π g x) := by
      intro x
      have h1 := hπ (g : spinGroup (quadOdd 3 K))
      rw [mem_fixedSubgroup.mp g.2] at h1
      have h3 : π ↑g * a = a * π ↑g := by
        calc π ↑g * a = a * π ↑g * a⁻¹ * a := by rw [← h1]
          _ = a * π ↑g := by group
      exact LinearEquiv.congr_fun h3 x
    obtain ⟨hgU, -⟩ := hsp.preserves_of_comm h2 hga
    have h4 := conj_mem_elemOn (hπO g) hgU (show π n ∈ E from hn)
    show π (↑(g * n * g⁻¹)) ∈ E
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv]
    exact h4
  have hdvd : (p ^ f) ^ 2 ∣ Nat.card ↥J := by
    let φ : ↥(U ⊓ P.perp) →ₗ[K] K := (polarBilin (quadOdd 3 K) w).comp (U ⊓ P.perp).subtype
    have hφ : LinearMap.ker φ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
      rw [Module.finrank_self]
      omega)
    obtain ⟨w', hw'ker, hw'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hφ
    have hw'w : polar (quadOdd 3 K) w w' = 0 := by
      have := LinearMap.mem_ker.mp hw'ker
      simpa [φ, polarBilin_apply_apply] using this
    have hw'U : (w' : Fin 3 ⊕ Fin 3 ⊕ Unit → K) ∈ U := w'.2.1
    have hw'P := HypPair.mem_perp.mp w'.2.2
    have hw'0' : (w' : Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≠ 0 := fun h => hw'0 (Subtype.ext h)
    let ρ : K × K →+ (Fin 3 ⊕ Fin 3 ⊕ Unit → K) :=
      { toFun := fun x => x.1 • w + x.2 • (w' : Fin 3 ⊕ Fin 3 ⊕ Unit → K)
        map_zero' := by simp
        map_add' := fun x y => by
          simp only [Prod.fst_add, Prod.snd_add, add_smul]
          abel }
    have hρ : Function.Injective ρ := by
      rw [injective_iff_map_eq_zero]
      rintro ⟨s, t⟩ hst
      change s • w + t • (w' : Fin 3 ⊕ Fin 3 ⊕ Unit → K) = 0 at hst
      have h1 := congrArg (polar (quadOdd 3 K) w) hst
      rw [polar_add_right, polar_smul_right, polar_smul_right, hw'w, polar_self, hQw,
        polar_zero_right, smul_eq_mul, smul_eq_mul, mul_zero, add_zero] at h1
      have hs : s = 0 := by
        have : s * 2 = 0 := by simpa using h1
        exact (mul_eq_zero.mp this).resolve_right h2
      rw [hs, zero_smul, zero_add] at hst
      have ht : t = 0 := (smul_eq_zero.mp hst).resolve_right hw'0'
      rw [hs, ht]
      rfl
    have hρmem : ∀ x : K × K, ρ x ∈ U := fun x =>
      U.add_mem (U.smul_mem _ hwU) (U.smul_mem _ hw'U)
    have hρe : ∀ x : K × K, polar (quadOdd 3 K) P.e (ρ x) = 0 := fun x => by
      change polar (quadOdd 3 K) P.e (x.1 • w + x.2 • (w' : Fin 3 ⊕ Fin 3 ⊕ Unit → K)) = 0
      rw [polar_add_right, polar_smul_right, polar_smul_right, hwP.1, hw'P.1, smul_zero,
        smul_zero, add_zero]
    have hρf : ∀ x : K × K, polar (quadOdd 3 K) P.f (ρ x) = 0 := fun x => by
      change polar (quadOdd 3 K) P.f (x.1 • w + x.2 • (w' : Fin 3 ⊕ Fin 3 ⊕ Unit → K)) = 0
      rw [polar_add_right, polar_smul_right, polar_smul_right, hwP.2, hw'P.2, smul_zero,
        smul_zero, add_zero]
    have h1 : Nat.card (K × K) ∣ Nat.card ↥E :=
      card_dvd_of_eichler_mem ρ hρ P.Q_e (by rw [P.polar_ef]; exact one_ne_zero) hρe hρf
        fun x => eichler_mem_elemOn hPe (hρmem x)
    have h3 : Nat.card ↥E ∣ Nat.card ↥J :=
      Subgroup.card_dvd_of_surjective (comapRestrict_surjective π hEr)
    rw [Nat.card_prod, hK, ← pow_two] at h1
    exact h1.trans h3
  refine ⟨J, isTwoComponentIn_of_normal_of_pPrimeCore hJC hnorm hJq hO, hzJ,
    not_isSLTwoOver_of_sq_dvd hO (by have := Finite.one_lt_card (α := K); omega) hdvd⟩

end ElemOn

section Linear

variable {K : Type} [Field K]

@[expose] def QuasisimpleRestrictInput (K : Type) [Field K] : Prop :=
  ∀ U : Submodule K (Fin 3 ⊕ Fin 3 ⊕ Unit → K), PolarNondegOn (quadOdd 3 K) U →
    4 ≤ Module.finrank K U →
    (Module.finrank K U ≠ 4 ∨ ∀ P P' : HypPair ((quadOdd 3 K).restrict U), ¬ P.Orth P') →
      CFSG.Open.IsQuasisimple ↥(elementaryGroup ((quadOdd 3 K).restrict U))

theorem quasisimpleRestrictInput_of_five_le [Finite K] (hodd : Odd (Nat.card K))
    (h5 : 5 ≤ Nat.card K) : QuasisimpleRestrictInput K := fun _ hU hU4 hne =>
  CFSG.ClassicalGroups.Orthogonal.Small.isQuasisimple_elementaryGroup_small hodd h5
    (nondegenerate_polarBilin_restrict hU) (by omega) hne

theorem u1_of_splitInv [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hQS : QuasisimpleRestrictInput K)
    {α : MulAut (spinGroup (quadOdd 3 K))}
    {a : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)}
    (ha : a ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K))
    {U U' : Submodule K (Fin 3 ⊕ Fin 3 ⊕ Unit → K)} (hsp : SplitInv (quadOdd 3 K) U U' a)
    (hU4 : 4 ≤ Module.finrank K U)
    (hπ : ∀ s, spinAction (quadOdd 3 K) (α s) = a * spinAction (quadOdd 3 K) s * a⁻¹) :
    (∃ x : spinGroup (quadOdd 3 K), x * x = 1 ∧ x ∉ center (spinGroup (quadOdd 3 K)) ∧
        α = MulAut.conj x) ∨
      ∃ J : Subgroup (spinGroup (quadOdd 3 K)), IsTwoComponentIn J (fixedSubgroup α) ∧
        spinZ K ∈ J ∧ ¬ IsSLTwoOver (p ^ f) (↥J ⧸ pPrimeCore 2 ↥J) := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_spin hp hp2 hK
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hfin : Module.finrank K (Fin 3 ⊕ Fin 3 ⊕ Unit → K) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hdims := finrank_add_finrank_of_splitInv h2 hsp
  rw [hfin] at hdims
  by_cases h4 : Module.finrank K U = 4 ∧
      ∃ P P' : HypPair ((quadOdd 3 K).restrict U), P.Orth P'
  · obtain ⟨hU4', P, P', hPP⟩ := h4
    have hU'0 : U' ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hdims
      omega
    obtain ⟨x, hx2, hxa⟩ := exists_spin_eq_of_splitInv_four h2 hsp hU4' hU'0 hPP
    left
    refine ⟨x, ?_, ?_, ?_⟩
    · rw [← pow_two, ← hx2, pow_orderOf_eq_one]
    · intro hxZ
      rw [center_spinGroup_quadOdd_eq_ker h2 (le_refl 3), MonoidHom.mem_ker, hxa] at hxZ
      have hU0 : U ≠ ⊥ := by
        intro h
        rw [h, finrank_bot] at hU4
        omega
      obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
      have h1 : u = -u := by
        have := hsp.negS u huU
        rwa [hxZ] at this
      have h3 : (2 : K) • u = 0 := by
        rw [two_smul]
        nth_rewrite 1 [h1]
        exact neg_add_cancel u
      exact hu0 ((smul_eq_zero.mp h3).resolve_left h2)
    · have : Group.IsPerfect (spinGroup (quadOdd 3 K)) :=
        isPerfect_spinGroup_quadOdd h2 (le_refl 3)
      exact eq_conj_of_map_apply_eq (spinAction (quadOdd 3 K)) (ker_spinAction_le_center _) α x
        fun s => by rw [hπ s, map_mul, map_mul, map_inv, hxa]
  · right
    have hne : Module.finrank K U ≠ 4 ∨
        ∀ P P' : HypPair ((quadOdd 3 K).restrict U), ¬ P.Orth P' := by
      by_cases h4' : Module.finrank K U = 4
      · exact Or.inr fun P P' hPP => h4 ⟨h4', P, P', hPP⟩
      · exact Or.inl h4'
    have hU' := nondegenerate_polarBilin_restrict hsp.ndS
    have hEq : CFSG.Open.IsQuasisimple ↥(elemOn (quadOdd 3 K) U) :=
      isQuasisimple_of_mulEquiv_open (resEquiv hU').symm (hQS U hsp.ndS hU4 hne)
    exact u1_elemOn hp hp2 hK ha hsp hU4 hEq hπ

theorem u1_linear [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (hQS : QuasisimpleRestrictInput K) {α : MulAut (spinGroup (quadOdd 3 K))}
    {F : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃+ (Fin 3 ⊕ Fin 3 ⊕ Unit → K)}
    (hF : ∀ (c : K) v, F (c • v) = c • F v) {μ : K}
    (hQF : ∀ v, quadOdd 3 K (F v) = μ * quadOdd 3 K v) {c : K} (hc : c ≠ 0)
    (hFF : ∀ v, F (F v) = c • v)
    (hπ : ∀ s v, spinAction (quadOdd 3 K) (α s) v = F (spinAction (quadOdd 3 K) s (F.symm v))) :
    (∃ x : spinGroup (quadOdd 3 K), x * x = 1 ∧ x ∉ center (spinGroup (quadOdd 3 K)) ∧
        α = MulAut.conj x) ∨
      ∃ J : Subgroup (spinGroup (quadOdd 3 K)), IsTwoComponentIn J (fixedSubgroup α) ∧
        spinZ K ∈ J ∧ ¬ IsSLTwoOver (p ^ f) (↥J ⧸ pPrimeCore 2 ↥J) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_spin hp hp2 hK
  obtain ⟨T, l, hl0, hTO, hTT, hFT⟩ := exists_isometry_involution h2 hF hQF hc hFF
  have hFsymm : ∀ v, F.symm v = l⁻¹ • T.symm v := fun v => F.injective (by
    rw [AddEquiv.apply_symm_apply, hFT, map_smul, LinearEquiv.apply_symm_apply, smul_smul,
      mul_inv_cancel₀ hl0, one_smul])
  have hπT : ∀ s, spinAction (quadOdd 3 K) (α s) = T * spinAction (quadOdd 3 K) s * T⁻¹ :=
    fun s => LinearEquiv.ext fun v => by
      rw [hπ, hFsymm, map_smul, hFT, map_smul, smul_smul, mul_inv_cancel₀ hl0, one_smul]
      rfl
  have hsp := splitInv_of_involution h2 (nondegenerate_polarBilin_quadOdd 3 K h2) hTO hTT
  have hfin : Module.finrank K (Fin 3 ⊕ Fin 3 ⊕ Unit → K) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hdims := finrank_add_finrank_of_splitInv h2 hsp
  rw [hfin] at hdims
  by_cases hU : 4 ≤ Module.finrank K (negSpace T)
  · exact u1_of_splitInv hp hp2 hK hQS hTO hsp hU hπT
  · have hTO' : T.trans (LinearEquiv.neg K) ∈
        TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
        rw [LinearEquiv.trans_apply, LinearEquiv.neg_apply, QuadraticMap.map_neg]
        exact map_of_mem hTO v
    have hπT' : ∀ s, spinAction (quadOdd 3 K) (α s) =
        T.trans (LinearEquiv.neg K) * spinAction (quadOdd 3 K) s *
          (T.trans (LinearEquiv.neg K))⁻¹ := fun s => by
      rw [hπT s]
      refine LinearEquiv.ext fun v => ?_
      change T (spinAction (quadOdd 3 K) s (T.symm v)) =
        -(T (spinAction (quadOdd 3 K) s (T.symm (-v))))
      rw [map_neg, map_neg, map_neg, neg_neg]
    exact u1_of_splitInv hp hp2 hK hQS hTO' (splitInv_neg hsp) (by omega) hπT'

end Linear

end CFSG.ComponentClassification.HarrisLit.T1
