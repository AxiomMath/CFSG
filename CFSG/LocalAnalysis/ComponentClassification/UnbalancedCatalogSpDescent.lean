module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticDescent
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpRadical

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher CatalogueBAlternatingIsometry CatalogueBSymplecticB
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace SpChain

theorem ringAut_pow_apply_of_sq {K : Type*} [Field K] {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ 2)
    (n : ℕ) (c : K) : (φ ^ n) c = c ^ 2 ^ n := by
  induction n with
  | zero => rw [pow_zero, RingAut.one_apply, pow_zero, pow_one]
  | succ n ih => rw [pow_succ', RingAut.mul_apply, ih, hφ, ← pow_mul, ← pow_succ]

theorem ringEquiv_involution_facts {K : Type*} [Field K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {σ : K ≃+* K} (hσσ : σ * σ = 1) (hσ1 : σ ≠ 1) :
    Even f ∧ (∀ t, σ t = t ^ 2 ^ (f / 2)) ∧ Nat.card (descentField σ) = 2 ^ (f / 2) := by
  obtain ⟨φ, hφ, hord, hzp, -, hfix⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf hK
  have hσord : orderOf σ = 2 := orderOf_eq_prime (by rw [sq, hσσ]) hσ1
  have hfin : IsOfFinOrder φ := orderOf_pos_iff.mp (by rw [hord]; omega)
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp
    (hfin.mem_powers_iff_mem_zpowers.mpr (hzp ▸ Subgroup.mem_top σ))
  set n := m % f with hn
  have hσn : φ ^ n = σ := by rw [hn, ← hord, pow_mod_orderOf, hm]
  have hnlt : n < f := Nat.mod_lt _ (by omega)
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hσn
    exact hσ1 hσn.symm
  have hdvd : f ∣ 2 * n := by
    rw [← hord]
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [pow_mul', hσn, sq, hσσ]
  have h2n : 2 * n = f := Nat.eq_of_dvd_of_lt_two_mul (by omega) hdvd (by omega)
  have hf2 : f / 2 = n := by omega
  refine ⟨⟨n, by omega⟩, fun t => by rw [← hσn, ringAut_pow_apply_of_sq hφ, hf2], ?_⟩
  obtain ⟨-, S, hS, hcardS⟩ := hfix (Subgroup.zpowers σ)
  rw [Nat.card_zpowers, hσord] at hcardS
  rw [← hcardS]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
  rw [mem_descentField, ← SetLike.mem_coe, hS]
  constructor
  · intro hc τ hτ
    have hσfin : IsOfFinOrder σ := orderOf_pos_iff.mp (by rw [hσord]; norm_num)
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp
      (hσfin.mem_powers_iff_mem_zpowers.mpr hτ)
    induction k with
    | zero => rw [pow_zero, RingAut.one_apply]
    | succ k ih => rw [pow_succ', RingAut.mul_apply, ih (Subgroup.pow_mem _ (Subgroup.mem_zpowers
        σ) k), hc]
  · intro hc
    exact hc σ (Subgroup.mem_zpowers σ)

variable {r : ℕ} {K : Type} [Field K]

@[expose] def spSemilinear (g : StatedSp r K) (σ : K ≃+* K) :
    (Fin r ⊕ Fin r → K) →ₛₗ[(σ : K →+* K)] (Fin r ⊕ Fin r → K) where
  toFun := semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) σ
  map_add' := map_add _
  map_smul' := semilinearCoordMap_smul _ σ

theorem spSemilinear_apply (g : StatedSp r K) (σ : K ≃+* K) (v : Fin r ⊕ Fin r → K) :
    spSemilinear g σ v = spMat g *ᵥ fun i => σ (v i) :=
  rfl

theorem pairedSympForm_mem_descentField {g : StatedSp r K} {σ : K ≃+* K} {w w' : Fin r ⊕ Fin r → K}
    (hw : w ∈ fixSpace (spSemilinear g σ)) (hw' : w' ∈ fixSpace (spSemilinear g σ)) :
    pairedSympForm K r w w' ∈ descentField σ := by
  have h1 : semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) σ w = w := mem_fixSpace.mp hw
  have h2 : semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) σ w' = w' := mem_fixSpace.mp hw'
  rw [mem_descentField, ← pairedSympForm_semilinearCoordMap g σ, h1, h2]

@[expose] def descentSymp (g : StatedSp r K) (σ : K ≃+* K) :
    LinearMap.BilinForm (descentField σ) (fixSpace (spSemilinear g σ)) :=
  LinearMap.mk₂ (descentField σ)
    (fun w w' => ⟨pairedSympForm K r w w', pairedSympForm_mem_descentField w.2 w'.2⟩)
    (fun w₁ w₂ w' => Subtype.ext (by simp))
    (fun a w w' => Subtype.ext (by simp [Subfield.smul_def]))
    (fun w w₁ w₂ => Subtype.ext (by simp))
    (fun a w w' => Subtype.ext (by simp [Subfield.smul_def]))

theorem coe_descentSymp (g : StatedSp r K) (σ : K ≃+* K) (w w' : fixSpace (spSemilinear g σ)) :
    (descentSymp g σ w w' : K) = pairedSympForm K r w w' :=
  rfl

theorem descentSymp_isAlt (g : StatedSp r K) (σ : K ≃+* K) : (descentSymp g σ).IsAlt :=
  fun w => Subtype.ext (pairedSympForm_self (w : Fin r ⊕ Fin r → K))

theorem eq_zero_of_forall_mem_span {S : Set (Fin r ⊕ Fin r → K)}
    (hS : Submodule.span K S = ⊤) {w : Fin r ⊕ Fin r → K}
    (hw : ∀ x ∈ S, pairedSympForm K r w x = 0) : w = 0 := by
  refine SymplecticFlag.pairedSympForm_nondegenerate.1 w fun x => ?_
  have hx : x ∈ Submodule.span K S := hS ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact hw x hx
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_smul, hx, smul_zero]

theorem descentSymp_nondegenerate {g : StatedSp r K} {σ : K ≃+* K}
    (hspan : Submodule.span K (fixSpace (spSemilinear g σ) : Set (Fin r ⊕ Fin r → K)) = ⊤) :
    (descentSymp g σ).Nondegenerate := by
  have hleft : ∀ w : fixSpace (spSemilinear g σ), (∀ w', descentSymp g σ w w' = 0) → w = 0 := by
    intro w hw
    refine Subtype.ext (eq_zero_of_forall_mem_span hspan fun x hx => ?_)
    exact congrArg Subtype.val (hw ⟨x, hx⟩)
  refine ⟨hleft, fun w hw => hleft w fun w' => ?_⟩
  rw [← (descentSymp_isAlt g σ).neg_eq w' w, hw w', neg_zero]

end SpChain

open SpChain

theorem even_symplectic_quadratic_involution_descent {r f : ℕ} (hr : 1 ≤ r) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) {a : MulAut (StatedProj (StatedSp r K))}
    (ha : a * a = 1) (g : StatedSp r K) (σ : K ≃+* K)
    (hag : a = conjAut r K ⟨g, statedSp_le_gsp g.2⟩ * fieldAut r K σ) (hσ : σ ≠ 1) :
    Even f ∧ (∀ t, σ t = t ^ 2 ^ (f / 2)) ∧ Nat.card (descentField σ) = 2 ^ (f / 2) ∧
    (∀ v, spSemilinear g σ (spSemilinear g σ v) = v) ∧
    finrank (descentField σ) (fixSpace (spSemilinear g σ)) = 2 * r ∧
    (∀ w ∈ fixSpace (spSemilinear g σ), ∀ w' ∈ fixSpace (spSemilinear g σ),
      pairedSympForm K r w w' ∈ descentField σ) ∧
    (∀ w ∈ fixSpace (spSemilinear g σ),
      (∀ w' ∈ fixSpace (spSemilinear g σ), pairedSympForm K r w w' = 0) → w = 0) ∧
    (∀ w ∈ fixSpace (spSemilinear g σ),
      (∀ w' ∈ fixSpace (spSemilinear g σ), pairedSympForm K r w' w = 0) → w = 0) ∧
    (∃ b : Module.Basis (Fin r ⊕ Fin r) (descentField σ) (fixSpace (spSemilinear g σ)),
      ∀ i j, pairedSympForm K r (b i) (b j) = formJ r K i j) ∧
    (∀ {ι : Type} (b : Module.Basis ι (descentField σ) (fixSpace (spSemilinear g σ))),
      LinearIndependent K (fun i => (b i : Fin r ⊕ Fin r → K)) ∧
        Submodule.span K (Set.range fun i => (b i : Fin r ⊕ Fin r → K)) = ⊤) ∧
    ∃ h : StatedSp r K, a = conjAut r K ⟨h, statedSp_le_gsp h.2⟩ * fieldAut r K σ *
      (conjAut r K ⟨h, statedSp_le_gsp h.2⟩)⁻¹ := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : NeZero r := ⟨by omega⟩
  rw [← spInner_apply] at hag
  subst hag
  have hsq := ha
  rw [spInner_mul_fieldAut_mul, show (1 : MulAut (StatedProj (StatedSp r K))) =
    spInner r K 1 * fieldAut r K 1 by rw [map_one, map_one, one_mul]] at hsq
  obtain ⟨hgg, hσσ⟩ := spInner_mul_fieldAut_inj hsq
  have hσσ' : ∀ t, σ (σ t) = t := fun t => by
    change (σ * σ) t = t
    rw [hσσ]
    rfl
  obtain ⟨hfeven, hσform, hcardk⟩ := ringEquiv_involution_facts hf hK hσσ hσ
  set T := spSemilinear g σ with hTdef
  have hTT : ∀ v, T (T v) = v := by
    intro v
    have h1 := semilinearCoordMap_sq (g : GL (Fin r ⊕ Fin r) K) σ (by rw [sq, hσσ]) 1
      (by rw [map_one]; exact congrArg Subtype.val hgg) v
    rwa [Units.val_one, one_smul] at h1
  obtain ⟨c, hc⟩ : ∃ c, σ c ≠ c := by
    by_contra! h
    exact hσ (RingEquiv.ext h)
  set W := fixSpace T with hWdef
  have hspan := span_fixSpace hσσ' hTT hc
  have : Module.Finite (descentField σ) W := finite_fixSpace
  have hfin : finrank (descentField σ) W = 2 * r := by
    rw [finrank_fixSpace hσσ' hTT hc, finrank_standard]
  have hleft : ∀ w ∈ W, (∀ w' ∈ W, pairedSympForm K r w w' = 0) → w = 0 := fun w _ hw =>
    eq_zero_of_forall_mem_span hspan hw
  have hright : ∀ w ∈ W, (∀ w' ∈ W, pairedSympForm K r w' w = 0) → w = 0 := by
    intro w hwW hw
    refine hleft w hwW fun w' hw' => ?_
    rw [← SymplecticFlag.pairedSympForm_isAlt.neg_eq w' w, hw w' hw', neg_zero]
  obtain ⟨b, hb, -⟩ := exists_completeIsotropicFlag (descentSymp_isAlt g σ)
    (descentSymp_nondegenerate hspan) hfin (W := ⊥) (fun x hx _ _ => by
      rw [Submodule.mem_bot] at hx
      rw [hx, map_zero, LinearMap.zero_apply])
  have hbJ : ∀ i j, pairedSympForm K r (b i) (b j) = formJ r K i j := by
    intro i j
    have h1 := congrFun₂ hb i j
    rw [LinearMap.BilinForm.toMatrix_apply] at h1
    rw [← coe_descentSymp, h1]
    exact congrFun₂ (UnitaryHigher.formJ_map_ringHom (r := r) (K := K)
      (descentField σ).subtype) i j
  have hKbasis : ∀ {ι : Type} (b : Module.Basis ι (descentField σ) W),
      LinearIndependent K (fun i => (b i : Fin r ⊕ Fin r → K)) ∧
        Submodule.span K (Set.range fun i => (b i : Fin r ⊕ Fin r → K)) = ⊤ :=
    fun b => ⟨linearIndependent_fixSpace hσσ' hc b,
      eq_top_iff.mpr (span_basis_fixSpace hσσ' hTT hc b)⟩
  refine ⟨hfeven, hσform, hcardk, hTT, hfin, fun w hw w' hw' =>
    pairedSympForm_mem_descentField hw hw', hleft, hright, ⟨b, hbJ⟩, hKbasis, ?_⟩
  set b' := fixSpaceBasis hσσ' hTT hc b with hb'def
  have hb' : IsSymplecticBasis (pairedSympForm K r) b' := by
    show LinearMap.BilinForm.toMatrix b' (pairedSympForm K r) = _
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, hb'def, fixSpaceBasis_apply, fixSpaceBasis_apply,
      hbJ]
  obtain ⟨h, hh⟩ := exists_statedSp_mulVec_basis (toMatrix_pairedSympForm (r := r) (K := K)) hb'
  have hF : T.comp (mulVecLin (spMat h)) = (mulVecLin (spMat h)).comp (spSemilinear 1 σ) := by
    refine (Pi.basisFun K (Fin r ⊕ Fin r)).ext fun x => ?_
    have hσe : (fun i => σ ((Pi.basisFun K (Fin r ⊕ Fin r)) x i)) =
        Pi.basisFun K (Fin r ⊕ Fin r) x := by
      funext i
      rw [Pi.basisFun_apply]
      by_cases hix : i = x
      · rw [hix, Pi.single_eq_same, map_one]
      · rw [Pi.single_eq_of_ne hix, map_zero]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, mulVecLin_apply, mulVecLin_apply, hh x,
      spSemilinear_apply 1 σ, hσe,
      show spMat (1 : StatedSp r K) *ᵥ Pi.basisFun K (Fin r ⊕ Fin r) x =
        Pi.basisFun K (Fin r ⊕ Fin r) x from one_mulVec _, hh x, hb'def, fixSpaceBasis_apply]
    exact mem_fixSpace.mp (b x).2
  have hgh : g * fieldSp r K σ h = h := by
    refine statedSp_ext fun u => ?_
    set v : Fin r ⊕ Fin r → K := fun i => σ.symm (u i) with hv
    have hσv : (fun i => σ (v i)) = u := funext fun i => σ.apply_symm_apply (u i)
    have h1 := LinearMap.congr_fun hF v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, mulVecLin_apply, mulVecLin_apply,
      spSemilinear_apply, spSemilinear_apply, coord_mulVec, hσv,
      show spMat (1 : StatedSp r K) *ᵥ u = u from one_mulVec u, mulVec_mulVec] at h1
    rw [← h1]
    rfl
  refine ⟨h, ?_⟩
  rw [← spInner_apply]
  have hg' : g = h * fieldSp r K σ h⁻¹ := by
    rw [map_inv]
    exact eq_mul_inv_of_mul_eq hgh
  calc spInner r K g * fieldAut r K σ
      _ = spInner r K h * spInner r K (fieldSp r K σ h⁻¹) * fieldAut r K σ := by
        rw [hg', map_mul]
      _ = spInner r K h * (fieldAut r K σ * spInner r K h⁻¹ * (fieldAut r K σ)⁻¹) *
          fieldAut r K σ := by rw [fieldAut_mul_spInner_mul_inv]
      _ = spInner r K h * fieldAut r K σ * (spInner r K h)⁻¹ := by rw [map_inv]; group

end CFSG.ComponentClassification.UnbalancedCatalog
