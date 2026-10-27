module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Lin
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Lin

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
open scoped MatrixGroups

section Compat

variable {K : Type} [Field K] {σ : K →+* K}

theorem torus_compat {x : twistedGroup σ} {b : Fin d4.rank → Kˣ}
    (hx : twistedIncl σ x = rootDiagUnit d4 b) :
    ((b (nd 1) : Kˣ) : K) = σ (b (nd 0)) ∧ ((b (nd 3) : Kˣ) : K) = σ (b (nd 1)) ∧
      ((b (nd 0) : Kˣ) : K) = σ (b (nd 3)) ∧ ((b (nd 2) : Kˣ) : K) = σ (b (nd 2)) := by
  have h := twistHom_eq_of_mem_twistedFixedGroup (twistedIncl_mem_twistedFixedGroup x)
  rw [hx] at h
  have c := fun i => compat_of_twistHom_rootDiagUnit (t := TwistTag.D4) h i
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact congrArg Units.val (c (nd 0))
  · exact congrArg Units.val (c (nd 1))
  · exact congrArg Units.val (c (nd 3))
  · exact congrArg Units.val (c (nd 2))

end Compat

section Long

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

theorem slLongE_HSL (t : (fixedField σ)ˣ) :
    slLongE σ (HSL t) =
      torusElement d4 K (nd 2) (Units.map (fixedField σ).subtype.toMonoidHom t) := by
  set t' : Kˣ := Units.map (fixedField σ).subtype.toMonoidHom t with ht'
  have hmem : torusElement d4 K (nd 2) t' ∈
      rankOne (rootGroup (rootOperatorFamily d4) K) (nd 2) := torusElement_mem_rankOne (nd 2) t'
  set z : SL(2, K) := Matrix.SpecialLinearGroup.map (fixedField σ).subtype (HSL t) with hz
  have hy : restrictEquiv (rootOperatorFamily d4) cartan_two_zero
      ⟨torusElement d4 K (nd 2) t', hmem⟩ = z := by
    apply Subtype.ext
    show ((restrictHom (rootOperatorFamily d4) cartan_two_zero ⟨_, hmem⟩ :
      SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = _
    rw [restrictHom_torusElement cartan_two_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hz, coe_HSL, ht']
  have : (restrictEquiv (rootOperatorFamily d4) cartan_two_zero).symm z =
      ⟨torusElement d4 K (nd 2) t', hmem⟩ := by
    rw [MulEquiv.symm_apply_eq, hy]
  show (((restrictEquiv (rootOperatorFamily d4) cartan_two_zero).symm z :
    rankOne (rootGroup (rootOperatorFamily d4) K) (nd 2)) : adjointGroup d4 K) = _
  rw [this]

include hσ in
theorem twistedIncl_slLong_HSL (t : (fixedField σ)ˣ) :
    twistedIncl σ (slLong σ hσ (HSL t)) = rootDiagUnit d4
      (fun j => (Units.map (fixedField σ).subtype.toMonoidHom t) ^ d4.cartan (nd 2) j) := by
  rw [← torusElt_eq_rootDiagUnit, twistedIncl_apply, slLong_val, slLongE_HSL]
  rfl

include hσ in
theorem torus_conj_slLong {x : twistedGroup σ} {b : Fin d4.rank → Kˣ}
    (hx : twistedIncl σ x = rootDiagUnit d4 b) :
    ∃ s : (fixedField σ)ˣ, (((s : (fixedField σ)ˣ) : fixedField σ) : K) = (b (nd 2) : K) ∧
      ∀ C : SL(2, fixedField σ), x * slLong σ hσ C * x⁻¹ =
        slLong σ hσ (glConjSL (diagGL s) C) := by
  have hb2 : σ (b (nd 2) : K) = (b (nd 2) : K) := (torus_compat hx).2.2.2.symm
  have hne : ((b (nd 2) : Kˣ) : K) ≠ 0 := (b (nd 2)).ne_zero
  let s : (fixedField σ)ˣ := Units.mk0 ⟨(b (nd 2) : K), hb2⟩
    (fun h => hne (congrArg Subtype.val h))
  have hs : (((s : (fixedField σ)ˣ) : fixedField σ) : K) = (b (nd 2) : K) := rfl
  refine ⟨s, hs, ?_⟩
  have hroot := isRoot_single d4 (nd 2)
  refine conj_eq_of_generators (Φ := slLong σ hσ) (glConjSL (diagGL s)) (fun c => ?_)
    (fun c => ?_)
  · apply twistedIncl_injective σ
    rw [glConjSL_diag_uSL, map_mul, map_mul, map_inv, hx, twistedIncl_slLong_upper hσ,
      twistedIncl_slLong_upper hσ, rootDiagUnit_conj_xPar_td4 b hroot, rootChar_single_td4]
    congr 3
  · apply twistedIncl_injective σ
    rw [glConjSL_diag_vSL, map_mul, map_mul, map_inv, hx, twistedIncl_slLong_lower hσ,
      twistedIncl_slLong_lower hσ, rootDiagUnit_conj_xPar_td4 b (IsRoot.neg hroot),
      rootChar_neg_inv, rootChar_single_td4]
    congr 3
    rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
    simp [hs]

end Long

section Short

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem slShort_HSL (t : Kˣ) :
    ((slShort σ hσ (HSL t) : twistedGroup σ) : adjointGroup d4 K) = hShortHom σ t := by
  have hmem : torusElement d4 K (nd 0) t ∈
      rankOne (rootGroup (rootOperatorFamily d4) K) (nd 0) := torusElement_mem_rankOne (nd 0) t
  have hy : restrictEquiv (rootOperatorFamily d4) cartan_zero_two
      ⟨torusElement d4 K (nd 0) t, hmem⟩ = HSL t := by
    apply Subtype.ext
    show ((restrictHom (rootOperatorFamily d4) cartan_zero_two ⟨_, hmem⟩ :
      SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = _
    rw [restrictHom_torusElement cartan_zero_two, coe_HSL]
  have : (restrictEquiv (rootOperatorFamily d4) cartan_zero_two).symm (HSL t) =
      ⟨torusElement d4 K (nd 0) t, hmem⟩ := by
    rw [MulEquiv.symm_apply_eq, hy]
  simp only [slShort, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this, phiShortTw_val]
  exact phiShort_torusElement σ t

include hσ in
theorem twistedIncl_slShort_HSL (t : Kˣ) :
    twistedIncl σ (slShort σ hσ (HSL t)) = rootDiagUnit d4
      (fun j => t ^ d4.cartan (nd 0) j * (Units.map σ.toMonoidHom t) ^ d4.cartan (nd 1) j *
        (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom t)) ^ d4.cartan (nd 3) j) := by
  rw [twistedIncl_apply, slShort_HSL hσ, hShortHom_apply]
  show torusElt d4 K (nd 0) t * torusElt d4 K (nd 1) (Units.map σ.toMonoidHom t) *
    torusElt d4 K (nd 3) (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom t)) = _
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
    ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  rfl

include hσ in
theorem torus_conj_slShort {x : twistedGroup σ} {b : Fin d4.rank → Kˣ}
    (hx : twistedIncl σ x = rootDiagUnit d4 b) :
    ∃ s : Kˣ, (s : K) = (b (nd 0) : K) ∧
      ∀ C : SL(2, K), x * slShort σ hσ C * x⁻¹ = slShort σ hσ (glConjSL (diagGL s) C) := by
  obtain ⟨h1, h3, -, -⟩ := torus_compat hx
  refine ⟨b (nd 0), rfl, ?_⟩
  have hs1 : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
  have hsm : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  refine conj_eq_of_generators (Φ := slShort σ hσ) (glConjSL (diagGL (b (nd 0))))
    (fun c => ?_) (fun c => ?_)
  · apply twistedIncl_injective σ
    rw [glConjSL_diag_uSL, map_mul, map_mul, map_inv, hx, twistedIncl_slShort_upper hσ,
      twistedIncl_slShort_upper hσ]
    rw [conj_xOuter 1 1 (fun c => rootDiagUnit_conj_xPar_td4 b (isRoot_smul_single hs1 _) c)
      (fun c => rootDiagUnit_conj_xPar_td4 b (isRoot_smul_single hs1 _) c)
      (fun c => rootDiagUnit_conj_xPar_td4 b (isRoot_smul_single hs1 _) c) c (σ c) (σ (σ c))]
    simp only [one_smul, rootChar_single_td4, map_mul, h1, h3]
  · apply twistedIncl_injective σ
    rw [glConjSL_diag_vSL, map_mul, map_mul, map_inv, hx, twistedIncl_slShort_lower hσ,
      twistedIncl_slShort_lower hσ]
    rw [conj_xOuter (-1) (-1) (fun c => rootDiagUnit_conj_xPar_td4 b (isRoot_smul_single hsm _) c)
      (fun c => rootDiagUnit_conj_xPar_td4 b (isRoot_smul_single hsm _) c)
      (fun c => rootDiagUnit_conj_xPar_td4 b (isRoot_smul_single hsm _) c) c (σ c) (σ (σ c))]
    simp only [neg_one_smul, rootChar_neg_inv, rootChar_single_td4, Units.val_inv_eq_inv_val,
      map_mul, map_inv₀, h3, h1]

end Short

end CFSG.ClassicalInvolution.G2D4Models
