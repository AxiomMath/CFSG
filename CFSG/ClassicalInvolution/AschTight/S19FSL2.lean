module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4SL2Lin
public import CFSG.LocalAnalysis.ComponentInitial.SLTwoInvolution

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19F

open CFSG.LieType.Chevalley CFSG.ClassicalInvolution.G2D4Models Matrix
open scoped MatrixGroups

section Entrywise

variable {F : Type} [Field F]

theorem map_glConjSL (δ : F ≃+* F) (D : GL (Fin 2) F) (A : SL2 F) :
    SpecialLinearGroup.map δ.toRingHom (glConjSL D A) =
      glConjSL (GeneralLinearGroup.map δ.toRingHom D) (SpecialLinearGroup.map δ.toRingHom A) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe, glConjSL_coe, glConjSL_coe,
    SpecialLinearGroup.map_apply_coe,
    ← map_inv, RingHom.map_mul, RingHom.map_mul]
  rfl

theorem glConjSL_of_mem_center {Z : GL (Fin 2) F} (hZ : Z ∈ Subgroup.center (GL (Fin 2) F))
    (A : SL2 F) : glConjSL Z A = A := by
  apply Subtype.ext
  have hc : (Z : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F) * Z :=
    congrArg Units.val ((Subgroup.mem_center_iff.mp hZ) (SpecialLinearGroup.toGL A)).symm
  rw [glConjSL_coe, hc, Matrix.mul_assoc, gl_mul_inv, Matrix.mul_one]

theorem glConjSL_scalar (s : Fˣ) (A : SL2 F) :
    glConjSL (GeneralLinearGroup.scalar (Fin 2) s) A = A :=
  glConjSL_of_mem_center (by rw [GeneralLinearGroup.center_eq_range_scalar]; exact ⟨s, rfl⟩) A

theorem glConjSL_scalar_mul (s : Fˣ) (D : GL (Fin 2) F) (A : SL2 F) :
    glConjSL (GeneralLinearGroup.scalar (Fin 2) s * D) A = glConjSL D A := by
  rw [glConjSL_mul, glConjSL_scalar]

theorem glConjSL_neg_one (D : GL (Fin 2) F) : glConjSL D (-1) = -1 := by
  apply Subtype.ext
  rw [glConjSL_coe]
  change (D : Matrix (Fin 2) (Fin 2) F) * (-1 : Matrix (Fin 2) (Fin 2) F) *
    ((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = -1
  rw [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, gl_mul_inv]

end Entrywise

section Frobenius

variable {F : Type} [Field F] [Finite F] {r : ℕ} (hF : Nat.card F = r ^ 2) {δ : F ≃+* F}
  (hδ : ∀ c, δ c = c ^ r)

include hF hδ

theorem frob_frob (c : F) : δ (δ c) = c := by
  have := Fintype.ofFinite F
  rw [hδ, hδ, ← pow_mul, ← sq, ← hF, Nat.card_eq_fintype_card, FiniteField.pow_card]

omit hδ in
theorem two_le_of_card_sq : 2 ≤ r := by
  have := Fintype.ofFinite F
  have h1 : 1 < Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  rw [hF] at h1
  rcases Nat.lt_or_ge r 2 with h | h
  · interval_cases r <;> simp at h1
  · exact h

omit hδ in
theorem orderOf_generator {γ : Fˣ} (hγ : ∀ x, x ∈ Subgroup.zpowers γ) :
    orderOf γ = r ^ 2 - 1 := by
  classical
  have := Fintype.ofFinite F
  rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_eq_fintype_card, Fintype.card_units,
    ← Nat.card_eq_fintype_card, hF]

theorem exists_frob_ne : ∃ c, δ c ≠ c := by
  classical
  have h2 := two_le_of_card_sq hF
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Fˣ)
  refine ⟨γ, fun h => ?_⟩
  rw [hδ] at h
  have h1 : γ ^ (r - 1) = 1 := by
    apply Units.ext
    have e : (γ : F) ^ (r - 1) * γ = 1 * γ := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul, h]
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact mul_right_cancel₀ γ.ne_zero e
  have hdvd := orderOf_dvd_of_pow_eq_one h1
  rw [orderOf_generator hF hγ] at hdvd
  have hle := Nat.le_of_dvd (by omega) hdvd
  have h3 : r ^ 2 = r * r := sq r
  have h4 : r * 2 ≤ r * r := Nat.mul_le_mul_left r h2
  omega

theorem exists_mul_frob_eq {μ : F} (hμ : μ ≠ 0) (hμδ : δ μ = μ) :
    ∃ ν : F, ν ≠ 0 ∧ ν * δ ν = μ := by
  classical
  have h2 := two_le_of_card_sq hF
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hγ (Units.mk0 μ hμ))
  have hμ1 : (Units.mk0 μ hμ) ^ (r - 1) = 1 := by
    apply Units.ext
    have e : μ ^ (r - 1) * μ = 1 * μ := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul, ← hδ, hμδ]
    rw [Units.val_pow_eq_pow_val, Units.val_one, Units.val_mk0]
    exact mul_right_cancel₀ hμ e
  have hzk : γ ^ (k * ((r - 1 : ℕ) : ℤ)) = 1 := by
    rw [_root_.zpow_mul, hk, zpow_natCast, hμ1]
  have hdvd := orderOf_dvd_iff_zpow_eq_one.mpr hzk
  rw [orderOf_generator hF hγ] at hdvd
  have hfac : ((r ^ 2 - 1 : ℕ) : ℤ) = ((r - 1 : ℕ) : ℤ) * ((r + 1 : ℕ) : ℤ) := by
    have h1 : 1 ≤ r ^ 2 := by nlinarith
    push_cast [h1, (by omega : 1 ≤ r)]
    ring
  rw [hfac, mul_comm k] at hdvd
  have hne : ((r - 1 : ℕ) : ℤ) ≠ 0 := by
    have : 1 ≤ r - 1 := by omega
    positivity
  obtain ⟨m, hm⟩ := (Int.dvd_of_mul_dvd_mul_left hne hdvd : ((r + 1 : ℕ) : ℤ) ∣ k)
  refine ⟨((γ ^ m : Fˣ) : F), Units.ne_zero _, ?_⟩
  rw [hδ, ← pow_succ', ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← _root_.zpow_mul,
    mul_comm m, ← hm, hk, Units.val_mk0]

end Frobenius

section Hilbert

variable {F : Type} [Field F]

@[expose] def semilinApply (A : GL (Fin 2) F) (δ : F ≃+* F) (v : Fin 2 → F) : Fin 2 → F :=
  Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) F) (fun i => δ (v i))

theorem semilinApply_add (A : GL (Fin 2) F) (δ : F ≃+* F) (v w : Fin 2 → F) :
    semilinApply A δ (v + w) = semilinApply A δ v + semilinApply A δ w := by
  ext i
  fin_cases i <;> simp [semilinApply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem semilinApply_smul (A : GL (Fin 2) F) (δ : F ≃+* F) (a : F) (v : Fin 2 → F) :
    semilinApply A δ (a • v) = δ a • semilinApply A δ v := by
  ext i
  fin_cases i <;> simp [semilinApply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem semilinApply_involutive (A : GL (Fin 2) F) (δ : F ≃+* F) (hδδ : ∀ c, δ (δ c) = c)
    (hA : A * GeneralLinearGroup.map δ.toRingHom A = 1) :
    Function.Involutive (semilinApply A δ) := by
  intro v
  have hmat : (A : Matrix (Fin 2) (Fin 2) F) *
      δ.toRingHom.mapMatrix (A : Matrix (Fin 2) (Fin 2) F) = 1 :=
    congrArg Units.val hA
  ext i
  change Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) F)
      (fun j => δ (Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) F) (fun k => δ (v k)) j)) i = v i
  have hmap (j : Fin 2) : δ (Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) F) (fun k => δ (v k)) j) =
      Matrix.mulVec (δ.toRingHom.mapMatrix (A : Matrix (Fin 2) (Fin 2) F)) v j := by
    simpa [Function.comp_def, hδδ] using
      δ.toRingHom.map_mulVec (A : Matrix (Fin 2) (Fin 2) F) (fun k => δ (v k)) j
  simp_rw [hmap]
  rw [Matrix.mulVec_mulVec, hmat, Matrix.one_mulVec]

theorem exists_semilin_fixed_basis (δ : F ≃+* F) (hδδ : ∀ c, δ (δ c) = c)
    (hδne : ∃ c, δ c ≠ c) (htwo : (2 : F) ≠ 0) (T : (Fin 2 → F) ≃+ (Fin 2 → F))
    (hTinvol : Function.Involutive T) (hTsmul : ∀ (a : F) (v : Fin 2 → F), T (a • v) = δ a • T v) :
    ∃ b : Module.Basis (Fin 2) F (Fin 2 → F), ∀ j, T (b j) = b j := by
  classical
  obtain ⟨β, hβ⟩ := hδne
  set a : F := β - δ β with ha_def
  have ha_ne : a ≠ 0 := fun ha => hβ (sub_eq_zero.mp ha).symm
  have hδa : δ a = -a := by rw [ha_def, map_sub, hδδ]; abel
  set v0 : Fin 2 → F := Pi.single 0 1 with hv0_def
  have hv0_ne : v0 ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp [v0] at h0
  set s0 : Fin 2 → F := v0 + T v0 with hs0_def
  have hTs0 : T s0 = s0 := by rw [hs0_def, map_add, hTinvol]; exact add_comm _ _
  set w0 : Fin 2 → F := if s0 = 0 then a • v0 else s0 with hw0_def
  have hTw0 : T w0 = w0 := by
    rw [hw0_def]
    split_ifs with hs0
    · have hTv0 : T v0 = -v0 := by
        apply add_left_cancel (a := v0)
        rw [← hs0_def, hs0, add_neg_cancel]
      rw [hTsmul, hδa, hTv0, smul_neg, neg_smul, neg_neg]
    · exact hTs0
  have hw0_ne : w0 ≠ 0 := by
    rw [hw0_def]
    split_ifs with hs0
    · exact smul_ne_zero ha_ne hv0_ne
    · exact hs0
  set z : Fin 2 → F := if w0 0 = 0 then Pi.single 0 1 else Pi.single 1 1 with hz_def
  have hz_not_span : z ∉ F ∙ w0 := by
    rw [Submodule.mem_span_singleton]
    rintro ⟨c, hc⟩
    by_cases hw00 : w0 0 = 0
    · have hw01 : w0 1 ≠ 0 := by
        intro hw01
        apply hw0_ne
        funext i
        fin_cases i <;> assumption
      have hc1 := congrFun hc 1
      have hc0 := congrFun hc 0
      simp [z, hw00, Pi.smul_apply, hw01] at hc1 hc0
    · have hc0 := congrFun hc 0
      have hc1 := congrFun hc 1
      simp [z, Pi.smul_apply, hw00] at hc0 hc1
      rw [hc0, zero_mul] at hc1
      exact zero_ne_one hc1
  set s1 : Fin 2 → F := z + T z with hs1_def
  have hTs1 : T s1 = s1 := by rw [hs1_def, map_add, hTinvol]; exact add_comm _ _
  set half : F := (2 : F)⁻¹ with hhalf_def
  have hhalf : (2 : F) * half = 1 := mul_inv_cancel₀ htwo
  have hδhalf : δ half = half := by rw [hhalf_def, map_inv₀, map_ofNat]
  set z' : Fin 2 → F := z - half • s1 with hz'_def
  have hz'_not_span (hs1span : s1 ∈ F ∙ w0) : z' ∉ F ∙ w0 := by
    intro hz'span
    apply hz_not_span
    have hsum : z' + half • s1 ∈ F ∙ w0 :=
      (F ∙ w0).add_mem hz'span ((F ∙ w0).smul_mem half hs1span)
    simpa [z', sub_add_cancel] using hsum
  have hTz' : T z' = -z' := by
    rw [hz'_def, map_sub, hTsmul, hδhalf, hTs1, hs1_def]
    ext i
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul]
    have htwohalf : half + half = 1 := by rw [← two_mul]; exact hhalf
    linear_combination (-(z i + T z i)) * htwohalf
  set w1 : Fin 2 → F := if s1 ∈ F ∙ w0 then a • z' else s1 with hw1_def
  have hTw1 : T w1 = w1 := by
    rw [hw1_def]
    split_ifs with hs1span
    · rw [hTsmul, hδa, hTz', smul_neg, neg_smul, neg_neg]
    · exact hTs1
  have hw1_not_span : w1 ∉ F ∙ w0 := by
    rw [hw1_def]
    split_ifs with hs1span
    · intro haw
      apply hz'_not_span hs1span
      have hmem := (F ∙ w0).smul_mem a⁻¹ haw
      simpa [smul_smul, ha_ne] using hmem
    · exact hs1span
  set w : Fin 2 → (Fin 2 → F) := ![w0, w1] with hw_def
  have hwLI : LinearIndependent F w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hsum : g 0 • w0 + g 1 • w1 = 0 := by simpa [w, Fin.sum_univ_two] using hg
    have hg1 : g 1 = 0 := by
      by_contra hg1
      apply hw1_not_span
      rw [Submodule.mem_span_singleton]
      refine ⟨-(g 1)⁻¹ * g 0, ?_⟩
      have hscaled := congrArg (fun v : Fin 2 → F => (g 1)⁻¹ • v) hsum
      have hscaled' : ((g 1)⁻¹ * g 0) • w0 + w1 = 0 := by
        simpa [smul_add, smul_smul, hg1] using hscaled
      have hw1eq : w1 = -(((g 1)⁻¹ * g 0) • w0) := eq_neg_of_add_eq_zero_right hscaled'
      simpa [neg_smul] using hw1eq.symm
    have hg0 : g 0 = 0 := by
      rw [hg1, zero_smul, add_zero] at hsum
      exact (smul_eq_zero.mp hsum).resolve_right hw0_ne
    fin_cases i
    · exact hg0
    · exact hg1
  have hcard : Fintype.card (Fin 2) = Module.finrank F (Fin 2 → F) := by simp
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hwLI hcard, fun j => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  fin_cases j
  · exact hTw0
  · exact hTw1

theorem exists_gl_frob_coboundary (δ : F ≃+* F) (hδδ : ∀ c, δ (δ c) = c)
    (hδne : ∃ c, δ c ≠ c) (htwo : (2 : F) ≠ 0) (A : GL (Fin 2) F)
    (hA : A * GeneralLinearGroup.map δ.toRingHom A = 1) :
    ∃ C : GL (Fin 2) F, A * GeneralLinearGroup.map δ.toRingHom C = C := by
  classical
  have hTinvol := semilinApply_involutive A δ hδδ hA
  let T : (Fin 2 → F) ≃+ (Fin 2 → F) :=
    { toFun := semilinApply A δ
      invFun := semilinApply A δ
      left_inv := hTinvol
      right_inv := hTinvol
      map_add' := semilinApply_add A δ }
  obtain ⟨b, hb⟩ :=
    exists_semilin_fixed_basis δ hδδ hδne htwo T hTinvol (semilinApply_smul A δ)
  let L : LinearMap.GeneralLinearGroup F (Fin 2 → F) :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv b.equivFun.symm
  let C : GL (Fin 2) F := Matrix.GeneralLinearGroup.toLin.symm L
  have hCcol (i j : Fin 2) : (C : Matrix (Fin 2) (Fin 2) F) i j = b j i := by
    let ej : Fin 2 → F := Pi.single j 1
    have hfun : Matrix.mulVec (C : Matrix (Fin 2) (Fin 2) F) ej = b j := by
      calc Matrix.mulVec (C : Matrix (Fin 2) (Fin 2) F) ej =
            (Matrix.GeneralLinearGroup.toLin C : (Fin 2 → F) → Fin 2 → F) ej := rfl
        _ = (L : (Fin 2 → F) → Fin 2 → F) ej := by
          rw [(Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := F)).apply_symm_apply]
        _ = b j := by simp [L, ej, LinearMap.GeneralLinearGroup.ofLinearEquiv]
    rw [Matrix.mulVec_single_one] at hfun
    exact congrFun hfun i
  refine ⟨C, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have hfix := congrFun (hb j) i
  change Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) F) (fun k => δ (b j k)) i = b j i at hfix
  simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, hCcol, semilinApply] using hfix

end Hilbert

section Pair

variable {F : Type} [Field F]

theorem slMap_slMap {δ : F ≃+* F} (hδδ : ∀ c, δ (δ c) = c) (A : SL2 F) :
    SpecialLinearGroup.map δ.toRingHom (SpecialLinearGroup.map δ.toRingHom A) = A := by
  apply Subtype.ext
  ext i j
  simp [hδδ]

theorem slMap_quatI (δ : F ≃+* F) : SpecialLinearGroup.map δ.toRingHom quatI = quatI := by
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quatI]

theorem slMap_quatJ (δ : F ≃+* F) {a b : F} (h : a ^ 2 + b ^ 2 = -1) (ha : δ a = a)
    (hb : δ b = b) : SpecialLinearGroup.map δ.toRingHom (quatJ h) = quatJ h := by
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quatJ, ha, hb]

theorem two_ne_zero_of_odd [Finite F] (hodd : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  classical
  have := Fintype.ofFinite F
  refine Ring.two_ne_zero fun h => ?_
  rw [Nat.card_eq_fintype_card, Nat.odd_iff, FiniteField.even_card_iff_char_two.1 h] at hodd
  exact zero_ne_one hodd

theorem odd_card_of_two_ne_zero [Finite F] (h2 : (2 : F) ≠ 0) : Odd (Nat.card F) := by
  classical
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Nat.odd_iff]
  refine FiniteField.odd_card_of_char_ne_two fun hc => h2 ?_
  have h := ringChar.Nat.cast_ringChar (R := F)
  rw [hc] at h
  exact_mod_cast h

theorem odd_card_fixField [Finite F] (hodd : Odd (Nat.card F)) (δ : F ≃+* F) :
    Odd (Nat.card (RingHom.eqLocusField δ.toRingHom (RingHom.id F))) := by
  refine odd_card_of_two_ne_zero fun h => two_ne_zero_of_odd hodd ?_
  have := congrArg (RingHom.eqLocusField δ.toRingHom (RingHom.id F)).subtype h
  rwa [map_ofNat, map_zero] at this

theorem scalar_of_glConjSL_eq [Finite F] (hodd : Odd (Nat.card F)) {N : GL (Fin 2) F}
    (hN : ∀ A : SL2 F, glConjSL N A = A) :
    ∃ μ : F, (N : Matrix (Fin 2) (Fin 2) F) = μ • 1 := by
  obtain ⟨a, b, hab⟩ := exists_sq_add_sq_eq_neg_one hodd
  have hcomm : ∀ X : SL2 F, (N : Matrix (Fin 2) (Fin 2) F) * X = X * N := by
    intro X
    have h := congrArg Subtype.val (hN X)
    rw [glConjSL_coe] at h
    calc (N : Matrix (Fin 2) (Fin 2) F) * X =
          (N : Matrix (Fin 2) (Fin 2) F) * X * ((N⁻¹ : GL (Fin 2) F) * N : GL (Fin 2) F) := by
            rw [inv_mul_cancel, Units.val_one, Matrix.mul_one]
      _ = ((N : Matrix (Fin 2) (Fin 2) F) * X * ((N⁻¹ : GL (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F)) * N := by
            rw [Units.val_mul, Matrix.mul_assoc _ _ (N : Matrix (Fin 2) (Fin 2) F)]
      _ = X * N := by rw [h]
  exact scalar_of_commute_quat hab (two_ne_zero_of_odd hodd) (hcomm quatI) (hcomm (quatJ hab))

variable [Finite F] {r : ℕ} (hF : Nat.card F = r ^ 2) {δ : F ≃+* F} (hδ : ∀ c, δ c = c ^ r)

include hF hδ

theorem exists_fixed_quaternion_pair (hodd : Odd (Nat.card F)) (D : GL (Fin 2) F)
    (hD : ∀ A : SL2 F, glConjSL D (SpecialLinearGroup.map δ.toRingHom
      (glConjSL D (SpecialLinearGroup.map δ.toRingHom A))) = A) :
    ∃ x y : SL2 F, x * x = -1 ∧ y * y = -1 ∧ x * y = -1 * (y * x) ∧
      glConjSL D (SpecialLinearGroup.map δ.toRingHom x) = x ∧
      glConjSL D (SpecialLinearGroup.map δ.toRingHom y) = y := by
  classical
  have hδδ := frob_frob hF hδ
  have htwo := two_ne_zero_of_odd hodd
  have hN : ∀ A : SL2 F, glConjSL (D * GeneralLinearGroup.map δ.toRingHom D) A = A := by
    intro A
    have h := hD A
    rwa [map_glConjSL, slMap_slMap hδδ, ← glConjSL_mul] at h
  obtain ⟨μ, hμ⟩ := scalar_of_glConjSL_eq hodd hN
  set Dm : Matrix (Fin 2) (Fin 2) F := (D : Matrix (Fin 2) (Fin 2) F) with hDm
  set Di : Matrix (Fin 2) (Fin 2) F := ((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
    with hDi
  have hDiD : Di * Dm = 1 := gl_inv_mul D
  have hmm : ∀ X : Matrix (Fin 2) (Fin 2) F,
      δ.toRingHom.mapMatrix (δ.toRingHom.mapMatrix X) = X := fun X => by ext i j; simp [hδδ]
  have hsm : ∀ (c : F) (X : Matrix (Fin 2) (Fin 2) F),
      δ.toRingHom.mapMatrix (c • X) = δ c • δ.toRingHom.mapMatrix X := fun c X => by
    ext i j
    simp
  have hsc : ∀ c : F, δ.toRingHom.mapMatrix (c • (1 : Matrix (Fin 2) (Fin 2) F)) =
      δ c • (1 : Matrix (Fin 2) (Fin 2) F) := fun c => by rw [hsm, RingHom.map_one]
  have hDD : Dm * δ.toRingHom.mapMatrix Dm = μ • 1 := hμ
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hDD
    have h1 : Dm * δ.toRingHom.mapMatrix Dm *
        δ.toRingHom.mapMatrix Di = Dm := by
      rw [Matrix.mul_assoc, ← RingHom.map_mul, gl_mul_inv, RingHom.map_one, Matrix.mul_one]
    rw [hDD, Matrix.zero_mul] at h1
    have h2 : Di * Dm = 0 := by rw [← h1, Matrix.mul_zero]
    rw [hDiD] at h2
    have h00 := congrFun (congrFun h2 0) 0
    simp at h00
  have hδμ : δ μ = μ := by
    have e1 : δ.toRingHom.mapMatrix Dm * Dm = δ μ • 1 := by
      have := congrArg δ.toRingHom.mapMatrix hDD
      rwa [RingHom.map_mul, hmm, hsc] at this
    have e2 : δ.toRingHom.mapMatrix Dm * Dm = μ • 1 := by
      calc δ.toRingHom.mapMatrix Dm * Dm = Di * (Dm * δ.toRingHom.mapMatrix Dm) * Dm := by
            rw [← Matrix.mul_assoc, hDiD, Matrix.one_mul]
        _ = μ • 1 := by rw [hDD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hDiD]
    have h00 := congrFun (congrFun (e1.symm.trans e2) 0) 0
    simpa using h00
  obtain ⟨ν, hν0, hνμ⟩ := exists_mul_frob_eq hF hδ hμ0 hδμ
  set u : Fˣ := Units.mk0 ν hν0 with hu
  set D₁ : GL (Fin 2) F := GeneralLinearGroup.scalar (Fin 2) u⁻¹ * D with hD₁def
  have hscal : ∀ (w : Fˣ) (X : GL (Fin 2) F),
      ((GeneralLinearGroup.scalar (Fin 2) w * X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (w : F) • (X : Matrix (Fin 2) (Fin 2) F) := fun w X => by
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, smul_eq_diagonal_mul]
  have hD₁ : D₁ * GeneralLinearGroup.map δ.toRingHom D₁ = 1 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_one]
    change ((GeneralLinearGroup.scalar (Fin 2) u⁻¹ * D : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      δ.toRingHom.mapMatrix ((GeneralLinearGroup.scalar (Fin 2) u⁻¹ * D : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = 1
    rw [hscal, hsm, Matrix.smul_mul, Matrix.mul_smul, hDD, smul_smul, smul_smul]
    have hc : ((u⁻¹ : Fˣ) : F) * δ ((u⁻¹ : Fˣ) : F) * μ = 1 := by
      rw [Units.val_inv_eq_inv_val, hu, Units.val_mk0, map_inv₀, ← hνμ]
      have hδν : δ ν ≠ 0 := by rwa [map_ne_zero]
      field_simp
    rw [hc, one_smul]
  obtain ⟨C, hC⟩ := exists_gl_frob_coboundary δ hδδ (exists_frob_ne hF hδ) htwo D₁ hD₁
  have hDC : D * GeneralLinearGroup.map δ.toRingHom C =
      GeneralLinearGroup.scalar (Fin 2) u * C := by
    have hD' : D = GeneralLinearGroup.scalar (Fin 2) u * D₁ := by
      rw [hD₁def, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    rw [hD', mul_assoc, hC]
  have hfix : ∀ Y : SL2 F, SpecialLinearGroup.map δ.toRingHom Y = Y →
      glConjSL D (SpecialLinearGroup.map δ.toRingHom (glConjSL C Y)) = glConjSL C Y := by
    intro Y hY
    rw [map_glConjSL, hY, ← glConjSL_mul, hDC, glConjSL_scalar_mul]
  obtain ⟨a, b, hab⟩ := exists_sq_add_sq_eq_neg_one (odd_card_fixField hodd δ)
  have hab' : (a : F) ^ 2 + (b : F) ^ 2 = -1 := by
    have := congrArg (RingHom.eqLocusField δ.toRingHom (RingHom.id F)).subtype hab
    rwa [map_add, map_pow, map_pow, map_neg, map_one] at this
  have ha : δ (a : F) = a := a.2
  have hb : δ (b : F) = b := b.2
  refine ⟨glConjSL C quatI, glConjSL C (quatJ hab'), ?_, ?_, ?_, hfix _ (slMap_quatI δ),
    hfix _ (slMap_quatJ δ hab' ha hb)⟩
  · rw [← map_mul, quatI_mul_self, glConjSL_neg_one]
  · rw [← map_mul, quatJ_mul_self, glConjSL_neg_one]
  · rw [← map_mul, quatI_mul_quatJ, map_mul, glConjSL_neg_one, map_mul]

theorem exists_fixed_quaternion_of_chart (hodd : Odd (Nat.card F)) {C : Type*} [Group C]
    (β : MulAut C) (hβ2 : ∀ x, β (β x) = x) (Φ : SL2 F →* C) (hΦ : Function.Injective Φ)
    (hβΦ : ∀ A, β (Φ A) = Φ (SpecialLinearGroup.map δ.toRingHom A)) (g : C)
    (hlin : LinAct Φ (g⁻¹ * β g)) :
    ∃ P : Subgroup C, IsPGroup 2 P ∧ P ≤ Φ.range.map (MulAut.conj g).toMonoidHom ∧
      (∀ x ∈ P, β x = x) ∧ ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x := by
  obtain ⟨D, hD⟩ := hlin
  have hβc : ∀ A, β (g * Φ A * g⁻¹) =
      g * Φ (glConjSL D (SpecialLinearGroup.map δ.toRingHom A)) * g⁻¹ := by
    intro A
    rw [← hD, map_mul, map_mul, map_inv, hβΦ]
    group
  have hθ : ∀ A : SL2 F, glConjSL D (SpecialLinearGroup.map δ.toRingHom
      (glConjSL D (SpecialLinearGroup.map δ.toRingHom A))) = A := by
    intro A
    apply hΦ
    have h := hβc (glConjSL D (SpecialLinearGroup.map δ.toRingHom A))
    rw [← hβc, hβ2] at h
    exact (mul_left_cancel (mul_right_cancel h)).symm
  obtain ⟨x₀, y₀, hx2, hy2, hxy, hxf, hyf⟩ := exists_fixed_quaternion_pair hF hδ hodd D hθ
  set e : SL2 F →* C := (MulAut.conj g).toMonoidHom.comp Φ with he
  have he_apply : ∀ A, e A = g * Φ A * g⁻¹ := fun A => rfl
  have he_inj : Function.Injective e := (MulAut.conj g).injective.comp hΦ
  have hchar : ringChar F ≠ 2 := fun hc => two_ne_zero_of_odd hodd (by
    have h := ringChar.Nat.cast_ringChar (R := F)
    rw [hc] at h
    exact_mod_cast h)
  have hz1 : e (-1) ≠ 1 := fun h =>
    CFSG.LocalAnalysis.ComponentInitial.sl2_neg_one_ne_one hchar
      (he_inj (h.trans (map_one e).symm))
  have hn1 : (-1 : SL2 F) ^ 2 = 1 := by
    apply Subtype.ext
    simp [sq]
  have hz2 : e (-1) ^ 2 = 1 := by rw [← map_pow, hn1, map_one]
  have hx : e x₀ ^ 2 = e (-1) := by rw [← map_pow, sq, hx2]
  have hy : e y₀ ^ 2 = e (-1) := by rw [← map_pow, sq, hy2]
  have hxy' : e x₀ * e y₀ = e (-1) * (e y₀ * e x₀) := by rw [← map_mul, hxy, map_mul, map_mul]
  obtain ⟨H, hxH, hyH, ⟨iso⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.exists_quaternion_subgroup_of_anticommuting hz1 hz2 hx hy
      hxy'
  have hH2 : IsPGroup 2 H := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [← Nat.card_congr iso.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  set P : Subgroup C := Subgroup.closure ({e x₀, e y₀} : Set C) with hP
  have hPH : P ≤ H := by
    rw [hP, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    exacts [hxH, hyH]
  have hfixP : P ≤ β.toMonoidHom.eqLocus (MonoidHom.id C) := by
    rw [hP, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · change β (e x₀) = e x₀
      rw [he_apply, hβc, hxf]
    · change β (e y₀) = e y₀
      rw [he_apply, hβc, hyf]
  refine ⟨P, hH2.to_le hPH, ?_, fun x hx => hfixP hx, e x₀, Subgroup.subset_closure (by simp),
    e y₀, Subgroup.subset_closure (by simp), fun h => hz1 ?_⟩
  · rw [hP, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    exacts [⟨Φ x₀, ⟨x₀, rfl⟩, rfl⟩, ⟨Φ y₀, ⟨y₀, rfl⟩, rfl⟩]
  · rw [hxy'] at h
    exact mul_eq_right.mp h

end Pair

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19F
