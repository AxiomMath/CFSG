module

public import CFSG.ClassicalInvolution.AschTight.S19FAut
public import CFSG.Quasithin.Background.G2UAdjoint

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19F

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.Generic Matrix
open scoped MatrixGroups

section ReeAut

@[expose] noncomputable def g2ExcAut (K : Type) [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.G2.prime] : MulAut ↥(adjointGroup .G2 K) :=
  CFSG.LieType.Ree.ReeTag.G2.finiteExceptionalAut K

@[expose] noncomputable def g2FrobAut (K : Type) [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.G2.prime] : MulAut ↥(adjointGroup .G2 K) :=
  CFSG.LieType.Ree.ReeTag.G2.finiteFrobeniusAut K

@[expose] noncomputable def g2ReeAut (K : Type) [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.G2.prime] (b : ℕ) : MulAut ↥(adjointGroup .G2 K) :=
  CFSG.LieType.Ree.ReeTag.G2.finiteReeAut K b

variable {K : Type} [Field K] [Finite K] [CharP K CFSG.LieType.Ree.ReeTag.G2.prime]

theorem g2ReeAut_eq (b : ℕ) : g2ReeAut K b = g2ExcAut K * g2FrobAut K ^ b :=
  rfl

theorem map_range_g2Chart_frobenius_pow (b : ℕ) (i : Fin Tag.G2.rank) :
    (g2Chart K i).range.map (g2FrobAut K ^ b).toMonoidHom = (g2Chart K i).range := by
  have : CharP K 3 := ‹CharP K CFSG.LieType.Ree.ReeTag.G2.prime›
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set σ : K ≃+* K := RingEquiv.ofBijective (iterateFrobenius K 3 b)
    ⟨RingHom.injective _, Finite.surjective_of_injective (RingHom.injective _)⟩ with hσdef
  have hσ : ∀ c, σ c = c ^ CFSG.LieType.Ree.ReeTag.G2.prime ^ b := fun c =>
    iterateFrobenius_def 3 b c
  have hEq : exactNormalAut .G2 K 1 σ 0 = g2FrobAut K ^ b :=
    exactNormalAut_one_eq_finiteFrobeniusAut_pow CFSG.LieType.Ree.ReeTag.G2 hσ
  have hα : ∀ h : adjointGroup .G2 K, ((g2FrobAut K ^ b) h : ModGL .G2 K) =
      ((1 : adjointGroup .G2 K) : ModGL .G2 K) * Units.map (entrywiseHom σ.toRingHom)
        (h : ModGL .G2 K) * ((1 : adjointGroup .G2 K) : ModGL .G2 K)⁻¹ := fun h => by
    rw [← hEq, coe_exactNormalAut_zero, rootDiagUnit_one, Subgroup.coe_one]
  rw [map_range_g2Chart_of_entrywise σ _ 1 hα i, conjSub_one]

theorem map_range_g2Chart_g2ReeAut (b : ℕ) (i : Fin Tag.G2.rank) :
    (g2Chart K i).range.map (g2ReeAut K b).toMonoidHom =
      (g2Chart K (CFSG.LieType.Ree.ReeTag.G2.perm i)).range := by
  have hφ : (g2Chart K i).range.map (g2ExcAut K).toMonoidHom =
      (g2Chart K (CFSG.LieType.Ree.ReeTag.G2.perm i)).range :=
    map_range_g2Chart_finiteExceptionalAut i
  rw [show (g2ReeAut K b).toMonoidHom = (g2ExcAut K).toMonoidHom.comp
      (g2FrobAut K ^ b).toMonoidHom from rfl, ← Subgroup.map_map,
    map_range_g2Chart_frobenius_pow, hφ]

end ReeAut

section Cube

variable {F : Type} [Field F]

theorem exists_conj_uSL_of_cube (h3 : (3 : F) = 0) {A : SL2 F} (hA : A ^ 3 = 1)
    (hA1 : A ≠ 1) : ∃ (B : SL2 F) (c : F), c ≠ 0 ∧ A = B * uSL c * B⁻¹ := by
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d : F, (A : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : a * d - b * c = 1 := by
    have h := A.2
    rw [hM, Matrix.det_fin_two_of] at h
    exact h
  have hcube : (A : Matrix (Fin 2) (Fin 2) F) * A * A = 1 := by
    have h := congrArg (fun X : SL2 F => (X : Matrix (Fin 2) (Fin 2) F)) hA
    simpa [pow_succ, Matrix.SpecialLinearGroup.coe_mul] using h
  rw [hM] at hcube
  have e00 := congrFun (congrFun hcube 0) 0
  have e11 := congrFun (congrFun hcube 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e11
  have htr3 : (a + d - 2) ^ 3 = 0 := by
    linear_combination e00 + e11 + 3 * (a + d) * hdet +
      (-2 * (a + d) ^ 2 + 5 * (a + d) - 2) * h3
  have htr : a + d = 2 := by
    have := pow_eq_zero_iff (n := 3) (by norm_num) |>.mp htr3
    linear_combination this
  by_cases hb : b = 0
  ·
    have ha1 : (a - 1) ^ 2 = 0 := by linear_combination a * htr - hdet - c * hb
    have ha : a = 1 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ha1
      linear_combination this
    have hd : d = 1 := by linear_combination htr - ha
    have hAv : A = vSL c := by
      apply Subtype.ext
      rw [hM, coe_vSL, hb, ha, hd]
    have hc : c ≠ 0 := by
      rintro rfl
      apply hA1
      rw [hAv]
      apply Subtype.ext
      rw [coe_vSL]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    exact ⟨WSL, -c, neg_ne_zero.mpr hc, by rw [hAv, vSL_eq]⟩
  ·
    have hBdet : (!![b, 0; d - 1, b⁻¹] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      rw [Matrix.det_fin_two_of, mul_inv_cancel₀ hb, zero_mul, sub_zero]
    obtain ⟨B, hB⟩ : ∃ B : SL2 F, (B : Matrix (Fin 2) (Fin 2) F) = !![b, 0; d - 1, b⁻¹] :=
      ⟨⟨_, hBdet⟩, rfl⟩
    refine ⟨B, b⁻¹, inv_ne_zero hb, ?_⟩
    rw [eq_mul_inv_iff_mul_eq]
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    show ((A : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F)) i j =
      ((B : Matrix (Fin 2) (Fin 2) F) * (uSL b⁻¹ : SL2 F)) i j
    rw [hM, coe_uSL, hB]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination b * htr
    · linear_combination d * htr - hdet
    · field_simp
      ring

end Cube

section Module

open CFSG.Quasithin.G2U

theorem xMat_zero_sq_zmod (a b : Fin 14) :
    ((XMat (ZMod 3) (ix 0) 1 - 1) * (XMat (ZMod 3) (ix 0) 1 - 1)) a b =
      if a = 5 ∧ b = 8 then 2 else 0 := by
  revert a b
  decide +kernel

theorem xMat_one_sq_zmod :
    ((XMat (ZMod 3) (ix 1) 1 - 1) * (XMat (ZMod 3) (ix 1) 1 - 1)) 2 5 = 2 ∧
      ((XMat (ZMod 3) (ix 1) 1 - 1) * (XMat (ZMod 3) (ix 1) 1 - 1)) 2 9 = 0 ∧
      ((XMat (ZMod 3) (ix 1) 1 - 1) * (XMat (ZMod 3) (ix 1) 1 - 1)) 4 9 = 2 := by
  decide +kernel

variable {K : Type} [Field K] [CharP K 3]

theorem xMat_sq_eq_map (i : Fin Tag.G2.rank) :
    (XMat K i 1 - 1) * (XMat K i 1 - 1) =
      ((XMat (ZMod 3) i 1 - 1) * (XMat (ZMod 3) i 1 - 1)).map (ZMod.castHom (dvd_refl 3) K) := by
  have h := map_XMat (ZMod.castHom (dvd_refl 3) K) i 1
  rw [map_one] at h
  rw [← h]
  change _ = (ZMod.castHom (dvd_refl 3) K).mapMatrix _
  rw [RingHom.map_mul, RingHom.map_sub, RingHom.map_one]
  rfl

theorem not_conj_xUnit_zero_one (g : ModGL .G2 K) :
    g * xUnit .G2 K (ix 0) 1 * g⁻¹ ≠ xUnit .G2 K (ix 1) 1 := by
  intro h
  have h2 : (2 : K) ≠ 0 := by
    intro h2
    have h1 : (1 : K) = 0 := by
      have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
      linear_combination h3 - h2
    exact one_ne_zero h1
  set Ψ := glEquiv (RingEquiv.refl K) with hΨ
  have hX : ∀ i : Fin Tag.G2.rank,
      ((Ψ (xUnit .G2 K i 1) : GL (Fin 14) K) : Matrix (Fin 14) (Fin 14) K) = XMat K i 1 :=
    fun i => by rw [hΨ, coe_glEquiv, coe_xUnit, endEquiv_xOp]; rfl
  set G : Matrix (Fin 14) (Fin 14) K := ((Ψ g : GL (Fin 14) K) : Matrix (Fin 14) (Fin 14) K)
  set Gi : Matrix (Fin 14) (Fin 14) K := (((Ψ g)⁻¹ : GL (Fin 14) K) : Matrix (Fin 14) (Fin 14) K)
  have hGGi : G * Gi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGiG : Gi * G = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hconj : G * XMat K (ix 0) 1 * Gi = XMat K (ix 1) 1 := by
    have h' := congrArg (fun x => ((Ψ x : GL (Fin 14) K) : Matrix (Fin 14) (Fin 14) K)) h
    simp only [map_mul, map_inv, Units.val_mul, hX] at h'
    exact h'
  have hsq : (XMat K (ix 1) 1 - 1) * (XMat K (ix 1) 1 - 1) =
      G * ((XMat K (ix 0) 1 - 1) * (XMat K (ix 0) 1 - 1)) * Gi := by
    have hsub : XMat K (ix 1) 1 - 1 = G * (XMat K (ix 0) 1 - 1) * Gi := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hconj, Matrix.mul_one, hGGi]
    rw [hsub]
    calc G * (XMat K (ix 0) 1 - 1) * Gi * (G * (XMat K (ix 0) 1 - 1) * Gi) =
        G * (XMat K (ix 0) 1 - 1) * (Gi * G) * (XMat K (ix 0) 1 - 1) * Gi := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hGiG, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hent : ∀ a b, ((XMat K (ix 1) 1 - 1) * (XMat K (ix 1) 1 - 1)) a b =
      2 * G a 5 * Gi 8 b := fun a b => by
    have hN0 : ((XMat (ZMod 3) (ix 0) 1 - 1) * (XMat (ZMod 3) (ix 0) 1 - 1)).map
        (ZMod.castHom (dvd_refl 3) K) =
        Matrix.of (fun k l : Fin 14 => if k = 5 ∧ l = 8 then (2 : K) else 0) := by
      ext k l
      rw [Matrix.map_apply, xMat_zero_sq_zmod, Matrix.of_apply]
      split_ifs
      · exact map_ofNat (ZMod.castHom (dvd_refl 3) K) 2
      · exact map_zero _
    rw [hsq, xMat_sq_eq_map (ix 0), hN0]
    simp only [Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_zero, ite_and,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, ite_mul, zero_mul]
    ring
  have hval : ∀ a b, ((XMat K (ix 1) 1 - 1) * (XMat K (ix 1) 1 - 1)) a b =
      ZMod.castHom (dvd_refl 3) K
        (((XMat (ZMod 3) (ix 1) 1 - 1) * (XMat (ZMod 3) (ix 1) 1 - 1)) a b) := fun a b => by
    rw [xMat_sq_eq_map (ix 1), Matrix.map_apply]
  obtain ⟨e1, e2, e3⟩ := xMat_one_sq_zmod
  have h25 := hent 2 5
  rw [hval, e1, map_ofNat] at h25
  have h29 := hent 2 9
  rw [hval, e2, map_zero] at h29
  have h49 := hent 4 9
  rw [hval, e3, map_ofNat] at h49
  have hG25 : G 2 5 ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_mul] at h25
    exact h2 h25
  have hGi : Gi 8 9 = 0 := by
    have h0 : 2 * G 2 5 * Gi 8 9 = 0 := h29.symm
    rcases mul_eq_zero.mp h0 with h0 | h0
    · rcases mul_eq_zero.mp h0 with h0 | h0
      · exact absurd h0 h2
      · exact absurd h0 hG25
    · exact h0
  rw [hGi, mul_zero] at h49
  exact h2 h49

end Module

section NotConj

variable {K : Type} [Field K]

theorem conjSub_range_g2Chart_ne [CharP K 3] (k : adjointGroup .G2 K) :
    conjSub k (g2Chart K (CFSG.Quasithin.G2U.ix 0)).range ≠
      (g2Chart K (CFSG.Quasithin.G2U.ix 1)).range := by
  intro h
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K 3]
    decide
  have hinj0 := g2Chart_injective hK2 (CFSG.Quasithin.G2U.ix 0)
  have hinj1 := g2Chart_injective hK2 (CFSG.Quasithin.G2U.ix 1)
  have huSL : ∀ a b : K, uSL a * uSL b = uSL (a + b) := fun a b =>
    Matrix.SpecialLinearGroup.ext _ _ fun i j => by
      show (((uSL a : SL2 K) : Matrix (Fin 2) (Fin 2) K) *
        ((uSL b : SL2 K) : Matrix (Fin 2) (Fin 2) K)) i j =
          ((uSL (a + b) : SL2 K) : Matrix (Fin 2) (Fin 2) K) i j
      rw [coe_uSL, coe_uSL, coe_uSL]
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  have hu0 : uSL (0 : K) = 1 := Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    show ((uSL 0 : SL2 K) : Matrix (Fin 2) (Fin 2) K) i j =
      ((1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) i j
    rw [coe_uSL, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp
  have hu3 : uSL (1 : K) ^ 3 = 1 := by
    rw [pow_succ, pow_succ, pow_one, huSL, huSL, show (1 : K) + 1 + 1 = 3 by norm_num, h3, hu0]
  set x := g2Chart K (CFSG.Quasithin.G2U.ix 0) (uSL 1) with hxdef
  have hx : k * x * k⁻¹ ∈ (g2Chart K (CFSG.Quasithin.G2U.ix 1)).range := by
    rw [← h]
    exact ⟨x, ⟨uSL 1, rfl⟩, rfl⟩
  obtain ⟨A, hA⟩ := hx
  have hA3 : A ^ 3 = 1 := by
    apply hinj1
    rw [map_pow, hA, map_one]
    calc (k * x * k⁻¹) ^ 3 = k * x ^ 3 * k⁻¹ := conj_pow
      _ = 1 := by rw [hxdef, ← map_pow, hu3, map_one]; group
  have hA1 : A ≠ 1 := by
    rintro rfl
    rw [map_one] at hA
    have hx1 : x = 1 := by
      calc x = k⁻¹ * (k * x * k⁻¹) * k := by group
        _ = 1 := by rw [← hA]; group
    have hu1 : uSL (1 : K) = 1 := hinj0 (by rw [map_one, ← hxdef, hx1])
    have h01 := congrArg (fun M : SL2 K => (M : Matrix (Fin 2) (Fin 2) K) 0 1) hu1
    simp [uSL] at h01
  obtain ⟨B, c, hc, hAB⟩ := exists_conj_uSL_of_cube h3 hA3 hA1
  have hA' : (k : ModGL .G2 K) * xUnit .G2 K (CFSG.Quasithin.G2U.ix 0) 1 * (k : ModGL .G2 K)⁻¹ =
      (g2Chart K (CFSG.Quasithin.G2U.ix 1) B : ModGL .G2 K) *
        xUnit .G2 K (CFSG.Quasithin.G2U.ix 1) c *
          (g2Chart K (CFSG.Quasithin.G2U.ix 1) B : ModGL .G2 K)⁻¹ := by
    have h1 := congrArg (fun y : adjointGroup .G2 K => (y : ModGL .G2 K)) hA
    simp only [hAB, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, coe_g2Chart,
      simpleRootSL2_uSL, hxdef] at h1
    exact h1.symm
  set cu : Kˣ := Units.mk0 c hc with hcu
  set bt : Fin Tag.G2.rank → Kˣ := fun j => if j = CFSG.Quasithin.G2U.ix 1 then cu else 1
    with hbt
  have hχ : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar bt
      ((1 : WeylGroup Tag.G2) • (Pi.single (CFSG.Quasithin.G2U.ix 1) 1 : Fin Tag.G2.rank → ℤ)) =
        cu := by
    rw [one_smul, rootChar_single_g2]
    simp [bt]
  have htor := rootDiagUnit_conj_rootChart (K := K) (1 : WeylGroup Tag.G2)
    (CFSG.Quasithin.G2U.ix 1) bt (uSL 1)
  rw [hχ, glConjSL_diag_uSL, rootChart_one, mul_one, simpleRootSL2_uSL, simpleRootSL2_uSL,
    hcu, Units.val_mk0] at htor
  set d := CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .G2 bt with hd
  set B' : ModGL .G2 K := (g2Chart K (CFSG.Quasithin.G2U.ix 1) B : ModGL .G2 K) with hB'
  set k' : ModGL .G2 K := (k : ModGL .G2 K) with hk'
  apply not_conj_xUnit_zero_one (k'⁻¹ * B' * d)⁻¹
  rw [← htor] at hA'
  calc (k'⁻¹ * B' * d)⁻¹ * xUnit .G2 K (CFSG.Quasithin.G2U.ix 0) 1 * (k'⁻¹ * B' * d)⁻¹⁻¹ =
      d⁻¹ * B'⁻¹ * (k' * xUnit .G2 K (CFSG.Quasithin.G2U.ix 0) 1 * k'⁻¹) * B' * d := by group
    _ = xUnit .G2 K (CFSG.Quasithin.G2U.ix 1) 1 := by rw [hA']; group
theorem graphInvolution_not_normalize [Finite K] [CharP K CFSG.LieType.Ree.ReeTag.G2.prime]
    (b : ℕ) (g : adjointGroup .G2 K) {R : Subgroup ↥(adjointGroup .G2 K)}
    (hR : R ∈ fundamentalSubgroups .G2 (CFSG.LieType.Steinberg.Adjoint.g2Datum K)) :
    R.map (MulAut.conj g * g2ReeAut K b).toMonoidHom ≠ R := by
  have : CharP K 3 := ‹CharP K CFSG.LieType.Ree.ReeTag.G2.prime›
  obtain ⟨i, h, rfl⟩ := exists_eq_conjSub_g2Chart hR
  intro heq
  rw [map_conj_mul, map_conjSub, map_range_g2Chart_g2ReeAut, ← conjSub_mul] at heq
  have key : conjSub (h⁻¹ * (g * g2ReeAut K b h))
      (g2Chart K (CFSG.LieType.Ree.ReeTag.G2.perm i)).range = (g2Chart K i).range := by
    rw [conjSub_mul, heq, conjSub_inv_conjSub]
  have hi : i = CFSG.Quasithin.G2U.ix 0 ∨ i = CFSG.Quasithin.G2U.ix 1 := by
    fin_cases i
    exacts [Or.inl rfl, Or.inr rfl]
  rcases hi with rfl | rfl
  · have hρ : CFSG.LieType.Ree.ReeTag.G2.perm (CFSG.Quasithin.G2U.ix 0) =
        CFSG.Quasithin.G2U.ix 1 := Equiv.swap_apply_left _ _
    rw [hρ] at key
    refine conjSub_range_g2Chart_ne (h⁻¹ * (g * g2ReeAut K b h))⁻¹ ?_
    rw [← key, conjSub_inv_conjSub]
  · have hρ : CFSG.LieType.Ree.ReeTag.G2.perm (CFSG.Quasithin.G2U.ix 1) =
        CFSG.Quasithin.G2U.ix 0 := Equiv.swap_apply_right _ _
    rw [hρ] at key
    exact conjSub_range_g2Chart_ne _ key

end NotConj

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19F
