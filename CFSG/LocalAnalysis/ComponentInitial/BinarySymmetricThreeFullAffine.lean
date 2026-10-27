module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeLinear
public import CFSG.Assembly.Defs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix

local notation "𝕍" => {X : Matrix (Fin 3) (Fin 3) (ZMod 2) // X ∈ binarySymMatrices 3}
local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)
local notation "𝔼" => Fin 3 → ZMod 2

@[expose] def symThreePolarSym (u v : 𝔼) : 𝕍 :=
  ⟨symThreePolar u v, symThreePolar_mem u v⟩

@[expose] def symThreePolarLin (a : 𝔼) : 𝕍 →ₗ[ZMod 2] 𝕍 where
  toFun B := symThreePolarSym a (symThreeDiag (B : M₃))
  map_add' B C := Subtype.ext (by
    change symThreePolar a (symThreeDiag ((B : M₃) + C)) = symThreePolar a (symThreeDiag B) +
      symThreePolar a (symThreeDiag C)
    rw [symThreeDiag_add, symThreePolar, symThreePolar, symThreePolar, vecMulVec_add,
      add_vecMulVec]
    abel)
  map_smul' c B := Subtype.ext (by
    change symThreePolar a (symThreeDiag (c • (B : M₃))) = c • symThreePolar a (symThreeDiag B)
    rw [symThreeDiag_smul, symThreePolar, symThreePolar, vecMulVec_smul, smul_vecMulVec, smul_add])

theorem symThreePolarLin_apply (a : 𝔼) (B : 𝕍) :
    symThreePolarLin a B = symThreePolarSym a (symThreeDiag (B : M₃)) :=
  rfl

theorem symThreeDiag_polarSym (u v : 𝔼) : symThreeDiag (symThreePolarSym u v : M₃) = 0 :=
  symThreeDiag_polar u v

theorem symThreePolarSym_zero_right (u : 𝔼) : symThreePolarSym u 0 = 0 :=
  Subtype.ext (by
    change symThreePolar u 0 = 0
    rw [symThreePolar, vecMulVec_zero, zero_vecMulVec, add_zero])

theorem symThreePolarLin_polarSym (a u v : 𝔼) : symThreePolarLin a (symThreePolarSym u v) = 0 := by
  rw [symThreePolarLin_apply, symThreeDiag_polarSym, symThreePolarSym_zero_right]

theorem symThreeTwoCoreLin_involutive (κ : ZMod 2) (a : 𝔼) :
    Function.Involutive (LinearMap.id + κ • symThreePolarLin a : 𝕍 →ₗ[ZMod 2] 𝕍) := by
  intro B
  have h : symThreePolarLin a (symThreePolarLin a B) = 0 := symThreePolarLin_polarSym _ _ _
  simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply, map_add, map_smul, h,
    smul_zero, add_zero]
  rw [add_assoc, symThree_add_self, add_zero]

@[expose] def symThreeTwoCoreLin (κ : ZMod 2) (a : 𝔼) : 𝕍 ≃ₗ[ZMod 2] 𝕍 :=
  LinearEquiv.ofInvolutive _ (symThreeTwoCoreLin_involutive κ a)

@[expose] def symThreeTwoCoreMap (κ : ZMod 2) (A : 𝕍) : 𝕍 ≃ᵃ[ZMod 2] 𝕍 :=
  AffineEquiv.constVAdd (ZMod 2) 𝕍 A * (symThreeTwoCoreLin κ (symThreeDiag (A : M₃))).toAffineEquiv

theorem symThreeTwoCoreMap_apply (κ : ZMod 2) (A B : 𝕍) :
    symThreeTwoCoreMap κ A B =
      B + A + κ • symThreePolarSym (symThreeDiag (A : M₃)) (symThreeDiag (B : M₃)) := by
  change A + (B + κ • symThreePolarSym (symThreeDiag (A : M₃)) (symThreeDiag (B : M₃))) = _
  abel

theorem coe_symThreeTwoCoreMap (κ : ZMod 2) (A : 𝕍) :
    ⇑(symThreeTwoCoreMap κ A) = symThreeAffine κ A := by
  funext B
  rw [symThreeTwoCoreMap_apply]
  exact Subtype.ext (by rw [coe_symThreeAffine]; rfl)

theorem symThreeTwoCoreMap_mul (κ : ZMod 2) (A A' : 𝕍) :
    symThreeTwoCoreMap κ A * symThreeTwoCoreMap κ A' =
      symThreeTwoCoreMap κ (A + A' + κ • symThreePolarSym (symThreeDiag (A : M₃))
        (symThreeDiag (A' : M₃))) := by
  refine AffineEquiv.ext fun B => ?_
  have hδ : symThreeDiag ((A + A' + κ • symThreePolarSym (symThreeDiag (A : M₃))
      (symThreeDiag (A' : M₃)) : 𝕍) : M₃) = symThreeDiag (A : M₃) + symThreeDiag (A' : M₃) := by
    rw [AddSubgroup.coe_add, AddSubgroup.coe_add, coe_smul_binarySymMatrices, symThreeDiag_add,
      symThreeDiag_add, symThreeDiag_smul, symThreeDiag_polarSym, smul_zero, add_zero]
  rw [AffineEquiv.coe_mul, Function.comp_apply, symThreeTwoCoreMap_apply,
    symThreeTwoCoreMap_apply, symThreeTwoCoreMap_apply, hδ]
  have hδB : symThreeDiag ((B + A' + κ • symThreePolarSym (symThreeDiag (A' : M₃))
      (symThreeDiag (B : M₃)) : 𝕍) : M₃) = symThreeDiag (B : M₃) + symThreeDiag (A' : M₃) := by
    rw [AddSubgroup.coe_add, AddSubgroup.coe_add, coe_smul_binarySymMatrices, symThreeDiag_add,
      symThreeDiag_add, symThreeDiag_smul, symThreeDiag_polarSym, smul_zero, add_zero]
  rw [hδB]
  have hp : ∀ u v w : 𝔼,
      symThreePolarSym u (v + w) = symThreePolarSym u v + symThreePolarSym u w :=
    fun u v w => Subtype.ext (by
      change symThreePolar u (v + w) = symThreePolar u v + symThreePolar u w
      rw [symThreePolar, symThreePolar, symThreePolar, vecMulVec_add, add_vecMulVec]
      abel)
  have hp' : ∀ u v w : 𝔼,
      symThreePolarSym (u + v) w = symThreePolarSym u w + symThreePolarSym v w :=
    fun u v w => Subtype.ext (by
      change symThreePolar (u + v) w = symThreePolar u w + symThreePolar v w
      rw [symThreePolar, symThreePolar, symThreePolar, vecMulVec_add, add_vecMulVec]
      abel)
  have hcomm : ∀ u v : 𝔼, symThreePolarSym u v = symThreePolarSym v u := fun u v =>
    Subtype.ext (symThreePolar_comm u v)
  rw [hp, hp', hcomm (symThreeDiag (A' : M₃)) (symThreeDiag (B : M₃))]
  simp only [smul_add]
  abel

theorem symThreeTwoCoreMap_zero (κ : ZMod 2) : symThreeTwoCoreMap κ 0 = 1 :=
  AffineEquiv.ext fun B => by
    rw [coe_symThreeTwoCoreMap, symThreeAffine_zero_left]
    rfl

@[expose] def symThreeTwoCoreGroup (κ : ZMod 2) : Subgroup (𝕍 ≃ᵃ[ZMod 2] 𝕍) where
  carrier := Set.range (symThreeTwoCoreMap κ)
  one_mem' := ⟨0, symThreeTwoCoreMap_zero κ⟩
  mul_mem' := by
    rintro _ _ ⟨A, rfl⟩ ⟨A', rfl⟩
    exact ⟨_, (symThreeTwoCoreMap_mul κ A A').symm⟩
  inv_mem' := by
    rintro _ ⟨A, rfl⟩
    refine ⟨A, eq_inv_of_mul_eq_one_left ?_⟩
    rw [symThreeTwoCoreMap_mul, show symThreePolarSym (symThreeDiag (A : M₃))
      (symThreeDiag (A : M₃)) = 0 from Subtype.ext (symThreePolar_self _), smul_zero, add_zero,
      symThree_add_self, symThreeTwoCoreMap_zero]

@[expose] def symThreeAltTranslations : Subgroup (𝕍 ≃ᵃ[ZMod 2] 𝕍) where
  carrier := {k | ∃ i : 𝕍, symThreeDiag (i : M₃) = 0 ∧ k = AffineEquiv.constVAdd (ZMod 2) 𝕍 i}
  one_mem' := ⟨0, rfl, AffineEquiv.ext fun B => by
    change B = 0 + B
    rw [zero_add]⟩
  mul_mem' := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    refine ⟨i + j, by rw [AddSubgroup.coe_add, symThreeDiag_add, hi, hj, add_zero],
      AffineEquiv.ext fun B => ?_⟩
    change i + (j + B) = i + j + B
    rw [add_assoc]
  inv_mem' := by
    rintro _ ⟨i, hi, rfl⟩
    refine ⟨i, hi, (eq_inv_of_mul_eq_one_left (AffineEquiv.ext fun B => ?_)).symm⟩
    change i + (i + B) = B
    rw [← add_assoc, symThree_add_self, zero_add]

theorem symThreePolarSym_zero_left (v : 𝔼) : symThreePolarSym 0 v = 0 :=
  Subtype.ext (symThreePolar_zero_left v)

theorem symThreePolarSym_self (u : 𝔼) : symThreePolarSym u u = 0 :=
  Subtype.ext (symThreePolar_self u)

theorem symThreeCongr_polarSym (D : GL (Fin 3) (ZMod 2)) (u v : 𝔼) :
    symThreeCongr D (symThreePolarSym u v) =
      symThreePolarSym ((D : M₃) *ᵥ u) ((D : M₃) *ᵥ v) :=
  Subtype.ext (by
    rw [coe_symThreeCongr]
    change (D : M₃) * symThreePolar u v * (D : M₃)ᵀ = symThreePolar _ _
    rw [symThreePolar, symThreePolar, Matrix.mul_add, Matrix.add_mul, mul_vecMulVec,
      mul_vecMulVec, vecMulVec_mul, vecMulVec_mul, vecMul_transpose, vecMul_transpose])

@[expose] def colDetThree (a e c : 𝔼) : ZMod 2 :=
  a 0 * (e 1 * c 2 - e 2 * c 1) - a 1 * (e 0 * c 2 - e 2 * c 0) + a 2 * (e 0 * c 1 - e 1 * c 0)

@[expose] def colMatThree (a e c : 𝔼) : M₃ :=
  Matrix.of fun i j => ![a, e, c] j i

theorem det_colMatThree (a e c : 𝔼) : (colMatThree a e c).det = colDetThree a e c := by
  rw [Matrix.det_fin_three]
  simp only [colMatThree, colDetThree, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem colMatThree_mulVec_one (a e c : 𝔼) : colMatThree a e c *ᵥ ![1, 0, 0] = a := by
  funext i
  simp [colMatThree, mulVec, dotProduct, Fin.sum_univ_three]

theorem colMatThree_mulVec_two (a e c : 𝔼) : colMatThree a e c *ᵥ ![0, 1, 0] = e := by
  funext i
  simp [colMatThree, mulVec, dotProduct, Fin.sum_univ_three]

theorem exists_colDetThree_ne_zero : ∀ a e : 𝔼, a ≠ 0 → e ≠ 0 → a ≠ e →
    ∃ c : 𝔼, colDetThree a e c ≠ 0 := by
  decide

theorem exists_ne_zero_ne : ∀ a : 𝔼, ∃ e : 𝔼, e ≠ 0 ∧ a ≠ e := by
  decide

theorem exists_gl_pair {a e : 𝔼} (ha : a ≠ 0) (he : e ≠ 0) (hae : a ≠ e) :
    ∃ D : GL (Fin 3) (ZMod 2), (D : M₃) *ᵥ ![1, 0, 0] = a ∧ (D : M₃) *ᵥ ![0, 1, 0] = e := by
  obtain ⟨c, hc⟩ := exists_colDetThree_ne_zero a e ha he hae
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (colMatThree a e c)
    (by rwa [det_colMatThree]), ?_, ?_⟩
  · rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, colMatThree_mulVec_one]
  · rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, colMatThree_mulVec_two]

@[expose] def glSwapTwoThree : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 0, 1; 0, 1, 0], by decide, by decide⟩

@[expose] def glTransTwoOne : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], !![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide, by decide⟩

@[expose] def glTransThreeOne : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], !![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide, by decide⟩

@[expose] def glTransThreeTwo : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], !![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide, by decide⟩

theorem eq_zero_of_stab_one : ∀ X : 𝕍, symThreeDiag (X : M₃) = 0 →
    symThreeCongr glSwapTwoThree X = X → symThreeCongr glTransTwoOne X = X →
      symThreeCongr glTransThreeTwo X = X → X = 0 := by
  decide +kernel

theorem eq_polar_of_stab_one_two : ∀ X : 𝕍, symThreeDiag (X : M₃) = 0 →
    symThreeCongr glTransThreeOne X = X → symThreeCongr glTransThreeTwo X = X →
      X = 0 ∨ X = symThreePolarSym ![1, 0, 0] ![0, 1, 0] := by
  decide +kernel

theorem eq_smul_polar_of_equivariant (t : 𝔼 → 𝔼 → 𝕍)
    (hadd₁ : ∀ a a' e, t (a + a') e = t a e + t a' e)
    (hadd₂ : ∀ a e e', t a (e + e') = t a e + t a e')
    (hI : ∀ a e, symThreeDiag (t a e : M₃) = 0)
    (heq : ∀ (D : GL (Fin 3) (ZMod 2)) a e,
      t ((D : M₃) *ᵥ a) ((D : M₃) *ᵥ e) = symThreeCongr D (t a e)) :
    ∃ κ : ZMod 2, ∀ a e, t a e = κ • symThreePolarSym a e := by
  have hstab1 : ∀ D : GL (Fin 3) (ZMod 2), (D : M₃) *ᵥ ![1, 0, 0] = ![1, 0, 0] →
      symThreeCongr D (t ![1, 0, 0] ![1, 0, 0]) = t ![1, 0, 0] ![1, 0, 0] := fun D hD => by
    rw [← heq, hD]
  have hstab2 : ∀ D : GL (Fin 3) (ZMod 2), (D : M₃) *ᵥ ![1, 0, 0] = ![1, 0, 0] →
      (D : M₃) *ᵥ ![0, 1, 0] = ![0, 1, 0] →
        symThreeCongr D (t ![1, 0, 0] ![0, 1, 0]) = t ![1, 0, 0] ![0, 1, 0] := fun D h1 h2 => by
    rw [← heq, h1, h2]
  have h11 : t ![1, 0, 0] ![1, 0, 0] = 0 := eq_zero_of_stab_one _ (hI _ _)
    (hstab1 _ (by decide)) (hstab1 _ (by decide)) (hstab1 _ (by decide))
  have hzero₁ : ∀ e, t 0 e = 0 := fun e => by
    have h := hadd₁ 0 0 e
    rwa [add_zero, symThree_add_self] at h
  have hzero₂ : ∀ a, t a 0 = 0 := fun a => by
    have h := hadd₂ a 0 0
    rwa [add_zero, symThree_add_self] at h
  have hdiag : ∀ a, t a a = 0 := by
    intro a
    by_cases ha : a = 0
    · rw [ha, hzero₁]
    · obtain ⟨e, he, hae⟩ := exists_ne_zero_ne a
      obtain ⟨D, hD1, -⟩ := exists_gl_pair ha he hae
      rw [← hD1, heq, h11]
      exact map_zero (symThreeCongrEquiv D)
  obtain ⟨κ, hκ⟩ : ∃ κ : ZMod 2,
      t ![1, 0, 0] ![0, 1, 0] = κ • symThreePolarSym ![1, 0, 0] ![0, 1, 0] := by
    rcases eq_polar_of_stab_one_two _ (hI _ _) (hstab2 _ (by decide) (by decide))
      (hstab2 _ (by decide) (by decide)) with h | h
    · exact ⟨0, by rw [h, zero_smul]⟩
    · exact ⟨1, by rw [h, one_smul]⟩
  refine ⟨κ, fun a e => ?_⟩
  by_cases ha : a = 0
  · rw [ha, hzero₁, symThreePolarSym_zero_left, smul_zero]
  by_cases he : e = 0
  · rw [he, hzero₂, symThreePolarSym_zero_right, smul_zero]
  by_cases hae : a = e
  · rw [hae, hdiag, symThreePolarSym_self, smul_zero]
  obtain ⟨D, hD1, hD2⟩ := exists_gl_pair ha he hae
  rw [← hD1, ← hD2, heq, hκ, symThreeCongr_smul, symThreeCongr_polarSym]

theorem exists_fixed_ne_of_isPGroup_two {Q : Type*} [Group Q] (hQ : IsPGroup 2 Q) {α : Type*}
    [MulAction Q α] [Finite α] (hα : 2 ∣ Nat.card α) (a : α) (ha : ∀ q : Q, q • a = a) :
    ∃ b, b ≠ a ∧ ∀ q : Q, q • b = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hQ.card_modEq_card_fixedPoints α
  have hmem : a ∈ MulAction.fixedPoints Q α := MulAction.mem_fixedPoints.2 ha
  have : Nonempty (MulAction.fixedPoints Q α) := ⟨⟨a, hmem⟩⟩
  have hpos : 0 < Nat.card (MulAction.fixedPoints Q α) := Nat.card_pos
  have h1 : 1 < Nat.card (MulAction.fixedPoints Q α) := by
    unfold Nat.ModEq at h
    omega
  have : Nontrivial (MulAction.fixedPoints Q α) := Finite.one_lt_card_iff_nontrivial.mp h1
  obtain ⟨⟨b, hb⟩, hba⟩ := exists_ne (⟨a, hmem⟩ : MulAction.fixedPoints Q α)
  exact ⟨b, fun h => hba (Subtype.ext h), MulAction.mem_fixedPoints.1 hb⟩

namespace SymThreeFullAffine

theorem aff_apply (k : 𝕍 ≃ᵃ[ZMod 2] 𝕍) (x : 𝕍) : k x = k.linear x + k 0 := by
  have h := congrFun (AffineMap.decomp k.toAffineMap) x
  simpa using h

theorem eq_toAffineEquiv_of_apply_zero {k : 𝕍 ≃ᵃ[ZMod 2] 𝕍} (h : k 0 = 0) :
    k = k.linear.toAffineEquiv :=
  AffineEquiv.ext fun x => by
    rw [aff_apply, h, add_zero]
    rfl

abbrev tr (v : 𝕍) : 𝕍 ≃ᵃ[ZMod 2] 𝕍 :=
  AffineEquiv.constVAdd (ZMod 2) 𝕍 v

theorem tr_apply (v x : 𝕍) : tr v x = v + x :=
  rfl

theorem tr_add (v w : 𝕍) : tr (v + w) = tr v * tr w :=
  AffineEquiv.ext fun x => by
    rw [AffineEquiv.coe_mul, Function.comp_apply, tr_apply, tr_apply, tr_apply, add_assoc]

theorem tr_zero : tr (0 : 𝕍) = 1 :=
  AffineEquiv.ext fun x => by
    rw [tr_apply, zero_add]
    rfl

theorem tr_linear (v : 𝕍) : (tr v).linear = 1 :=
  AffineEquiv.linear_constVAdd (ZMod 2) 𝕍 v

theorem conj_tr (k : 𝕍 ≃ᵃ[ZMod 2] 𝕍) (v : 𝕍) : k * tr v * k⁻¹ = tr (k.linear v) :=
  AffineEquiv.ext fun x => by
    change k (v + k.symm x) = k.linear v + x
    rw [aff_apply k, map_add, add_assoc, ← aff_apply k, AffineEquiv.apply_symm_apply]

@[expose] def toAff : (𝕍 ≃ₗ[ZMod 2] 𝕍) →* (𝕍 ≃ᵃ[ZMod 2] 𝕍) where
  toFun g := g.toAffineEquiv
  map_one' := AffineEquiv.ext fun _ => rfl
  map_mul' _ _ := AffineEquiv.ext fun _ => rfl

theorem toAff_linear (g : 𝕍 ≃ₗ[ZMod 2] 𝕍) : (toAff g).linear = g :=
  rfl

theorem linear_mul (k k' : 𝕍 ≃ᵃ[ZMod 2] 𝕍) : (k * k').linear = k.linear * k'.linear :=
  rfl

theorem linear_inv (k : 𝕍 ≃ᵃ[ZMod 2] 𝕍) : k⁻¹.linear = k.linear⁻¹ :=
  map_inv AffineEquiv.linearHom k

theorem neg_eq_self (v : 𝕍) : -v = v :=
  neg_eq_of_add_eq_zero_left (symThree_add_self v)

structure Hyp (K : Subgroup (𝕍 ≃ᵃ[ZMod 2] 𝕍)) : Prop where
  trans : ∀ x y : 𝕍, ∃ k ∈ K, k x = y
  stab : ∀ g : 𝕍 ≃ₗ[ZMod 2] 𝕍, toAff g ∈ K ↔ g ∈ symThreeCongrGroup

variable {K : Subgroup (𝕍 ≃ᵃ[ZMod 2] 𝕍)}

theorem congr_mem (hK : Hyp K) (D : GL (Fin 3) (ZMod 2)) : toAff (symThreeCongrHom D) ∈ K :=
  (hK.stab _).mpr ⟨D, rfl⟩

theorem linear_mem_of_apply_zero (hK : Hyp K) {k : 𝕍 ≃ᵃ[ZMod 2] 𝕍} (hk : k ∈ K) (h0 : k 0 = 0) :
    k.linear ∈ symThreeCongrGroup := by
  rw [← hK.stab, show toAff k.linear = k.linear.toAffineEquiv from rfl,
    ← eq_toAffineEquiv_of_apply_zero h0]
  exact hk

theorem finite_aff : Finite (𝕍 ≃ᵃ[ZMod 2] 𝕍) :=
  Finite.of_injective _ AffineEquiv.coeFn_injective

theorem card_K (hK : Hyp K) : Nat.card K = 10752 := by
  choose g hgK hg using fun A : 𝕍 => hK.trans 0 A
  let e1 : K ≃ 𝕍 × {k : K // (k : 𝕍 ≃ᵃ[ZMod 2] 𝕍) 0 = 0} :=
    { toFun := fun k => (k.1 0, ⟨⟨(g (k.1 0))⁻¹ * k.1, K.mul_mem (K.inv_mem (hgK _)) k.2⟩, by
        change (g (k.1 0)).symm (k.1 0) = 0
        rw [AffineEquiv.symm_apply_eq, hg]⟩)
      invFun := fun p => ⟨g p.1 * p.2.1.1, K.mul_mem (hgK _) p.2.1.2⟩
      left_inv := fun k => Subtype.ext (mul_inv_cancel_left _ _)
      right_inv := fun p => by
        obtain ⟨A, ⟨k, hk⟩, hk0⟩ := p
        have h1 : (g A * k) 0 = A := by
          rw [AffineEquiv.coe_mul, Function.comp_apply, hk0, hg]
        refine Prod.ext h1 (Subtype.ext (Subtype.ext ?_))
        change (g ((g A * k) 0))⁻¹ * (g A * k) = k
        rw [h1, inv_mul_cancel_left] }
  let e2 : {k : K // (k : 𝕍 ≃ᵃ[ZMod 2] 𝕍) 0 = 0} ≃ symThreeCongrGroup :=
    { toFun := fun k => ⟨k.1.1.linear, linear_mem_of_apply_zero hK k.1.2 k.2⟩
      invFun := fun g => ⟨⟨toAff g.1, (hK.stab _).mpr g.2⟩, map_zero g.1⟩
      left_inv := fun k => Subtype.ext (Subtype.ext (eq_toAffineEquiv_of_apply_zero k.2).symm)
      right_inv := fun g => rfl }
  rw [Nat.card_congr e1, Nat.card_prod, Nat.card_congr e2, card_symThreeCongrGroup, card_symThree]

@[expose] def transSub (K : Subgroup (𝕍 ≃ᵃ[ZMod 2] 𝕍)) : AddSubgroup 𝕍 where
  carrier := {v | tr v ∈ K}
  add_mem' := fun {v w} hv hw => by
    change tr (v + w) ∈ K
    rw [tr_add]
    exact K.mul_mem hv hw
  zero_mem' := by
    change tr 0 ∈ K
    rw [tr_zero]
    exact K.one_mem
  neg_mem' := fun {v} hv => by
    change tr (-v) ∈ K
    rw [neg_eq_self]
    exact hv

theorem mem_transSub {v : 𝕍} : v ∈ transSub K ↔ tr v ∈ K :=
  Iff.rfl

theorem linear_mem_transSub {k : 𝕍 ≃ᵃ[ZMod 2] 𝕍} (hk : k ∈ K) {v : 𝕍} (hv : v ∈ transSub K) :
    k.linear v ∈ transSub K := by
  rw [mem_transSub, ← conj_tr]
  exact K.mul_mem (K.mul_mem hk hv) (K.inv_mem hk)

theorem transSub_invariant (hK : Hyp K) : IsSymThreeCongrInvariant (transSub K : Set 𝕍) :=
  fun D _ hv => linear_mem_transSub (congr_mem hK D) hv

theorem finite_linearEquiv : Finite (𝕍 ≃ₗ[ZMod 2] 𝕍) :=
  Finite.of_injective (fun g : 𝕍 ≃ₗ[ZMod 2] 𝕍 => (g : 𝕍 → 𝕍)) fun _ _ h =>
    LinearEquiv.ext (congrFun h)

theorem card_le_of_rankOne_invariant (G : Subgroup (𝕍 ≃ₗ[ZMod 2] 𝕍))
    (hG : ∀ g ∈ G, ∀ B : 𝕍, symThreeType (B : M₃) = 1 → symThreeType (g B : M₃) = 1) :
    Nat.card G ≤ 5040 := by
  classical
  have hS₁ : Nat.card {B : 𝕍 // symThreeType (B : M₃) = 1} = 7 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, card_symThreeType]
    rfl
  let Φ : G → Equiv.Perm {B : 𝕍 // symThreeType (B : M₃) = 1} := fun g =>
    Equiv.subtypeEquiv (g : 𝕍 ≃ₗ[ZMod 2] 𝕍).toEquiv fun B =>
      ⟨hG g g.2 B, fun h => by
        have h' := hG _ (G.inv_mem g.2) _ h
        rwa [show ((g : 𝕍 ≃ₗ[ZMod 2] 𝕍)⁻¹ : 𝕍 ≃ₗ[ZMod 2] 𝕍) = (g : 𝕍 ≃ₗ[ZMod 2] 𝕍).symm from rfl,
          LinearEquiv.coe_toEquiv, LinearEquiv.symm_apply_apply] at h'⟩
  have hΦ : Function.Injective Φ := by
    intro g g' h
    refine Subtype.ext (eq_of_eq_on_symThreeType_one fun B hB => ?_)
    have h1 := congrArg (fun σ : Equiv.Perm {B : 𝕍 // symThreeType (B : M₃) = 1} =>
      (σ ⟨B, hB⟩ : 𝕍)) h
    exact h1
  have h := Nat.card_le_card_of_injective Φ hΦ
  rwa [Nat.card_perm, hS₁] at h

theorem linear_preserves_alt_of_bot (hK : Hyp K) (hT : transSub K = ⊥) {k : 𝕍 ≃ᵃ[ZMod 2] 𝕍}
    (hk : k ∈ K) {B : 𝕍} (hB : symThreeDiag (B : M₃) = 0) :
    symThreeDiag (k.linear B : M₃) = 0 := by
  classical
  have := finite_aff
  have := finite_linearEquiv
  let lam : K →* (𝕍 ≃ₗ[ZMod 2] 𝕍) := AffineEquiv.linearHom.comp K.subtype
  have hinj : Function.Injective lam := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k₁ hk₁
    rw [MonoidHom.mem_ker] at hk₁
    have hlin : (k₁ : 𝕍 ≃ᵃ[ZMod 2] 𝕍).linear = 1 := hk₁
    have htr : (k₁ : 𝕍 ≃ᵃ[ZMod 2] 𝕍) = tr ((k₁ : 𝕍 ≃ᵃ[ZMod 2] 𝕍) 0) := AffineEquiv.ext fun x => by
      rw [aff_apply, hlin, tr_apply, add_comm]
      rfl
    have h0 : (k₁ : 𝕍 ≃ᵃ[ZMod 2] 𝕍) 0 ∈ transSub K := by
      rw [mem_transSub, ← htr]
      exact k₁.2
    rw [hT, AddSubgroup.mem_bot] at h0
    rw [Subgroup.mem_bot]
    exact Subtype.ext (htr.trans (by rw [h0, tr_zero]; rfl))
  let G := lam.range
  have hG : Nat.card G = 10752 := by
    rw [← card_K hK]
    exact Nat.card_congr (Equiv.ofInjective lam hinj).symm
  have hHG : ∀ D : GL (Fin 3) (ZMod 2), symThreeCongrHom D ∈ G := fun D =>
    ⟨⟨toAff _, congr_mem hK D⟩, rfl⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime (G := G) 2 (n := 9)
    (by rw [hG]; norm_num)
  have hSp : IsPGroup 2 S := IsPGroup.of_card hS
  obtain ⟨v₀, hv₀, hfix⟩ := exists_fixed_ne_of_isPGroup_two hSp (α := 𝕍)
    (by rw [card_symThree]; norm_num) 0 fun s => by
      change ((s : G) : 𝕍 ≃ₗ[ZMod 2] 𝕍) 0 = 0
      exact map_zero _
  let O : Set 𝕍 := MulAction.orbit G v₀
  have hOinv : ∀ g ∈ G, ∀ B ∈ O, g B ∈ O := by
    rintro g hg B ⟨g', rfl⟩
    refine ⟨⟨g, hg⟩ * g', ?_⟩
    change (⟨g, hg⟩ * g' : G) • v₀ = g (g' • v₀)
    rw [mul_smul]
    rfl
  have hOcongr : IsSymThreeCongrInvariant O := fun D B hB => hOinv _ (hHG D) B hB
  have hcard : Nat.card O ∣ 21 := by
    have h1 := (MulAction.stabilizer G v₀).index_mul_card
    rw [MulAction.index_stabilizer, hG] at h1
    have h2 : Nat.card S ∣ Nat.card (MulAction.stabilizer G v₀) :=
      Subgroup.card_dvd_of_le fun s hs => hfix ⟨s, hs⟩
    rw [hS] at h2
    obtain ⟨c, hc⟩ := h2
    rw [hc] at h1
    have h3 : 2 ^ 9 * ((MulAction.orbit G v₀).ncard * c) = 2 ^ 9 * 21 := by
      rw [Nat.mul_left_comm, h1]
      norm_num
    rw [Nat.card_coe_set_eq]
    exact Dvd.intro c (Nat.eq_of_mul_eq_mul_left (by norm_num) h3)
  have hsum := card_eq_sum_of_invariant hOcongr
  have hmemO : ∀ B : 𝕍, symThreeType (B : M₃) ∈ symThreeTypesOf O ↔ B ∈ O :=
    fun B => mem_symThreeTypesOf hOcongr
  have h0O : (0 : Fin 5) ∉ symThreeTypesOf O := by
    rw [← (symThreeType_eq_zero_iff 0).2 rfl, hmemO]
    rintro ⟨g, hg⟩
    exact hv₀ ((LinearEquiv.map_eq_zero_iff (g : 𝕍 ≃ₗ[ZMod 2] 𝕍)).1 hg)
  have hne : (symThreeTypesOf O).Nonempty := ⟨_, (hmemO v₀).2 (MulAction.mem_orbit_self v₀)⟩
  have hdvd : (∑ t ∈ symThreeTypesOf O, symThreeTypeCount t) ∣ 21 := by
    rw [← hsum]
    exact hcard
  have hGinv : ∀ t : Fin 5, symThreeTypesOf O = {t} → ∀ g ∈ G, ∀ B : 𝕍,
      symThreeType (B : M₃) = t → symThreeType (g B : M₃) = t := by
    intro t hτ g hg B hBt
    have hBO : B ∈ O := (hmemO B).1 (by rw [hτ, hBt]; exact Finset.mem_singleton_self t)
    have h1 := (hmemO _).2 (hOinv g hg B hBO)
    rwa [hτ, Finset.mem_singleton] at h1
  rcases symThreeTypes_of_card_dvd_twentyOne _ h0O hne hdvd with hτ | hτ | hτ
  · exfalso
    have h := card_le_of_rankOne_invariant G (hGinv 1 hτ)
    omega
  · by_cases hB0 : B = 0
    · rw [hB0, map_zero]
      rfl
    · have h2 : symThreeType (B : M₃) = 2 := by
        rcases (symThreeType_mem_zero_two_iff B).2 hB with h | h
        · exact absurd ((symThreeType_eq_zero_iff B).1 h) hB0
        · exact h
      exact (symThreeType_mem_zero_two_iff _).1
        (Or.inr (hGinv 2 hτ _ ⟨⟨k, hk⟩, rfl⟩ B h2))
  · exfalso
    have h3 := hGinv 3 hτ
    have h := card_le_of_rankOne_invariant G fun g hg B hB => by
      obtain ⟨hB0, hBs⟩ := (symThreeType_eq_one_iff B).1 hB
      refine (symThreeType_eq_one_iff _).2 ⟨fun h => hB0 ?_, fun A hA hgA => ?_⟩
      · exact (LinearEquiv.map_eq_zero_iff g).1 h
      · have hginv : (g⁻¹ : 𝕍 ≃ₗ[ZMod 2] 𝕍) ∈ G := G.inv_mem hg
        have hA' := h3 _ hginv A hA
        have hgA' := h3 _ hginv _ hgA
        rw [map_add, show (g⁻¹ : 𝕍 ≃ₗ[ZMod 2] 𝕍) = g.symm from rfl,
          LinearEquiv.symm_apply_apply] at hgA'
        exact hBs _ hA' hgA'
    omega

theorem linear_preserves_alt (hK : Hyp K) {k : 𝕍 ≃ᵃ[ZMod 2] 𝕍} (hk : k ∈ K) {B : 𝕍}
    (hB : symThreeDiag (B : M₃) = 0) : symThreeDiag (k.linear B : M₃) = 0 := by
  rcases invariant_addSubgroup (transSub K) (transSub_invariant hK) with hT | hT | hT
  · exact linear_preserves_alt_of_bot hK hT hk hB
  · exact (hT _).1 (linear_mem_transSub hk ((hT B).2 hB))
  · have h0 : k 0 ∈ transSub K := hT ▸ AddSubgroup.mem_top _
    have hk' : (tr (k 0))⁻¹ * k ∈ K := K.mul_mem (K.inv_mem h0) hk
    have hk'0 : ((tr (k 0))⁻¹ * k) 0 = 0 := by
      change (tr (k 0)).symm (k 0) = 0
      rw [AffineEquiv.symm_apply_eq, tr_apply, add_zero]
    have hlin : ((tr (k 0))⁻¹ * k).linear = k.linear := by
      rw [linear_mul, linear_inv, tr_linear, inv_one, one_mul]
    obtain ⟨D, hD⟩ := linear_mem_of_apply_zero hK hk' hk'0
    rw [← hlin, ← hD, symThreeCongrHom_apply, symThreeDiag_coe_congr, hB, mulVec_zero]

@[expose] def indLin (k : 𝕍 ≃ᵃ[ZMod 2] 𝕍) : 𝔼 →ₗ[ZMod 2] 𝔼 :=
  symThreeDiagLin ∘ₗ k.linear.toLinearMap ∘ₗ symThreeDiagSection

theorem indLin_apply (k : 𝕍 ≃ᵃ[ZMod 2] 𝕍) (e : 𝔼) :
    indLin k e = symThreeDiag (k.linear (symThreeDiagSection e) : M₃) :=
  rfl

theorem diag_linear_apply (hK : Hyp K) {k : 𝕍 ≃ᵃ[ZMod 2] 𝕍} (hk : k ∈ K) (B : 𝕍) :
    symThreeDiag (k.linear B : M₃) = indLin k (symThreeDiag (B : M₃)) := by
  have hB : B = symThreeDiagSection (symThreeDiag (B : M₃)) +
      (B + symThreeDiagSection (symThreeDiag (B : M₃))) := by
    rw [add_left_comm, symThree_add_self, add_zero]
  have hI := linear_preserves_alt hK hk (symThreeDiag_add_diagSection B)
  conv_lhs => rw [hB]
  rw [map_add, AddSubgroup.coe_add, symThreeDiag_add, hI, add_zero]
  rfl

theorem diag_apply (hK : Hyp K) {k : 𝕍 ≃ᵃ[ZMod 2] 𝕍} (hk : k ∈ K) (B : 𝕍) :
    symThreeDiag (k B : M₃) = indLin k (symThreeDiag (B : M₃)) + symThreeDiag (k 0 : M₃) := by
  rw [aff_apply k B, AddSubgroup.coe_add, symThreeDiag_add, diag_linear_apply hK hk]

theorem indLin_mul (hK : Hyp K) {k : 𝕍 ≃ᵃ[ZMod 2] 𝕍} (hk : k ∈ K) (k' : 𝕍 ≃ᵃ[ZMod 2] 𝕍)
    (e : 𝔼) : indLin (k * k') e = indLin k (indLin k' e) := by
  rw [indLin_apply, linear_mul]
  exact diag_linear_apply hK hk _

theorem indLin_one (e : 𝔼) : indLin 1 e = e :=
  symThreeDiag_diagSection e

theorem indLin_congr (D : GL (Fin 3) (ZMod 2)) (e : 𝔼) :
    indLin (toAff (symThreeCongrHom D)) e = (D : M₃) *ᵥ e := by
  rw [indLin_apply, toAff_linear, symThreeCongrHom_apply, symThreeDiag_coe_congr,
    symThreeDiag_diagSection]

theorem gl_eq_one_of_mulVec (D : GL (Fin 3) (ZMod 2)) (h : ∀ e : 𝔼, (D : M₃) *ᵥ e = e) :
    D = 1 := by
  refine Units.ext ?_
  rw [Units.val_one, ← Matrix.toLin'.injective.eq_iff]
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, h, Matrix.toLin'_one, LinearMap.id_apply]

@[expose] noncomputable def glOfUnit (u : (𝔼 →ₗ[ZMod 2] 𝔼)ˣ) : GL (Fin 3) (ZMod 2) :=
  Matrix.GeneralLinearGroup.toLin.symm u

theorem glOfUnit_mulVec (u : (𝔼 →ₗ[ZMod 2] 𝔼)ˣ) (e : 𝔼) :
    ((glOfUnit u : GL (Fin 3) (ZMod 2)) : M₃) *ᵥ e = (u : 𝔼 →ₗ[ZMod 2] 𝔼) e := by
  have h := Matrix.GeneralLinearGroup.coe_toLin (glOfUnit u)
  rw [glOfUnit, MulEquiv.apply_symm_apply] at h
  rw [h]
  rfl

section Ind

variable {hK : Hyp K}

variable (hK) in
@[expose] noncomputable def indHom : K →* (𝔼 →ₗ[ZMod 2] 𝔼)ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun k => indLin k.1
      map_one' := LinearMap.ext indLin_one
      map_mul' := fun k k' => LinearMap.ext fun e => indLin_mul hK k.2 k'.1 e }

theorem indHom_apply (k : K) (e : 𝔼) :
    ((indHom hK k : (𝔼 →ₗ[ZMod 2] 𝔼)ˣ) : 𝔼 →ₗ[ZMod 2] 𝔼) e = indLin k.1 e :=
  rfl

variable (hK) in
@[expose] noncomputable def pSub : Subgroup (𝕍 ≃ᵃ[ZMod 2] 𝕍) :=
  (indHom hK).ker.map K.subtype

theorem mem_pSub {p : 𝕍 ≃ᵃ[ZMod 2] 𝕍} : p ∈ pSub hK ↔ p ∈ K ∧ ∀ e, indLin p e = e := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k.2, fun e => ?_⟩
    have h1 := congrArg (fun u : (𝔼 →ₗ[ZMod 2] 𝔼)ˣ => (u : 𝔼 →ₗ[ZMod 2] 𝔼) e)
      (MonoidHom.mem_ker.mp hk)
    exact h1
  · rintro ⟨hp, h⟩
    exact ⟨⟨p, hp⟩, MonoidHom.mem_ker.mpr (Units.ext (LinearMap.ext h)), rfl⟩

theorem pSub_le : pSub hK ≤ K := fun _ hp => (mem_pSub.mp hp).1

theorem diag_apply_of_mem_pSub {p : 𝕍 ≃ᵃ[ZMod 2] 𝕍} (hp : p ∈ pSub hK) (B : 𝕍) :
    symThreeDiag (p B : M₃) = symThreeDiag (B : M₃) + symThreeDiag (p 0 : M₃) := by
  rw [diag_apply hK (mem_pSub.mp hp).1, (mem_pSub.mp hp).2]

theorem diag_linear_of_mem_pSub {p : 𝕍 ≃ᵃ[ZMod 2] 𝕍} (hp : p ∈ pSub hK) (B : 𝕍) :
    symThreeDiag (p.linear B : M₃) = symThreeDiag (B : M₃) := by
  rw [diag_linear_apply hK (mem_pSub.mp hp).1, (mem_pSub.mp hp).2]

theorem conj_mem_pSub {k p : 𝕍 ≃ᵃ[ZMod 2] 𝕍} (hk : k ∈ K) (hp : p ∈ pSub hK) :
    k * p * k⁻¹ ∈ pSub hK := by
  obtain ⟨hpK, hp1⟩ := mem_pSub.mp hp
  refine mem_pSub.mpr ⟨K.mul_mem (K.mul_mem hk hpK) (K.inv_mem hk), fun e => ?_⟩
  rw [indLin_mul hK (K.mul_mem hk hpK), indLin_mul hK hk, hp1, ← indLin_mul hK hk,
    mul_inv_cancel, indLin_one]

theorem eq_one_of_mem_pSub {p : 𝕍 ≃ᵃ[ZMod 2] 𝕍} (hp : p ∈ pSub hK) (h0 : p 0 = 0) : p = 1 := by
  obtain ⟨D, hD⟩ := linear_mem_of_apply_zero hK (mem_pSub.mp hp).1 h0
  have hD1 : D = 1 := gl_eq_one_of_mulVec D fun e => by
    rw [← indLin_congr, show toAff (symThreeCongrHom D) = p by
      rw [hD, eq_toAffineEquiv_of_apply_zero h0]; rfl]
    exact (mem_pSub.mp hp).2 e
  rw [eq_toAffineEquiv_of_apply_zero h0, ← hD, hD1, map_one]
  rfl

theorem eq_of_mem_pSub {p p' : 𝕍 ≃ᵃ[ZMod 2] 𝕍} (hp : p ∈ pSub hK) (hp' : p' ∈ pSub hK)
    (h : p 0 = p' 0) : p = p' := by
  have h1 := eq_one_of_mem_pSub ((pSub hK).mul_mem ((pSub hK).inv_mem hp') hp) (by
      change p'.symm (p 0) = 0
      rw [AffineEquiv.symm_apply_eq, h])
  rw [← mul_inv_cancel_left p' p, h1, mul_one]

theorem exists_mem_pSub_apply_zero (A : 𝕍) : ∃ p ∈ pSub hK, p 0 = A := by
  obtain ⟨k, hk, hk0⟩ := hK.trans 0 A
  let D := glOfUnit (indHom hK ⟨k, hk⟩)
  refine ⟨k * toAff (symThreeCongrHom D⁻¹), mem_pSub.mpr ⟨K.mul_mem hk (congr_mem hK _),
    fun e => ?_⟩, ?_⟩
  · rw [indLin_mul hK hk, indLin_congr]
    have h := glOfUnit_mulVec (indHom hK ⟨k, hk⟩) (((D⁻¹ : GL (Fin 3) (ZMod 2)) : M₃) *ᵥ e)
    rw [indHom_apply] at h
    rw [← h, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  · change k (symThreeCongrHom D⁻¹ 0) = A
    rw [map_zero, hk0]

theorem card_pSub : Nat.card (pSub hK) = 64 := by
  rw [← card_symThree]
  refine Nat.card_congr (Equiv.ofBijective (fun p : pSub hK => p.1 0)
    ⟨fun p p' h => Subtype.ext (eq_of_mem_pSub p.2 p'.2 h), fun A => ?_⟩)
  obtain ⟨p, hp, hpA⟩ := exists_mem_pSub_apply_zero (hK := hK) A
  exact ⟨⟨p, hp⟩, hpA⟩

theorem isPGroup_pSub : IsPGroup 2 (pSub hK) :=
  IsPGroup.of_card (n := 6) card_pSub

theorem linear_fix_alt {p : 𝕍 ≃ᵃ[ZMod 2] 𝕍} (hp : p ∈ pSub hK) {i : 𝕍}
    (hi : symThreeDiag (i : M₃) = 0) : p.linear i = i := by
  let Gp := (pSub hK).map (AffineEquiv.linearHom : (𝕍 ≃ᵃ[ZMod 2] 𝕍) →* (𝕍 ≃ₗ[ZMod 2] 𝕍))
  have hGp : IsPGroup 2 Gp := isPGroup_pSub.map _
  obtain ⟨v₀, hv₀, hfix⟩ := exists_fixed_ne_of_isPGroup_two hGp (α := 𝕍)
    (by rw [card_symThree]; norm_num) 0 fun g => map_zero (g : 𝕍 ≃ₗ[ZMod 2] 𝕍)
  let C : AddSubgroup 𝕍 :=
    { carrier := {B | ∀ q ∈ pSub hK, q.linear B = B}
      add_mem' := fun {B B'} hB hB' q hq => by
        change q.linear (B + B') = B + B'
        rw [map_add, hB q hq, hB' q hq]
      zero_mem' := fun q _ => map_zero _
      neg_mem' := fun {B} hB q hq => by
        change q.linear (-B) = -B
        rw [neg_eq_self]
        exact hB q hq }
  have hv₀C : v₀ ∈ C := fun q hq => hfix ⟨q.linear, ⟨q, hq, rfl⟩⟩
  have hCinv : IsSymThreeCongrInvariant (C : Set 𝕍) := by
    intro D B hB q hq
    have hq' : (toAff (symThreeCongrHom D))⁻¹ * q * toAff (symThreeCongrHom D) ∈ pSub hK := by
      have h := conj_mem_pSub (hK := hK) (K.inv_mem (congr_mem hK D)) hq
      rwa [inv_inv] at h
    have h1 : (symThreeCongrHom D).symm (q.linear (symThreeCongrHom D B)) = B := hB _ hq'
    have h2 := congrArg (symThreeCongrHom D) h1
    rw [LinearEquiv.apply_symm_apply] at h2
    exact h2
  rcases invariant_addSubgroup C hCinv with hC | hC | hC
  · exfalso
    rw [hC] at hv₀C
    exact hv₀ hv₀C
  · exact (hC i).2 hi p hp
  · have hiC : i ∈ C := hC ▸ AddSubgroup.mem_top i
    exact hiC p hp

theorem tau_diag {p : 𝕍 ≃ᵃ[ZMod 2] 𝕍} (hp : p ∈ pSub hK) (B : 𝕍) :
    symThreeDiag ((p.linear B + B : 𝕍) : M₃) = 0 := by
  rw [AddSubgroup.coe_add, symThreeDiag_add, diag_linear_of_mem_pSub hp]
  funext k
  exact symThree_zmod_add_self _

theorem linear_linear_apply {p q : 𝕍 ≃ᵃ[ZMod 2] 𝕍} (hp : p ∈ pSub hK) (hq : q ∈ pSub hK)
    (B : 𝕍) : p.linear (q.linear B) = p.linear B + (q.linear B + B) := by
  conv_lhs => rw [show q.linear B = B + (q.linear B + B) by
    rw [add_left_comm, symThree_add_self, add_zero]]
  rw [map_add, linear_fix_alt hp (tau_diag hq B)]

theorem linear_linear_comm {p q : 𝕍 ≃ᵃ[ZMod 2] 𝕍} (hp : p ∈ pSub hK) (hq : q ∈ pSub hK)
    (B : 𝕍) : p.linear (q.linear B) = q.linear (p.linear B) := by
  rw [linear_linear_apply hp hq, linear_linear_apply hq hp]
  abel

theorem mul_eq_tr_mul {p q : 𝕍 ≃ᵃ[ZMod 2] 𝕍} (hp : p ∈ pSub hK) (hq : q ∈ pSub hK) :
    p * q = tr (p.linear (q 0) + q 0 + (q.linear (p 0) + p 0)) * (q * p) := by
  refine AffineEquiv.ext fun B => ?_
  have e1 : (p * q) B = p.linear (q.linear B) + p.linear (q 0) + p 0 := by
    rw [AffineEquiv.coe_mul, Function.comp_apply, aff_apply p (q B), aff_apply q B, map_add]
  have e2 : (q * p) B = q.linear (p.linear B) + q.linear (p 0) + q 0 := by
    rw [AffineEquiv.coe_mul, Function.comp_apply, aff_apply q (p B), aff_apply p B, map_add]
  rw [e1, AffineEquiv.coe_mul, Function.comp_apply, tr_apply, e2, linear_linear_comm hp hq]
  have key : ∀ a b c d e : 𝕍, a + b + c = b + d + (e + c) + (a + e + d) := by
    intro a b c d e
    have h : b + d + (e + c) + (a + e + d) = a + b + c + (d + d) + (e + e) := by abel
    rw [h, symThree_add_self, symThree_add_self, add_zero, add_zero]
  exact key _ _ _ _ _

theorem transSub_ne_bot (hK : Hyp K) : transSub K ≠ ⊥ := by
  intro hT
  let i₀ : 𝕍 := symThreePolarSym ![1, 0, 0] ![0, 1, 0]
  have hi₀ : symThreeDiag (i₀ : M₃) = 0 := symThreeDiag_polarSym _ _
  have hi₀0 : i₀ ≠ 0 := by decide
  by_cases hc : ∃ p ∈ pSub hK, ∃ q ∈ pSub hK, p.linear (q 0) + q 0 + (q.linear (p 0) + p 0) ≠ 0
  · obtain ⟨p, hp, q, hq, hne⟩ := hc
    have hmem : p.linear (q 0) + q 0 + (q.linear (p 0) + p 0) ∈ transSub K := by
      rw [mem_transSub, eq_mul_inv_of_mul_eq (mul_eq_tr_mul hp hq).symm]
      exact K.mul_mem (K.mul_mem (pSub_le hp) (pSub_le hq))
        (K.inv_mem (K.mul_mem (pSub_le hq) (pSub_le hp)))
    rw [hT, AddSubgroup.mem_bot] at hmem
    exact hne hmem
  · push Not at hc
    obtain ⟨n, hn, hn0⟩ := exists_mem_pSub_apply_zero (hK := hK) i₀
    have hlin : n.linear = 1 := by
      refine LinearEquiv.ext fun B => ?_
      obtain ⟨p, hp, hp0⟩ := exists_mem_pSub_apply_zero (hK := hK) B
      have h := hc p hp n hn
      rw [hn0, linear_fix_alt hp hi₀, symThree_add_self, zero_add, hp0] at h
      exact symThree_eq_of_add_eq_zero h
    have htr : n = tr i₀ := AffineEquiv.ext fun x => by
      rw [aff_apply, hlin, hn0, tr_apply, add_comm]
      rfl
    have hmem : i₀ ∈ transSub K := by
      rw [mem_transSub, ← htr]
      exact pSub_le hn
    rw [hT, AddSubgroup.mem_bot] at hmem
    exact hi₀0 hmem

theorem tr_mem_of_alt (hK : Hyp K) {i : 𝕍} (hi : symThreeDiag (i : M₃) = 0) : tr i ∈ K := by
  rcases invariant_addSubgroup (transSub K) (transSub_invariant hK) with hT | hT | hT
  · exact absurd hT (transSub_ne_bot hK)
  · exact (hT i).2 hi
  · exact (hT ▸ AddSubgroup.mem_top i : i ∈ transSub K)

theorem tr_symm_apply (v x : 𝕍) : (tr v).symm x = v + x := by
  rw [AffineEquiv.constVAdd_symm, tr_apply, neg_eq_self]

theorem mem_altTranslations_of_diag (hK : Hyp K) {k : 𝕍 ≃ᵃ[ZMod 2] 𝕍} (hk : k ∈ K)
    (h : ∀ B : 𝕍, symThreeDiag (k B : M₃) = symThreeDiag (B : M₃)) :
    k ∈ symThreeAltTranslations := by
  have hi : symThreeDiag (k 0 : M₃) = 0 := h 0
  have hk' : (tr (k 0))⁻¹ * k ∈ K := K.mul_mem (K.inv_mem (tr_mem_of_alt hK hi)) hk
  have hk'0 : ((tr (k 0))⁻¹ * k) 0 = 0 := by
    change (tr (k 0)).symm (k 0) = 0
    rw [tr_symm_apply, symThree_add_self]
  obtain ⟨D, hD⟩ := linear_mem_of_apply_zero hK hk' hk'0
  have hD1 : D = 1 := gl_eq_one_of_mulVec D fun e => by
    have h1 : symThreeDiag (((tr (k 0))⁻¹ * k) (symThreeDiagSection e) : M₃) = e := by
      change symThreeDiag ((tr (k 0)).symm (k (symThreeDiagSection e)) : M₃) = e
      rw [tr_symm_apply, AddSubgroup.coe_add, symThreeDiag_add, hi, zero_add, h,
        symThreeDiag_diagSection]
    calc (D : M₃) *ᵥ e = symThreeDiag (symThreeCongrHom D (symThreeDiagSection e) : M₃) := by
          rw [symThreeCongrHom_apply, symThreeDiag_coe_congr, symThreeDiag_diagSection]
      _ = symThreeDiag (((tr (k 0))⁻¹ * k).linear (symThreeDiagSection e) : M₃) := by rw [hD]
      _ = symThreeDiag ((((tr (k 0))⁻¹ * k) (symThreeDiagSection e)) : M₃) := by
          rw [aff_apply ((tr (k 0))⁻¹ * k) (symThreeDiagSection e), hk'0, add_zero]
      _ = e := h1
  refine ⟨k 0, hi, ?_⟩
  have hk'1 : (tr (k 0))⁻¹ * k = 1 := by
    rw [eq_toAffineEquiv_of_apply_zero hk'0, ← hD, hD1, map_one]
    rfl
  calc k = tr (k 0) * ((tr (k 0))⁻¹ * k) := by group
    _ = tr (k 0) := by rw [hk'1, mul_one]

theorem tau_add (p : 𝕍 ≃ᵃ[ZMod 2] 𝕍) (B C : 𝕍) :
    p.linear (B + C) + (B + C) = (p.linear B + B) + (p.linear C + C) := by
  rw [map_add]
  abel

theorem tau_alt {p : 𝕍 ≃ᵃ[ZMod 2] 𝕍} (hp : p ∈ pSub hK) {i : 𝕍}
    (hi : symThreeDiag (i : M₃) = 0) : p.linear i + i = 0 := by
  rw [linear_fix_alt hp hi, symThree_add_self]

theorem tau_eq_diag {p : 𝕍 ≃ᵃ[ZMod 2] 𝕍} (hp : p ∈ pSub hK) (B : 𝕍) :
    p.linear B + B = p.linear (symThreeDiagSection (symThreeDiag (B : M₃))) +
      symThreeDiagSection (symThreeDiag (B : M₃)) := by
  have hB : B = symThreeDiagSection (symThreeDiag (B : M₃)) +
      (B + symThreeDiagSection (symThreeDiag (B : M₃))) := by
    rw [add_left_comm, symThree_add_self, add_zero]
  conv_lhs => rw [hB]
  rw [tau_add, tau_alt hp (symThreeDiag_add_diagSection B), add_zero]

theorem tau_mul {p q : 𝕍 ≃ᵃ[ZMod 2] 𝕍} (hp : p ∈ pSub hK) (hq : q ∈ pSub hK) (B : 𝕍) :
    (p * q).linear B + B = (p.linear B + B) + (q.linear B + B) := by
  rw [linear_mul]
  change p.linear (q.linear B) + B = _
  rw [linear_linear_apply hp hq]
  abel

theorem vec_eq_of_add_eq_zero {x y : 𝔼} (h : x + y = 0) : x = y := by
  funext k
  have h1 := congrFun h k
  have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  exact key _ _ h1

theorem linear_eq_of_diag {p q : 𝕍 ≃ᵃ[ZMod 2] 𝕍} (hp : p ∈ pSub hK) (hq : q ∈ pSub hK)
    (h : symThreeDiag (p 0 : M₃) = symThreeDiag (q 0 : M₃)) : p.linear = q.linear := by
  have hqi : q⁻¹ ∈ pSub hK := (pSub hK).inv_mem hq
  have hqp : q⁻¹ * p ∈ pSub hK := (pSub hK).mul_mem hqi hp
  have hqinv : symThreeDiag (q⁻¹ 0 : M₃) = symThreeDiag (q 0 : M₃) := by
    have h1 := diag_apply_of_mem_pSub hq (q⁻¹ 0)
    rw [show q (q⁻¹ 0) = 0 from q.apply_symm_apply 0] at h1
    exact vec_eq_of_add_eq_zero h1.symm
  have hdiag : ∀ B : 𝕍, symThreeDiag ((q⁻¹ * p) B : M₃) = symThreeDiag (B : M₃) := by
    intro B
    have h2 : symThreeDiag ((q⁻¹ * p) 0 : M₃) = 0 := by
      rw [AffineEquiv.coe_mul, Function.comp_apply, diag_apply_of_mem_pSub hqi, hqinv, h]
      funext k
      exact symThree_zmod_add_self _
    rw [diag_apply_of_mem_pSub hqp, h2, add_zero]
  obtain ⟨i, -, hi⟩ := mem_altTranslations_of_diag hK (pSub_le hqp) hdiag
  have hlin : (q⁻¹ * p).linear = 1 := by
    rw [hi]
    exact tr_linear i
  calc p.linear = (q * (q⁻¹ * p)).linear := by rw [mul_inv_cancel_left]
    _ = q.linear * (q⁻¹ * p).linear := linear_mul _ _
    _ = q.linear := by rw [hlin, mul_one]

theorem exists_eq_twoCoreMap : ∃ κ : ZMod 2, ∀ p ∈ pSub hK, p = symThreeTwoCoreMap κ (p 0) := by
  choose pE hpE hpE0 using fun a : 𝔼 =>
    exists_mem_pSub_apply_zero (hK := hK) (symThreeDiagSection a)
  have hδE : ∀ a, symThreeDiag (pE a 0 : M₃) = a := fun a => by
    rw [hpE0, symThreeDiag_diagSection]
  let t : 𝔼 → 𝔼 → 𝕍 := fun a e =>
    (pE a).linear (symThreeDiagSection e) + symThreeDiagSection e
  have hadd₁ : ∀ a a' e, t (a + a') e = t a e + t a' e := by
    intro a a' e
    have hmul := (pSub hK).mul_mem (hpE a) (hpE a')
    have hl : (pE (a + a')).linear = (pE a * pE a').linear := linear_eq_of_diag (hpE _) hmul (by
      rw [hδE, AffineEquiv.coe_mul, Function.comp_apply, diag_apply_of_mem_pSub (hpE a), hδE,
        hδE, add_comm])
    change (pE (a + a')).linear (symThreeDiagSection e) + symThreeDiagSection e = _
    rw [hl, tau_mul (hpE a) (hpE a')]
  have hadd₂ : ∀ a e e', t a (e + e') = t a e + t a e' := by
    intro a e e'
    change (pE a).linear (symThreeDiagSection (e + e')) + symThreeDiagSection (e + e') = _
    rw [map_add, tau_add]
  have hI : ∀ a e, symThreeDiag (t a e : M₃) = 0 := fun a e => tau_diag (hpE a) _
  have heq : ∀ (D : GL (Fin 3) (ZMod 2)) a e,
      t ((D : M₃) *ᵥ a) ((D : M₃) *ᵥ e) = symThreeCongr D (t a e) := by
    intro D a e
    have hq := conj_mem_pSub (hK := hK) (congr_mem hK D) (hpE a)
    have hq0 : symThreeDiag ((toAff (symThreeCongrHom D) * pE a * (toAff (symThreeCongrHom D))⁻¹)
        0 : M₃) = (D : M₃) *ᵥ a := by
      change symThreeDiag (symThreeCongrHom D (pE a ((symThreeCongrHom D).symm 0)) : M₃) = _
      rw [map_zero, hpE0, symThreeCongrHom_apply, symThreeDiag_coe_congr,
        symThreeDiag_diagSection]
    have hl := linear_eq_of_diag (hpE ((D : M₃) *ᵥ a)) hq (by rw [hδE, hq0])
    let Y := (symThreeCongrHom D).symm (symThreeDiagSection ((D : M₃) *ᵥ e))
    have hY : symThreeDiag (Y : M₃) = e := by
      change symThreeDiag (symThreeCongr D⁻¹ (symThreeDiagSection ((D : M₃) *ᵥ e)) : M₃) = e
      rw [symThreeDiag_coe_congr, symThreeDiag_diagSection, mulVec_mulVec, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, one_mulVec]
    have hYe := tau_eq_diag (hpE a) Y
    rw [hY] at hYe
    change (pE ((D : M₃) *ᵥ a)).linear (symThreeDiagSection ((D : M₃) *ᵥ e)) +
      symThreeDiagSection ((D : M₃) *ᵥ e) = symThreeCongrHom D ((pE a).linear
        (symThreeDiagSection e) + symThreeDiagSection e)
    rw [hl, ← hYe, map_add, show symThreeCongrHom D Y = symThreeDiagSection ((D : M₃) *ᵥ e) from
      LinearEquiv.apply_symm_apply _ _]
    rfl
  obtain ⟨κ, hκ⟩ := eq_smul_polar_of_equivariant t hadd₁ hadd₂ hI heq
  refine ⟨κ, fun p hp => AffineEquiv.ext fun B => ?_⟩
  rw [symThreeTwoCoreMap_apply, aff_apply p B]
  have hl := linear_eq_of_diag hp (hpE (symThreeDiag (p 0 : M₃))) (by rw [hδE])
  have h1 : p.linear B + B = κ • symThreePolarSym (symThreeDiag (p 0 : M₃))
      (symThreeDiag (B : M₃)) := by
    rw [tau_eq_diag hp B, hl, ← hκ]
  calc p.linear B + p 0 = (p.linear B + B) + B + p 0 := by
        rw [add_assoc (p.linear B) B B, symThree_add_self, add_zero]
    _ = B + p 0 + κ • symThreePolarSym (symThreeDiag (p 0 : M₃)) (symThreeDiag (B : M₃)) := by
        rw [h1]
        abel

theorem pSub_eq_twoCoreGroup {κ : ZMod 2}
    (hκ : ∀ p ∈ pSub hK, p = symThreeTwoCoreMap κ (p 0)) :
    pSub hK = symThreeTwoCoreGroup κ := by
  ext p
  constructor
  · intro hp
    exact ⟨p 0, (hκ p hp).symm⟩
  · rintro ⟨A, rfl⟩
    obtain ⟨p, hp, hpA⟩ := exists_mem_pSub_apply_zero (hK := hK) A
    rw [← hpA, ← hκ p hp]
    exact hp

theorem le_ker_indHom {N : Subgroup K} (hN : N.Normal) (hNp : IsPGroup 2 N) :
    N ≤ (indHom hK).ker := by
  let Q := N.map (indHom hK)
  have hQ : IsPGroup 2 Q := hNp.map _
  obtain ⟨x₀, hx₀, hfix⟩ := exists_fixed_ne_of_isPGroup_two hQ (α := 𝔼)
    (by rw [Nat.card_eq_fintype_card]; decide) 0 fun q => map_zero
      ((q : (𝔼 →ₗ[ZMod 2] 𝔼)ˣ) : 𝔼 →ₗ[ZMod 2] 𝔼)
  have hx₀N : ∀ n ∈ N, indLin (n : 𝕍 ≃ᵃ[ZMod 2] 𝕍) x₀ = x₀ := fun n hn =>
    hfix ⟨indHom hK n, n, hn, rfl⟩
  have hinv : ∀ x : 𝔼, (∀ n ∈ N, indLin (n : 𝕍 ≃ᵃ[ZMod 2] 𝕍) x = x) →
      ∀ D : GL (Fin 3) (ZMod 2), ∀ n ∈ N, indLin (n : 𝕍 ≃ᵃ[ZMod 2] 𝕍) ((D : M₃) *ᵥ x) =
        (D : M₃) *ᵥ x := by
    intro x hx D n hn
    let h : K := ⟨toAff (symThreeCongrHom D), congr_mem hK D⟩
    have hn' : h⁻¹ * n * h ∈ N := by
      have := hN.conj_mem n hn h⁻¹
      rwa [inv_inv] at this
    have h1 := hx _ hn'
    change indLin ((toAff (symThreeCongrHom D))⁻¹ * ((n : 𝕍 ≃ᵃ[ZMod 2] 𝕍) *
      toAff (symThreeCongrHom D))) x = x at h1
    rw [indLin_mul hK (K.inv_mem (congr_mem hK D)),
      indLin_mul hK n.2, indLin_congr] at h1
    have h2 := congrArg (indLin (toAff (symThreeCongrHom D))) h1
    rw [← indLin_mul hK (congr_mem hK D), mul_inv_cancel, indLin_one, indLin_congr] at h2
    exact h2
  have hall : ∀ y : 𝔼, ∀ n ∈ N, indLin (n : 𝕍 ≃ᵃ[ZMod 2] 𝕍) y = y := by
    intro y n hn
    by_cases hy : y = 0
    · rw [hy, map_zero]
    · obtain ⟨e₁, he₁, hne₁⟩ := exists_ne_zero_ne x₀
      obtain ⟨D₁, hD₁, -⟩ := exists_gl_pair hx₀ he₁ hne₁
      obtain ⟨e₂, he₂, hne₂⟩ := exists_ne_zero_ne y
      obtain ⟨D₂, hD₂, -⟩ := exists_gl_pair hy he₂ hne₂
      have hinv1 : ((D₁⁻¹ : GL (Fin 3) (ZMod 2)) : M₃) *ᵥ x₀ = ![1, 0, 0] := by
        rw [← hD₁, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
      have hD : ((D₂ * D₁⁻¹ : GL (Fin 3) (ZMod 2)) : M₃) *ᵥ x₀ = y := by
        rw [Units.val_mul, ← mulVec_mulVec, hinv1, hD₂]
      rw [← hD]
      exact hinv x₀ hx₀N _ n hn
  intro n hn
  rw [MonoidHom.mem_ker]
  exact Units.ext (LinearMap.ext fun y => hall y n hn)

theorem pCoreOf_eq_pSub : CFSG.Assembly.pCoreOf 2 K = pSub hK := by
  rw [CFSG.Open.pCoreOf, CFSG.pCore_eq_iSup]
  apply le_antisymm
  · exact Subgroup.map_mono (iSup_le fun N => iSup_le fun hN => iSup_le fun hp =>
      le_ker_indHom hN hp)
  · refine Subgroup.map_mono (le_iSup_of_le _ (le_iSup_of_le (MonoidHom.normal_ker _)
      (le_iSup_of_le ?_ le_rfl)))
    refine IsPGroup.of_card (n := 6) ?_
    rw [← Subgroup.card_map_of_injective K.subtype_injective]
    exact card_pSub

end Ind

theorem isElemAbelian_twoCoreGroup (κ : ZMod 2) :
    CFSG.Assembly.IsElemAbelian 2 (symThreeTwoCoreGroup κ) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨A, hA⟩ := x.2
    obtain ⟨A', hA'⟩ := y.2
    change x.1 * y.1 = y.1 * x.1
    rw [← hA, ← hA', symThreeTwoCoreMap_mul, symThreeTwoCoreMap_mul,
      show symThreePolarSym (symThreeDiag (A : M₃)) (symThreeDiag (A' : M₃)) =
        symThreePolarSym (symThreeDiag (A' : M₃)) (symThreeDiag (A : M₃)) from
          Subtype.ext (symThreePolar_comm _ _), add_comm A A']
  · rintro _ ⟨A, rfl⟩
    rw [sq, symThreeTwoCoreMap_mul, symThreePolarSym_self, smul_zero, add_zero, symThree_add_self,
      symThreeTwoCoreMap_zero]

theorem isElemAbelian_altTranslations :
    CFSG.Assembly.IsElemAbelian 2 symThreeAltTranslations := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨i, -, hi⟩ := x.2
    obtain ⟨j, -, hj⟩ := y.2
    change x.1 * y.1 = y.1 * x.1
    rw [hi, hj, ← tr_add, ← tr_add, add_comm]
  · rintro _ ⟨i, -, rfl⟩
    rw [sq, ← tr_add, symThree_add_self, tr_zero]

theorem card_alt : (Finset.univ.filter fun B : 𝕍 => symThreeDiag (B : M₃) = 0).card = 8 := by
  decide +kernel

theorem card_altTranslations : Nat.card symThreeAltTranslations = 8 := by
  classical
  have h : Nat.card {B : 𝕍 // symThreeDiag (B : M₃) = 0} = 8 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, card_alt]
  rw [← h]
  refine Nat.card_congr (Equiv.ofBijective (fun u : symThreeAltTranslations =>
    (⟨u.1 0, ?_⟩ : {B : 𝕍 // symThreeDiag (B : M₃) = 0})) ⟨fun u u' huu => ?_, fun B => ?_⟩)
  · obtain ⟨i, hi, hu⟩ := u.2
    rw [hu, tr_apply, add_zero]
    exact hi
  · obtain ⟨i, -, hu⟩ := u.2
    obtain ⟨j, -, hu'⟩ := u'.2
    have h1 := congrArg Subtype.val huu
    change u.1 0 = u'.1 0 at h1
    rw [hu, hu', tr_apply, tr_apply, add_zero, add_zero] at h1
    exact Subtype.ext (by rw [hu, hu', h1])
  · exact ⟨⟨tr B.1, B.1, B.2, rfl⟩, Subtype.ext (by
      change B.1 + 0 = B.1
      rw [add_zero])⟩

end SymThreeFullAffine

open SymThreeFullAffine in
theorem binary_symmetric_three_full_affine_orbit_two_core_and_actions
    (K : Subgroup (↥(binarySymMatrices 3) ≃ᵃ[ZMod 2] ↥(binarySymMatrices 3)))
    (htrans : ∀ x y : ↥(binarySymMatrices 3), ∃ k ∈ K, k x = y)
    (hK₀ : ∀ g : ↥(binarySymMatrices 3) ≃ₗ[ZMod 2] ↥(binarySymMatrices 3),
      g.toAffineEquiv ∈ K ↔ g ∈ symThreeCongrGroup) :
    ∃ κ : ZMod 2,
      (∀ A : ↥(binarySymMatrices 3), symThreeTwoCoreMap κ A ∈ K) ∧
      CFSG.Assembly.pCoreOf 2 K = symThreeTwoCoreGroup κ ∧
      (∀ A B : ↥(binarySymMatrices 3), symThreeTwoCoreMap κ A B =
        B + A + κ • symThreePolarSym (symThreeDiag (A : M₃)) (symThreeDiag (B : M₃))) ∧
      CFSG.Assembly.IsElemAbelian 2 (symThreeTwoCoreGroup κ) ∧
      Nat.card (symThreeTwoCoreGroup κ) = 64 ∧
      (∀ x y : ↥(binarySymMatrices 3), ∃! p, p ∈ symThreeTwoCoreGroup κ ∧ p x = y) ∧
      (∀ k ∈ K, ∀ p ∈ symThreeTwoCoreGroup κ, k * p * k⁻¹ ∈ symThreeTwoCoreGroup κ) ∧
      (∀ g ∈ symThreeCongrGroup, g.toAffineEquiv ∈ symThreeTwoCoreGroup κ → g = 1) ∧
      (∀ k ∈ K, ∃ p ∈ symThreeTwoCoreGroup κ, ∃ g ∈ symThreeCongrGroup,
        k = p * g.toAffineEquiv) ∧
      (∀ k ∈ K, ∀ B : ↥(binarySymMatrices 3), symThreeDiag (B : M₃) = 0 →
        symThreeDiag (k.linear B : M₃) = 0) ∧
      (∀ k ∈ K, ∃ D : GL (Fin 3) (ZMod 2), ∃ a : Fin 3 → ZMod 2, ∀ B : ↥(binarySymMatrices 3),
        symThreeDiag (k B : M₃) = (D : M₃) *ᵥ symThreeDiag (B : M₃) + a) ∧
      (∀ (D : GL (Fin 3) (ZMod 2)) (a : Fin 3 → ZMod 2), ∃ k ∈ K,
        ∀ B : ↥(binarySymMatrices 3),
          symThreeDiag (k B : M₃) = (D : M₃) *ᵥ symThreeDiag (B : M₃) + a) ∧
      (∀ k ∈ K, (∀ B : ↥(binarySymMatrices 3), symThreeDiag (k B : M₃) = symThreeDiag (B : M₃)) ↔
        k ∈ symThreeAltTranslations) ∧
      CFSG.Assembly.IsElemAbelian 2 symThreeAltTranslations ∧
      Nat.card symThreeAltTranslations = 8 ∧
      symThreeAltTranslations ≤ K ∧
      (∀ k ∈ K, ∀ u ∈ symThreeAltTranslations, k * u * k⁻¹ ∈ symThreeAltTranslations) ∧
      symThreeAltTranslations ≤ symThreeTwoCoreGroup κ ∧
      (∀ p ∈ symThreeTwoCoreGroup κ, ∃ a : Fin 3 → ZMod 2, ∀ B : ↥(binarySymMatrices 3),
        symThreeDiag (p B : M₃) = symThreeDiag (B : M₃) + a) ∧
      (∀ a : Fin 3 → ZMod 2, ∃ p ∈ symThreeTwoCoreGroup κ, ∀ B : ↥(binarySymMatrices 3),
        symThreeDiag (p B : M₃) = symThreeDiag (B : M₃) + a) := by
  have hK : Hyp K := ⟨htrans, hK₀⟩
  obtain ⟨κ, hκ⟩ := exists_eq_twoCoreMap (hK := hK)
  have hP := pSub_eq_twoCoreGroup hκ
  have hUP : symThreeAltTranslations ≤ pSub hK := by
    rintro _ ⟨i, hi, rfl⟩
    refine mem_pSub.mpr ⟨tr_mem_of_alt hK hi, fun e => ?_⟩
    rw [indLin_apply, tr_linear]
    exact symThreeDiag_diagSection e
  refine ⟨κ, fun A => pSub_le (hP ▸ ⟨A, rfl⟩ : symThreeTwoCoreMap κ A ∈ pSub hK),
    (pCoreOf_eq_pSub (hK := hK)).trans hP, symThreeTwoCoreMap_apply κ,
    isElemAbelian_twoCoreGroup κ, hP ▸ card_pSub, ?_, ?_, ?_, ?_,
    fun k hk B hB => linear_preserves_alt hK hk hB, ?_, ?_, ?_,
    isElemAbelian_altTranslations, card_altTranslations, ?_, ?_, hP ▸ hUP, ?_, ?_⟩
  ·
    intro x y
    rw [← hP]
    obtain ⟨p, hp, hp0⟩ := exists_mem_pSub_apply_zero (hK := hK) y
    obtain ⟨q, hq, hq0⟩ := exists_mem_pSub_apply_zero (hK := hK) x
    have hpq : (p * q⁻¹) x = y := by
      change p (q.symm x) = y
      rw [show q.symm x = 0 by rw [AffineEquiv.symm_apply_eq, hq0], hp0]
    have hfree : ∀ r ∈ pSub hK, ∀ r' ∈ pSub hK, r x = r' x → r = r' := by
      intro r hr r' hr' h
      have h1 := eq_of_mem_pSub ((pSub hK).mul_mem hr hq) ((pSub hK).mul_mem hr' hq) (by
        change r (q 0) = r' (q 0)
        rw [hq0, h])
      exact mul_right_cancel h1
    refine ⟨p * q⁻¹, ⟨(pSub hK).mul_mem hp ((pSub hK).inv_mem hq), hpq⟩, ?_⟩
    rintro r ⟨hr, hrx⟩
    exact hfree r hr _ ((pSub hK).mul_mem hp ((pSub hK).inv_mem hq)) (hrx.trans hpq.symm)
  ·
    intro k hk p hp
    rw [← hP] at hp ⊢
    exact conj_mem_pSub hk hp
  ·
    intro g _ hgP
    rw [← hP] at hgP
    have h1 := eq_one_of_mem_pSub hgP (map_zero g)
    exact LinearEquiv.ext fun x => congrArg (fun k : 𝕍 ≃ᵃ[ZMod 2] 𝕍 => k x) h1
  ·
    intro k hk
    obtain ⟨p, hp, hp0⟩ := exists_mem_pSub_apply_zero (hK := hK) (k 0)
    have h0 : (p⁻¹ * k) 0 = 0 := by
      change p.symm (k 0) = 0
      rw [AffineEquiv.symm_apply_eq, hp0]
    refine ⟨p, hP ▸ hp, (p⁻¹ * k).linear,
      linear_mem_of_apply_zero hK (K.mul_mem (K.inv_mem (pSub_le hp)) hk) h0, ?_⟩
    rw [← eq_toAffineEquiv_of_apply_zero h0, mul_inv_cancel_left]
  ·
    intro k hk
    refine ⟨glOfUnit (indHom hK ⟨k, hk⟩), symThreeDiag (k 0 : M₃), fun B => ?_⟩
    rw [diag_apply hK hk, glOfUnit_mulVec, indHom_apply]
  ·
    intro D a
    obtain ⟨p, hp, hp0⟩ := exists_mem_pSub_apply_zero (hK := hK) (symThreeDiagSection a)
    refine ⟨p * toAff (symThreeCongrHom D), K.mul_mem (pSub_le hp) (congr_mem hK D),
      fun B => ?_⟩
    change symThreeDiag (p (symThreeCongrHom D B) : M₃) = _
    rw [diag_apply_of_mem_pSub hp, hp0, symThreeDiag_diagSection, symThreeCongrHom_apply,
      symThreeDiag_coe_congr]
  ·
    intro k hk
    constructor
    · exact mem_altTranslations_of_diag hK hk
    · rintro ⟨i, hi, rfl⟩ B
      rw [tr_apply, AddSubgroup.coe_add, symThreeDiag_add, hi, zero_add]
  ·
    exact hUP.trans pSub_le
  ·
    rintro k hk _ ⟨i, hi, rfl⟩
    rw [conj_tr]
    exact ⟨_, linear_preserves_alt hK hk hi, rfl⟩
  ·
    intro p hp
    rw [← hP] at hp
    exact ⟨symThreeDiag (p 0 : M₃), diag_apply_of_mem_pSub hp⟩
  ·
    intro a
    obtain ⟨p, hp, hp0⟩ := exists_mem_pSub_apply_zero (hK := hK) (symThreeDiagSection a)
    refine ⟨p, hP ▸ hp, fun B => ?_⟩
    rw [diag_apply_of_mem_pSub hp, hp0, symThreeDiag_diagSection]

end CFSG.LocalAnalysis.ComponentInitial
