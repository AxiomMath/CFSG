module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearBorel
public import CFSG.CharacterTheory.Wreathed.CentralSL2.CompleteFamily

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization
open TwoRankLowerBound.Helpers

section Subgroups

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem semilinear_smul_eq (h : SemilinearExtension F b m hm heven Sigma hSigma) (x : Omega F) :
    h • x = h.left • fieldExtension F (h.right : F ≃+* F) x := by
  rw [semilinearExtension_smul_def, centralExtension_smul_def]
  change semilinearAction F b m hm heven Sigma hSigma ⟨h.left, h.right⟩ x = _
  rw [semilinearAction_mk]
  rfl

theorem semilinear_smul_none (h : SemilinearExtension F b m hm heven Sigma hSigma) :
    h • (none : Omega F) = h.left • (none : Omega F) := by
  rw [semilinear_smul_eq]
  rfl

theorem semilinear_smul_zero (h : SemilinearExtension F b m hm heven Sigma hSigma) :
    h • (some 0 : Omega F) = h.left • (some 0 : Omega F) := by
  rw [semilinear_smul_eq]
  change h.left • (some ((h.right : F ≃+* F) 0) : Omega F) = _
  rw [map_zero]

@[expose] noncomputable def semilinearBorel (S : Subgroup Sigma) :
    Subgroup (SemilinearExtension F b m hm heven Sigma hSigma) where
  carrier := {h | h.left ∈ borelSubgroup F b m hm heven ∧ h.right ∈ S}
  mul_mem' {x y} hx hy := ⟨(borelSubgroup F b m hm heven).mul_mem hx.1
    ((fieldAction_mem_borel_iff hSigma x.right y.left).mpr hy.1), S.mul_mem hx.2 hy.2⟩
  one_mem' := ⟨(borelSubgroup F b m hm heven).one_mem, S.one_mem⟩
  inv_mem' {x} hx := ⟨(fieldAction_mem_borel_iff hSigma x.right⁻¹ x.left⁻¹).mpr
    ((borelSubgroup F b m hm heven).inv_mem hx.1), S.inv_mem hx.2⟩

@[expose] noncomputable def semilinearTorus (S : Subgroup Sigma) :
    Subgroup (SemilinearExtension F b m hm heven Sigma hSigma) where
  carrier := {h | h.left ∈ splitTorus F b m hm heven ∧ h.right ∈ S}
  mul_mem' {x y} hx hy := ⟨(splitTorus F b m hm heven).mul_mem hx.1
    ((fieldAction_mem_splitTorus_iff hSigma x.right y.left).mpr hy.1), S.mul_mem hx.2 hy.2⟩
  one_mem' := ⟨(splitTorus F b m hm heven).one_mem, S.one_mem⟩
  inv_mem' {x} hx := ⟨(fieldAction_mem_splitTorus_iff hSigma x.right⁻¹ x.left⁻¹).mpr
    ((splitTorus F b m hm heven).inv_mem hx.1), S.inv_mem hx.2⟩

theorem mem_semilinearBorel_iff (S : Subgroup Sigma)
    (h : SemilinearExtension F b m hm heven Sigma hSigma) :
    h ∈ semilinearBorel hSigma S ↔ h.left ∈ borelSubgroup F b m hm heven ∧ h.right ∈ S :=
  Iff.rfl

theorem mem_semilinearTorus_iff (S : Subgroup Sigma)
    (h : SemilinearExtension F b m hm heven Sigma hSigma) :
    h ∈ semilinearTorus hSigma S ↔ h.left ∈ splitTorus F b m hm heven ∧ h.right ∈ S :=
  Iff.rfl

theorem semilinearBorel_le_inertia (S : Subgroup Sigma) :
    semilinearBorel hSigma S ≤ semilinearInertia (hm := hm) (heven := heven) S :=
  fun _ hx => hx.2

theorem semilinearTorus_le_borel (S : Subgroup Sigma) :
    semilinearTorus hSigma S ≤ semilinearBorel (hm := hm) (heven := heven) hSigma S :=
  fun _ hx => ⟨splitTorus_le_borel F b m hm heven hx.1, hx.2⟩

end Subgroups

section Twist

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem torusCharacter_comp_torusField {P : PrincipalSeriesParameter F b m} {σ : Sigma}
    (hσ : σ ∈ parameterStabilizer hSigma P) :
    (torusCharacter F b m hm heven P).comp (torusField hSigma σ) =
      torusCharacter F b m hm heven P := by
  have h := torusCharacter_fieldAction (hm := hm) (heven := heven) hSigma σ⁻¹ P
  rw [inv_inv, (mem_parameterStabilizer_iff hSigma P σ⁻¹).mp
    ((parameterStabilizer hSigma P).inv_mem hσ)] at h
  exact h

@[expose] noncomputable def borelLeft (S : Subgroup Sigma) :
    semilinearBorel (hm := hm) (heven := heven) hSigma S → borelSubgroup F b m hm heven :=
  fun x => ⟨(x : SemilinearExtension F b m hm heven Sigma hSigma).left, x.2.1⟩

@[expose] noncomputable def borelTwist (P : PrincipalSeriesParameter F b m) (S : Subgroup Sigma)
    (hS : S ≤ parameterStabilizer hSigma P) (ρ : S →* ℂˣ) :
    semilinearBorel (hm := hm) (heven := heven) hSigma S →* ℂˣ where
  toFun x := torusCharacter F b m hm heven P (borelProjection F b m hm heven
      (borelLeft hSigma S x)) *
    ρ ⟨(x : SemilinearExtension F b m hm heven Sigma hSigma).right, x.2.2⟩
  map_one' := by
    have h1 : borelLeft hSigma S (1 : semilinearBorel (hm := hm) (heven := heven) hSigma S) = 1 :=
      rfl
    have h2 : (⟨((1 : semilinearBorel (hm := hm) (heven := heven) hSigma S) :
        SemilinearExtension F b m hm heven Sigma hSigma).right, (1 : semilinearBorel (hm := hm)
          (heven := heven) hSigma S).2.2⟩ : S) = 1 := rfl
    rw [h1, h2, map_one, map_one, map_one, mul_one]
  map_mul' x y := by
    have h1 : borelLeft hSigma S (x * y) = borelLeft hSigma S x *
        ⟨fieldAction F b m hm heven Sigma hSigma
          (x : SemilinearExtension F b m hm heven Sigma hSigma).right
            (y : SemilinearExtension F b m hm heven Sigma hSigma).left,
          (fieldAction_mem_borel_iff hSigma _ _).mpr y.2.1⟩ := rfl
    have h2 : (⟨((x * y : semilinearBorel (hm := hm) (heven := heven) hSigma S) :
        SemilinearExtension F b m hm heven Sigma hSigma).right, (x * y).2.2⟩ : S) =
          ⟨(x : SemilinearExtension F b m hm heven Sigma hSigma).right, x.2.2⟩ *
          ⟨(y : SemilinearExtension F b m hm heven Sigma hSigma).right, y.2.2⟩ := rfl
    have h3 : borelProjection F b m hm heven ⟨fieldAction F b m hm heven Sigma hSigma
        (x : SemilinearExtension F b m hm heven Sigma hSigma).right
          (y : SemilinearExtension F b m hm heven Sigma hSigma).left,
        (fieldAction_mem_borel_iff hSigma _ _).mpr y.2.1⟩ =
          torusField hSigma (x : SemilinearExtension F b m hm heven Sigma hSigma).right
            (borelProjection F b m hm heven (borelLeft hSigma S y)) :=
      Subtype.ext (borelProjection_fieldAction hSigma _ (borelLeft hSigma S y))
    have h4 : torusCharacter F b m hm heven P (torusField hSigma
        (x : SemilinearExtension F b m hm heven Sigma hSigma).right
          (borelProjection F b m hm heven (borelLeft hSigma S y))) =
        torusCharacter F b m hm heven P (borelProjection F b m hm heven (borelLeft hSigma S y)) :=
      DFunLike.congr_fun (torusCharacter_comp_torusField hSigma (hS x.2.2)) _
    rw [h1, h2, map_mul, map_mul, map_mul, h3, h4]
    exact mul_mul_mul_comm _ _ _ _

theorem borelTwist_apply (P : PrincipalSeriesParameter F b m) (S : Subgroup Sigma)
    (hS : S ≤ parameterStabilizer hSigma P) (ρ : S →* ℂˣ)
    (x : semilinearBorel (hm := hm) (heven := heven) hSigma S) :
    borelTwist hSigma P S hS ρ x = torusCharacter F b m hm heven P
        (borelProjection F b m hm heven (borelLeft hSigma S x)) *
      ρ ⟨(x : SemilinearExtension F b m hm heven Sigma hSigma).right, x.2.2⟩ := rfl

@[expose] noncomputable def inertiaLinear (S : Subgroup Sigma) (ρ : S →* ℂˣ) :
    semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S →* ℂˣ :=
  ρ.comp ((SemidirectProduct.rightHom.comp (semilinearInertia S).subtype).codRestrict S
    fun x => x.2)

theorem inertiaLinear_apply (S : Subgroup Sigma) (ρ : S →* ℂˣ)
    (x : semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S) :
    inertiaLinear hSigma S ρ x =
      ρ ⟨(x : SemilinearExtension F b m hm heven Sigma hSigma).right, x.2⟩ := rfl

variable [Fintype F]

@[expose] noncomputable def principalTwist (P : PrincipalSeriesParameter F b m)
    (S : Subgroup Sigma) (hS : S ≤ parameterStabilizer hSigma P) (ρ : S →* ℂˣ) :
    SemilinearExtension F b m hm heven Sigma hSigma → ℂ :=
  inducedFunction (semilinearBorel hSigma S) fun x => (borelTwist hSigma P S hS ρ x : ℂ)

@[expose] noncomputable def inertiaTwist (P : PrincipalSeriesParameter F b m)
    (S : Subgroup Sigma) (hS : S ≤ parameterStabilizer hSigma P) (ρ : S →* ℂˣ) :
    semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S → ℂ :=
  inducedFunction ((semilinearBorel hSigma S).subgroupOf (semilinearInertia S))
    fun x => (borelTwist hSigma P S hS ρ
      ⟨(x.1 : SemilinearExtension F b m hm heven Sigma hSigma), x.2⟩ : ℂ)

theorem principalTwist_eq_induced (P : PrincipalSeriesParameter F b m) (S : Subgroup Sigma)
    (hS : S ≤ parameterStabilizer hSigma P) (ρ : S →* ℂˣ) :
    principalTwist (hm := hm) (heven := heven) hSigma P S hS ρ =
      inducedFunction (semilinearInertia S) (inertiaTwist hSigma P S hS ρ) :=
  (inducedFunction_stages (semilinearBorel_le_inertia hSigma S) _).symm

theorem inertiaTwist_eq_mul (P : PrincipalSeriesParameter F b m) (S : Subgroup Sigma)
    (hS : S ≤ parameterStabilizer hSigma P) (ρ : S →* ℂˣ) :
    inertiaTwist (hm := hm) (heven := heven) hSigma P S hS ρ =
      fun x => inertiaTwist hSigma P S hS 1 x * (inertiaLinear hSigma S ρ x : ℂ) := by
  funext x
  have hclass : BlocksIsClassFunction fun y : semilinearInertia (hm := hm) (heven := heven)
      (hSigma := hSigma) S => (inertiaLinear hSigma S ρ y : ℂ) := by
    intro g h
    dsimp only
    rw [map_mul, map_mul, map_inv, mul_comm (inertiaLinear hSigma S ρ h), mul_inv_cancel_right]
  rw [inertiaTwist, inertiaTwist, ← inducedFunction_mul_classFunction _ _ hclass]
  congr 1
  funext y
  rw [borelTwist_apply, borelTwist_apply, MonoidHom.one_apply, mul_one, Units.val_mul]
  rfl

end Twist

section Restriction

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

omit [Fintype F] in
theorem card_semilinearBorel (S : Subgroup Sigma) :
    Nat.card (semilinearBorel (hm := hm) (heven := heven) hSigma S) =
      Nat.card (borelSubgroup F b m hm heven) * Nat.card S := by
  rw [← Nat.card_prod]
  exact Nat.card_congr
    { toFun := fun x => (⟨(x : SemilinearExtension F b m hm heven Sigma hSigma).left, x.2.1⟩,
        ⟨(x : SemilinearExtension F b m hm heven Sigma hSigma).right, x.2.2⟩)
      invFun := fun p => ⟨⟨p.1.1, p.2.1⟩, p.1.2, p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem sum_semilinearInertia (S : Subgroup Sigma)
    (f : semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S → ℂ) :
    ∑ x, f x = ∑ n : CentralExtension F b m hm heven, ∑ τ : S, f ⟨⟨n, τ⟩, τ.2⟩ := by
  rw [← Fintype.sum_prod_type']
  let e : semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S ≃
      CentralExtension F b m hm heven × S :=
    { toFun := fun x => ((x : SemilinearExtension F b m hm heven Sigma hSigma).left,
        ⟨(x : SemilinearExtension F b m hm heven Sigma hSigma).right, x.2⟩)
      invFun := fun p =>
        ⟨(⟨p.1, (p.2 : Sigma)⟩ : SemilinearExtension F b m hm heven Sigma hSigma), p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Fintype.sum_equiv e _ _ fun _ => rfl

omit [Fintype F] in
theorem extendByZero_inertiaTwist_conj (P : PrincipalSeriesParameter F b m) (S : Subgroup Sigma)
    (hS : S ≤ parameterStabilizer hSigma P) (ρ : S →* ℂˣ) (g n : CentralExtension F b m hm heven)
    (hg : (SemidirectProduct.inl g : SemilinearExtension F b m hm heven Sigma hSigma) ∈
      semilinearInertia S) (τ : S) :
    extendByZero ((semilinearBorel hSigma S).subgroupOf (semilinearInertia S))
        (fun x => (borelTwist hSigma P S hS ρ
          ⟨(x.1 : SemilinearExtension F b m hm heven Sigma hSigma), x.2⟩ : ℂ))
        ((⟨⟨n, τ⟩, τ.2⟩ : semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S)⁻¹ *
          ⟨SemidirectProduct.inl g, hg⟩ * ⟨⟨n, τ⟩, τ.2⟩) =
      extendByZero (borelSubgroup F b m hm heven)
        (fun y => (borelInflation F b m hm heven (torusCharacter F b m hm heven P) y : ℂ))
        (n⁻¹ * g * n) := by
  set y : semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S :=
    (⟨⟨n, τ⟩, τ.2⟩ : semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S)⁻¹ *
      ⟨SemidirectProduct.inl g, hg⟩ * ⟨⟨n, τ⟩, τ.2⟩ with hy
  have hyH : (y : SemilinearExtension F b m hm heven Sigma hSigma) =
      (⟨n, τ⟩ : SemilinearExtension F b m hm heven Sigma hSigma)⁻¹ * SemidirectProduct.inl g *
        ⟨n, τ⟩ := rfl
  have hleft : (y : SemilinearExtension F b m hm heven Sigma hSigma).left =
      fieldAction F b m hm heven Sigma hSigma (τ : Sigma)⁻¹ (n⁻¹ * g * n) := by
    rw [hyH, conj_inl_left hSigma]
  have hright : (y : SemilinearExtension F b m hm heven Sigma hSigma).right = 1 := by
    rw [hyH]
    simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right,
      SemidirectProduct.right_inl, mul_one, inv_mul_cancel]
  by_cases hB : n⁻¹ * g * n ∈ borelSubgroup F b m hm heven
  · have hmem : y ∈ (semilinearBorel hSigma S).subgroupOf (semilinearInertia S) := by
      rw [Subgroup.mem_subgroupOf, mem_semilinearBorel_iff, hleft, hright]
      exact ⟨(fieldAction_mem_borel_iff hSigma _ _).mpr hB, S.one_mem⟩
    rw [extendByZero_of_mem _ _ hmem, extendByZero_of_mem _ _ hB, borelTwist_apply]
    have hL : borelLeft hSigma S ⟨(y : SemilinearExtension F b m hm heven Sigma hSigma), hmem⟩ =
        ⟨fieldAction F b m hm heven Sigma hSigma (τ : Sigma)⁻¹ (n⁻¹ * g * n),
          (fieldAction_mem_borel_iff hSigma _ _).mpr hB⟩ := Subtype.ext hleft
    have hπ : borelProjection F b m hm heven ⟨fieldAction F b m hm heven Sigma hSigma
        (τ : Sigma)⁻¹ (n⁻¹ * g * n), (fieldAction_mem_borel_iff hSigma _ _).mpr hB⟩ =
          torusField hSigma (τ : Sigma)⁻¹ (borelProjection F b m hm heven ⟨n⁻¹ * g * n, hB⟩) :=
      Subtype.ext (borelProjection_fieldAction hSigma _ ⟨n⁻¹ * g * n, hB⟩)
    have hρ : (⟨(y : SemilinearExtension F b m hm heven Sigma hSigma).right, hmem.2⟩ : S) = 1 :=
      Subtype.ext hright
    have hτ : (τ : Sigma)⁻¹ ∈ parameterStabilizer hSigma P := hS (S.inv_mem τ.2)
    rw [hL, hπ, hρ, map_one, mul_one,
      ← MonoidHom.comp_apply (torusCharacter F b m hm heven P) (torusField hSigma (τ : Sigma)⁻¹),
      torusCharacter_comp_torusField hSigma hτ]
    rfl
  · have hmem : y ∉ (semilinearBorel hSigma S).subgroupOf (semilinearInertia S) := by
      rw [Subgroup.mem_subgroupOf, mem_semilinearBorel_iff, hleft]
      exact fun h => hB ((fieldAction_mem_borel_iff hSigma _ _).mp h.1)
    rw [extendByZero_of_not_mem _ _ hmem, extendByZero_of_not_mem _ _ hB]

theorem inertiaTwist_inl (P : PrincipalSeriesParameter F b m) (S : Subgroup Sigma)
    (hS : S ≤ parameterStabilizer hSigma P) (ρ : S →* ℂˣ) (g : CentralExtension F b m hm heven)
    (hg : (SemidirectProduct.inl g : SemilinearExtension F b m hm heven Sigma hSigma) ∈
      semilinearInertia S) :
    inertiaTwist hSigma P S hS ρ ⟨SemidirectProduct.inl g, hg⟩ =
      principalSeries F b m hm heven (torusCharacter F b m hm heven P) g := by
  rw [inertiaTwist, inducedFunction_eq_extendByZero, sum_semilinearInertia hSigma S,
    principalSeries, inducedFunction_eq_extendByZero]
  simp_rw [extendByZero_inertiaTwist_conj hSigma P S hS ρ g _ hg]
  rw [Finset.sum_congr rfl fun n _ => Finset.sum_const _, ← Finset.smul_sum]
  have hcard : Nat.card ((semilinearBorel (hm := hm) (heven := heven) hSigma S).subgroupOf
      (semilinearInertia S)) = Nat.card (borelSubgroup F b m hm heven) * Nat.card S := by
    rw [← card_semilinearBorel hSigma S]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (semilinearBorel_le_inertia hSigma S)).toEquiv
  rw [hcard, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]
  have hS0 : (Nat.card S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hB0 : (Nat.card (borelSubgroup F b m hm heven) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  push_cast
  field_simp

end Restriction

section TwoPoint

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

@[expose] noncomputable def inertiaWeyl (S : Subgroup Sigma) :
    semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S :=
  ⟨SemidirectProduct.inl (weylElement F b m hm heven), S.one_mem⟩

@[expose] noncomputable def inertiaRep (S : Subgroup Sigma) (p : Omega F) :
    semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S :=
  p.elim 1 fun y => ⟨SemidirectProduct.inl (unipotentElement F b m hm heven y), S.one_mem⟩

omit [Fintype F] in
theorem mem_inertiaBorel_iff (S : Subgroup Sigma)
    (x : semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S) :
    x ∈ (semilinearBorel hSigma S).subgroupOf (semilinearInertia S) ↔
      x • (none : Omega F) = none := by
  rw [Subgroup.mem_subgroupOf, mem_semilinearBorel_iff, Subgroup.smul_def, semilinear_smul_none,
    ← mem_borelSubgroup_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩

omit [Fintype F] in
theorem mem_inertiaTorus_iff (S : Subgroup Sigma)
    (x : semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S) :
    x ∈ (semilinearTorus hSigma S).subgroupOf (semilinearInertia S) ↔
      x ∈ (semilinearBorel hSigma S).subgroupOf (semilinearInertia S) ∧
        x • (some 0 : Omega F) = some 0 := by
  rw [mem_inertiaBorel_iff, Subgroup.mem_subgroupOf, mem_semilinearTorus_iff, Subgroup.smul_def,
    Subgroup.smul_def, semilinear_smul_none, semilinear_smul_zero, mem_splitTorus_iff]
  exact ⟨fun h => ⟨h.1.1, h.1.2⟩, fun h => ⟨⟨h.1, h.2⟩, x.2⟩⟩

omit [Fintype F] in
theorem inertiaWeyl_smul_none (S : Subgroup Sigma) :
    inertiaWeyl (hm := hm) (heven := heven) hSigma S • (none : Omega F) = some 0 := by
  rw [Subgroup.smul_def, semilinear_smul_none]
  exact weylElement_smul_none F b m hm heven

omit [Fintype F] in
theorem inertiaRep_spec (S : Subgroup Sigma) (p : Omega F) (hp : p ≠ none) :
    inertiaRep (hm := hm) (heven := heven) hSigma S p ∈
        (semilinearBorel hSigma S).subgroupOf (semilinearInertia S) ∧
      inertiaRep (hm := hm) (heven := heven) hSigma S p • (some 0 : Omega F) = p := by
  cases p with
  | none => exact absurd rfl hp
  | some y =>
    refine ⟨?_, ?_⟩
    · rw [mem_inertiaBorel_iff, Subgroup.smul_def, semilinear_smul_none]
      exact unipotentElement_smul_none F b m hm heven y
    · rw [Subgroup.smul_def, semilinear_smul_zero]
      change unipotentElement F b m hm heven y • (some 0 : Omega F) = some y
      rw [unipotentElement_smul_some, zero_add]

omit [Fintype F] in
theorem inertiaWeyl_conj (S : Subgroup Sigma)
    (x : semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S) :
    (((inertiaWeyl hSigma S)⁻¹ * x * inertiaWeyl hSigma S :
      semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S) :
        SemilinearExtension F b m hm heven Sigma hSigma) =
      ⟨(weylElement F b m hm heven)⁻¹ * (x : SemilinearExtension F b m hm heven Sigma hSigma).left *
        weylElement F b m hm heven,
        (x : SemilinearExtension F b m hm heven Sigma hSigma).right⟩ := by
  have hcoe : (((inertiaWeyl hSigma S)⁻¹ * x * inertiaWeyl hSigma S :
      semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S) :
        SemilinearExtension F b m hm heven Sigma hSigma) =
      (SemidirectProduct.inl (weylElement F b m hm heven))⁻¹ *
        (x : SemilinearExtension F b m hm heven Sigma hSigma) *
          SemidirectProduct.inl (weylElement F b m hm heven) := rfl
  rw [hcoe]
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.inv_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, SemidirectProduct.mul_right, SemidirectProduct.inv_right,
      inv_one, map_one, MulAut.one_apply, fieldAction_weylElement hSigma]
  · simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right,
      SemidirectProduct.right_inl, inv_one, one_mul, mul_one]

end TwoPoint

section Inner

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

@[expose] noncomputable def borelTwistB (P : PrincipalSeriesParameter F b m) (S : Subgroup Sigma)
    (hS : S ≤ parameterStabilizer hSigma P) (ρ : S →* ℂˣ) :
    (semilinearBorel (hm := hm) (heven := heven) hSigma S).subgroupOf (semilinearInertia S) →*
      ℂˣ :=
  (borelTwist hSigma P S hS ρ).comp
    (Subgroup.subgroupOfEquivOfLe (semilinearBorel_le_inertia hSigma S)).toMonoidHom

omit [Fintype F] in
theorem torus_mem_borel (S : Subgroup Sigma)
    (l : (semilinearTorus (hm := hm) (heven := heven) hSigma S).subgroupOf
      (semilinearInertia S)) :
    (l.1 : SemilinearExtension F b m hm heven Sigma hSigma) ∈ semilinearBorel hSigma S :=
  semilinearTorus_le_borel hSigma S (Subgroup.mem_subgroupOf.mp l.2)

omit [Fintype F] in
theorem torus_conj_mem_borel (S : Subgroup Sigma)
    (l : (semilinearTorus (hm := hm) (heven := heven) hSigma S).subgroupOf
      (semilinearInertia S)) :
    (((inertiaWeyl hSigma S)⁻¹ * l.1 * inertiaWeyl hSigma S :
      semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S) :
        SemilinearExtension F b m hm heven Sigma hSigma) ∈ semilinearBorel hSigma S := by
  have hl := Subgroup.mem_subgroupOf.mp l.2
  rw [inertiaWeyl_conj, mem_semilinearBorel_iff]
  exact ⟨splitTorus_le_borel F b m hm heven (weyl_conj_mem_splitTorus F b m hm heven hl.1), hl.2⟩

@[expose] noncomputable def torusToBorel (S : Subgroup Sigma) :
    (semilinearTorus (hm := hm) (heven := heven) hSigma S).subgroupOf (semilinearInertia S) →*
      semilinearBorel (hm := hm) (heven := heven) hSigma S where
  toFun l := ⟨l.1, torus_mem_borel hSigma S l⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def torusConjBorel (S : Subgroup Sigma) :
    (semilinearTorus (hm := hm) (heven := heven) hSigma S).subgroupOf (semilinearInertia S) →*
      semilinearBorel (hm := hm) (heven := heven) hSigma S where
  toFun l := ⟨((inertiaWeyl hSigma S)⁻¹ * l.1 * inertiaWeyl hSigma S :
    semilinearInertia S), torus_conj_mem_borel hSigma S l⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := by
    apply Subtype.ext
    show (((inertiaWeyl hSigma S)⁻¹ * (x * y).1 * inertiaWeyl hSigma S :
        semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S) :
          SemilinearExtension F b m hm heven Sigma hSigma) =
      (((inertiaWeyl hSigma S)⁻¹ * x.1 * inertiaWeyl hSigma S :
        semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S) :
          SemilinearExtension F b m hm heven Sigma hSigma) *
      (((inertiaWeyl hSigma S)⁻¹ * y.1 * inertiaWeyl hSigma S :
        semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S) :
          SemilinearExtension F b m hm heven Sigma hSigma)
    rw [← Subgroup.coe_mul]
    congr 1
    rw [Subgroup.coe_mul]
    group

@[expose] noncomputable def borelTwistL (P : PrincipalSeriesParameter F b m) (S : Subgroup Sigma)
    (hS : S ≤ parameterStabilizer hSigma P) (ρ : S →* ℂˣ) :
    (semilinearTorus (hm := hm) (heven := heven) hSigma S).subgroupOf (semilinearInertia S) →*
      ℂˣ :=
  (borelTwist hSigma P S hS ρ).comp (torusToBorel hSigma S)

@[expose] noncomputable def borelTwistLw (P : PrincipalSeriesParameter F b m)
    (S : Subgroup Sigma) (hS : S ≤ parameterStabilizer hSigma P) (ρ : S →* ℂˣ) :
    (semilinearTorus (hm := hm) (heven := heven) hSigma S).subgroupOf (semilinearInertia S) →*
      ℂˣ :=
  (borelTwist hSigma P S hS ρ).comp (torusConjBorel hSigma S)

theorem inner_inertiaTwist (P P' : PrincipalSeriesParameter F b m) (S : Subgroup Sigma)
    (hS : S ≤ parameterStabilizer hSigma P) (hS' : S ≤ parameterStabilizer hSigma P')
    (ρ ρ' : S →* ℂˣ) :
    BlocksInnerProduct (inertiaTwist (hm := hm) (heven := heven) hSigma P S hS ρ)
        (inertiaTwist hSigma P' S hS' ρ') =
      (if borelTwistB (hm := hm) (heven := heven) hSigma P S hS ρ =
          borelTwistB hSigma P' S hS' ρ' then 1 else 0) +
        (if borelTwistL (hm := hm) (heven := heven) hSigma P S hS ρ =
          borelTwistLw hSigma P' S hS' ρ' then 1 else 0) := by
  rw [← blocksInnerProduct_units_hom, ← blocksInnerProduct_units_hom, inertiaTwist, inertiaTwist,
    blocksInnerProduct_inducedFunction_twoPoint' (mem_inertiaBorel_iff hSigma S) (some 0)
      (inertiaWeyl hSigma S) (inertiaWeyl_smul_none hSigma S) (Option.some_ne_none 0)
      (inertiaRep hSigma S) (inertiaRep_spec hSigma S) (mem_inertiaTorus_iff hSigma S)]
  · congr 1
  · intro s t
    change (borelTwistB hSigma P S hS ρ (s * t * s⁻¹) : ℂ) = borelTwistB hSigma P S hS ρ t
    rw [map_mul, map_mul, map_inv, mul_comm (borelTwistB hSigma P S hS ρ s), mul_inv_cancel_right]
  · intro s t
    change (borelTwistB hSigma P' S hS' ρ' (s * t * s⁻¹) : ℂ) = borelTwistB hSigma P' S hS' ρ' t
    rw [map_mul, map_mul, map_inv, mul_comm (borelTwistB hSigma P' S hS' ρ' s),
      mul_inv_cancel_right]

end Inner

section Weyl

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

omit [Fintype F] in
theorem borelTwistL_apply (P : PrincipalSeriesParameter F b m) (S : Subgroup Sigma)
    (hS : S ≤ parameterStabilizer hSigma P) (ρ : S →* ℂˣ)
    (l : (semilinearTorus (hm := hm) (heven := heven) hSigma S).subgroupOf
      (semilinearInertia S)) :
    borelTwistL hSigma P S hS ρ l = torusCharacter F b m hm heven P
        ⟨(l.1 : SemilinearExtension F b m hm heven Sigma hSigma).left,
          (Subgroup.mem_subgroupOf.mp l.2).1⟩ *
      ρ ⟨(l.1 : SemilinearExtension F b m hm heven Sigma hSigma).right,
        (Subgroup.mem_subgroupOf.mp l.2).2⟩ := by
  change borelTwist hSigma P S hS ρ (torusToBorel hSigma S l) = _
  rw [borelTwist_apply]
  congr 2
  exact borelProjection_of_mem_splitTorus F b m hm heven _ (Subgroup.mem_subgroupOf.mp l.2).1

omit [Fintype F] in
theorem borelTwistLw_apply (P : PrincipalSeriesParameter F b m) (S : Subgroup Sigma)
    (hS : S ≤ parameterStabilizer hSigma P) (ρ : S →* ℂˣ)
    (l : (semilinearTorus (hm := hm) (heven := heven) hSigma S).subgroupOf
      (semilinearInertia S)) :
    borelTwistLw hSigma P S hS ρ l = torusCharacter F b m hm heven P
        (weylConj F b m hm heven ⟨(l.1 : SemilinearExtension F b m hm heven Sigma hSigma).left,
          (Subgroup.mem_subgroupOf.mp l.2).1⟩) *
      ρ ⟨(l.1 : SemilinearExtension F b m hm heven Sigma hSigma).right,
        (Subgroup.mem_subgroupOf.mp l.2).2⟩ := by
  change borelTwist hSigma P S hS ρ (torusConjBorel hSigma S l) = _
  rw [borelTwist_apply]
  have hconj := inertiaWeyl_conj hSigma S l.1
  have hT : (weylElement F b m hm heven)⁻¹ *
      (l.1 : SemilinearExtension F b m hm heven Sigma hSigma).left * weylElement F b m hm heven ∈
        splitTorus F b m hm heven :=
    weyl_conj_mem_splitTorus F b m hm heven (Subgroup.mem_subgroupOf.mp l.2).1
  congr 1
  congr 1
  apply Subtype.ext
  rw [borelProjection_of_mem_splitTorus F b m hm heven _ (by
    change (((inertiaWeyl hSigma S)⁻¹ * l.1 * inertiaWeyl hSigma S :
      semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S) :
        SemilinearExtension F b m hm heven Sigma hSigma).left ∈ _
    rw [hconj]
    exact hT)]
  change (((inertiaWeyl hSigma S)⁻¹ * l.1 * inertiaWeyl hSigma S :
    semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S) :
      SemilinearExtension F b m hm heven Sigma hSigma).left = _
  rw [hconj]
  rfl

@[expose] noncomputable def torusPoint (S : Subgroup Sigma) (t : splitTorus F b m hm heven) :
    (semilinearTorus (hm := hm) (heven := heven) hSigma S).subgroupOf (semilinearInertia S) :=
  ⟨⟨SemidirectProduct.inl (t : CentralExtension F b m hm heven), S.one_mem⟩, t.2, S.one_mem⟩

omit [Fintype F] in
theorem borelTwistL_torusPoint (P : PrincipalSeriesParameter F b m) (S : Subgroup Sigma)
    (hS : S ≤ parameterStabilizer hSigma P) (ρ : S →* ℂˣ) (t : splitTorus F b m hm heven) :
    borelTwistL hSigma P S hS ρ (torusPoint hSigma S t) = torusCharacter F b m hm heven P t := by
  rw [borelTwistL_apply]
  have h1 : (⟨((torusPoint hSigma S t).1 : SemilinearExtension F b m hm heven Sigma hSigma).right,
      (Subgroup.mem_subgroupOf.mp (torusPoint hSigma S t).2).2⟩ : S) = 1 := rfl
  rw [h1, map_one, mul_one]
  rfl

omit [Fintype F] in
theorem borelTwistLw_torusPoint (P : PrincipalSeriesParameter F b m) (S : Subgroup Sigma)
    (hS : S ≤ parameterStabilizer hSigma P) (ρ : S →* ℂˣ) (t : splitTorus F b m hm heven) :
    borelTwistLw hSigma P S hS ρ (torusPoint hSigma S t) =
      torusCharacter F b m hm heven P (weylConj F b m hm heven t) := by
  rw [borelTwistLw_apply]
  have h1 : (⟨((torusPoint hSigma S t).1 : SemilinearExtension F b m hm heven Sigma hSigma).right,
      (Subgroup.mem_subgroupOf.mp (torusPoint hSigma S t).2).2⟩ : S) = 1 := rfl
  rw [h1, map_one, mul_one]
  rfl

omit [Fintype F] in
theorem borelTwistB_torusPoint (P : PrincipalSeriesParameter F b m) (S : Subgroup Sigma)
    (hS : S ≤ parameterStabilizer hSigma P) (ρ : S →* ℂˣ) (t : splitTorus F b m hm heven) :
    borelTwistB hSigma P S hS ρ ⟨(torusPoint hSigma S t).1,
      torus_mem_borel hSigma S (torusPoint hSigma S t)⟩ = torusCharacter F b m hm heven P t :=
  borelTwistL_torusPoint hSigma P S hS ρ t

theorem inertiaTwist_norm (hb : ¬ IsSquare b) {P : PrincipalSeriesParameter F b m}
    (hP : P.1.1 ≠ 1) (S : Subgroup Sigma) (hS : S ≤ parameterStabilizer hSigma P)
    (ρ : S →* ℂˣ) :
    BlocksInnerProduct (inertiaTwist (hm := hm) (heven := heven) hSigma P S hS ρ)
      (inertiaTwist hSigma P S hS ρ) = 1 := by
  rw [inner_inertiaTwist, ite_eq_left rfl, ite_eq_right, add_zero]
  intro h
  apply ne_weylParameter F b m heven hb hP
  apply torusCharacter_injective F b m hm heven
  rw [← torusCharacter_comp_weylConj]
  refine MonoidHom.ext fun t => ?_
  have h1 := DFunLike.congr_fun h (torusPoint hSigma S t)
  rw [borelTwistL_torusPoint, borelTwistLw_torusPoint] at h1
  exact h1

theorem inertiaTwist_inner_weyl (hb : ¬ IsSquare b) {P : PrincipalSeriesParameter F b m}
    (hP : P.1.1 ≠ 1) (S : Subgroup Sigma) (hS : S ≤ parameterStabilizer hSigma P)
    (hS' : S ≤ parameterStabilizer hSigma (weylParameter F b m heven P)) (ρ : S →* ℂˣ) :
    BlocksInnerProduct (inertiaTwist (hm := hm) (heven := heven) hSigma P S hS ρ)
      (inertiaTwist hSigma (weylParameter F b m heven P) S hS' ρ) = 1 := by
  rw [inner_inertiaTwist, ite_eq_right, ite_eq_left, zero_add]
  · refine MonoidHom.ext fun l => ?_
    rw [borelTwistL_apply, borelTwistLw_apply, ← MonoidHom.comp_apply
      (torusCharacter F b m hm heven (weylParameter F b m heven P)),
      ← torusCharacter_comp_weylConj, MonoidHom.comp_apply, MonoidHom.comp_apply,
      weylConj_involutive]
  · intro h
    apply ne_weylParameter F b m heven hb hP
    apply torusCharacter_injective F b m hm heven
    refine MonoidHom.ext fun t => ?_
    have h1 := DFunLike.congr_fun h ⟨(torusPoint hSigma S t).1,
      torus_mem_borel hSigma S (torusPoint hSigma S t)⟩
    rw [borelTwistB_torusPoint, borelTwistB_torusPoint] at h1
    exact h1

theorem inertiaTwist_mem_blocksIrr (hb : ¬ IsSquare b) {P : PrincipalSeriesParameter F b m}
    (hP : P.1.1 ≠ 1) (S : Subgroup Sigma) (hS : S ≤ parameterStabilizer hSigma P)
    (ρ : S →* ℂˣ) :
    inertiaTwist (hm := hm) (heven := heven) hSigma P S hS ρ ∈
      BlocksIrr (semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S) := by
  have hlin : (fun x : (semilinearBorel (hm := hm) (heven := heven) hSigma S).subgroupOf
      (semilinearInertia S) => (borelTwist hSigma P S hS ρ
        ⟨(x.1 : SemilinearExtension F b m hm heven Sigma hSigma), x.2⟩ : ℂ)) ∈
        BlocksIrr ((semilinearBorel (hm := hm) (heven := heven) hSigma S).subgroupOf
          (semilinearInertia S)) :=
    monoidHom_mem_blocksIrr ((Units.coeHom ℂ).comp (borelTwistB hSigma P S hS ρ))
  obtain ⟨W, _, _, _, τ, hτ⟩ :=
    CFSG.Wreathed.exists_representation_inducedFunction _ hlin
  have h := CFSG.Wreathed.mem_blocksIrr_of_norm_one τ (by
    rw [hτ]
    exact inertiaTwist_norm hSigma hb hP S hS ρ)
  rw [hτ] at h
  exact h

theorem inertiaTwist_weyl (hb : ¬ IsSquare b) {P : PrincipalSeriesParameter F b m}
    (hP : P.1.1 ≠ 1) (S : Subgroup Sigma) (hS : S ≤ parameterStabilizer hSigma P)
    (hS' : S ≤ parameterStabilizer hSigma (weylParameter F b m heven P)) (ρ : S →* ℂˣ) :
    inertiaTwist (hm := hm) (heven := heven) hSigma (weylParameter F b m heven P) S hS' ρ =
      inertiaTwist hSigma P S hS ρ := by
  have h1 := inertiaTwist_mem_blocksIrr (hm := hm) (heven := heven) hSigma hb hP S hS ρ
  have h2 := inertiaTwist_mem_blocksIrr (hm := hm) (heven := heven) hSigma hb
    (weylParameter_ne_one F b m heven hP) S hS' ρ
  have h3 := blocksInnerProduct_irreducible ⟨_, h1⟩ ⟨_, h2⟩
  change BlocksInnerProduct (inertiaTwist hSigma P S hS ρ)
    (inertiaTwist hSigma (weylParameter F b m heven P) S hS' ρ) = _ at h3
  rw [inertiaTwist_inner_weyl hSigma hb hP S hS hS' ρ] at h3
  by_contra hne
  rw [ite_eq_right (fun h => hne (congrArg Subtype.val h).symm)] at h3
  exact one_ne_zero h3

end Weyl

end CFSG.Wreathed.CentralSL2
