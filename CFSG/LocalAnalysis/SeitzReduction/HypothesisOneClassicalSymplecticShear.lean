module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalShear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpInner

public section

namespace CFSG.SeitzReduction

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.ComponentClassification.CatalogueBSymplecticB

namespace SpShear

section Abstract

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : LinearMap.BilinForm K V}

theorem shear_comp_shear (hB : B.IsAlt) {W L : Submodule K V} (hWL : W ≤ L)
    (hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, B w v = 0) {w a b : V} (hw : w ∈ W) (ha : a ∈ L) (hb : b ∈ L)
    {g₁ g₂ : V → V} (h₁L : ∀ v ∈ L, g₁ v = v + B v a • w) (h₁W : ∀ v, g₁ v - v - B v w • a ∈ W)
    (h₂L : ∀ v ∈ L, g₂ v = v + B v b • w) (h₂W : ∀ v, g₂ v - v - B v w • b ∈ W) :
    (∀ v ∈ L, g₁ (g₂ v) = v + B v (a + b) • w) ∧ ∀ v, g₁ (g₂ v) - v - B v w • (a + b) ∈ W := by
  have hwa : B w a = 0 := (hL a).1 ha w hw
  have hbw : B b w = 0 := by rw [← hB.neg_eq, (hL b).1 hb w hw, neg_zero]
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · have h2L : g₂ v ∈ L := by
      rw [h₂L v hv]
      exact L.add_mem hv (L.smul_mem _ (hWL hw))
    rw [h₁L _ h2L, h₂L v hv, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hwa,
      smul_eq_mul, mul_zero, add_zero, map_add, add_smul]
    abel
  · have e : B (g₂ v) w = B v w := by
      have h3 : g₂ v = v + B v w • b + (g₂ v - v - B v w • b) := by abel
      rw [h3, map_add, map_add, map_smul, LinearMap.add_apply, LinearMap.add_apply,
        LinearMap.smul_apply, hbw, smul_eq_mul, mul_zero, add_zero,
        (hL w).1 (hWL hw) _ (h₂W v), add_zero]
    have h := W.add_mem (h₁W (g₂ v)) (h₂W v)
    rw [e] at h
    convert h using 1
    rw [smul_add]
    abel

theorem shearMap_shear (hB : B.IsAlt) {W L : Submodule K V}
    (hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, B w v = 0) {w : V} (hw : w ∈ W) (a : V) :
    (∀ v ∈ L, shearMap B w a v = v + B v a • w) ∧ ∀ v, shearMap B w a v - v - B v w • a ∈ W := by
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · have hvw : B v w = 0 := by rw [← hB.neg_eq, (hL v).1 hv w hw, neg_zero]
    rw [shearMap_apply, hvw, zero_smul, add_zero]
  · rw [shearMap_apply, show v + B v a • w + B v w • a - v - B v w • a = B v a • w by abel]
    exact W.smul_mem _ hw

theorem conj_shearIsometry_apply [CharP K 2] (hB : B.IsAlt) {w h : V} (hwh : B w h = 0)
    (g : isometryGroup B) (v : V) :
    ((g * shearIsometry hB hwh * g⁻¹ : isometryGroup B) : V ≃ₗ[K] V) v =
      shearMap B ((g : V ≃ₗ[K] V) w) ((g : V ≃ₗ[K] V) h) v := by
  have h1 : (g : V ≃ₗ[K] V) (((g⁻¹ : isometryGroup B) : V ≃ₗ[K] V) v) = v := by
    rw [← isometryGroup_mul_apply, mul_inv_cancel, isometryGroup_one_apply]
  have h2 : ∀ x, B (((g⁻¹ : isometryGroup B) : V ≃ₗ[K] V) v) x =
      B v ((g : V ≃ₗ[K] V) x) := by
    intro x
    rw [← isometryGroup_apply_apply g, h1]
  rw [isometryGroup_mul_apply, isometryGroup_mul_apply, shearIsometry_apply, map_add, map_add,
    map_smul, map_smul, h1, h2, h2, shearMap_apply]

theorem shearIsometry_mul_self [CharP K 2] (hB : B.IsAlt) {w h : V} (hwh : B w h = 0) :
    shearIsometry hB hwh * shearIsometry hB hwh = 1 :=
  isometryGroup_ext fun v => by
    rw [isometryGroup_mul_apply, isometryGroup_one_apply]
    exact shearMap_involutive hB hwh v

theorem binaryTransvection_mul_pow_three [CharP K 2] (hB : B.IsAlt) {x u : V} (hxu : B x u = 1) :
    (binaryTransvection hB x * binaryTransvection hB u) ^ 3 = 1 := by
  have hux : B u x = 1 := by rw [← hB.neg_eq, hxu, CharTwo.neg_eq]
  have h1 : binaryTransvection hB x * binaryTransvection hB u * binaryTransvection hB x =
      binaryTransvection hB (x + u) := by
    have h := conj_binaryTransvection hB (binaryTransvection hB x) u
    rw [binaryTransvection_inv, binaryTransvection_apply, hux, one_smul, add_comm] at h
    exact h
  have h2 : binaryTransvection hB u * binaryTransvection hB x * binaryTransvection hB u =
      binaryTransvection hB (x + u) := by
    have h := conj_binaryTransvection hB (binaryTransvection hB u) x
    rw [binaryTransvection_inv, binaryTransvection_apply, hxu, one_smul] at h
    exact h
  calc (binaryTransvection hB x * binaryTransvection hB u) ^ 3
      = (binaryTransvection hB x * binaryTransvection hB u * binaryTransvection hB x) *
          (binaryTransvection hB u * binaryTransvection hB x * binaryTransvection hB u) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (binaryTransvection hB u * binaryTransvection hB x * binaryTransvection hB u) *
          (binaryTransvection hB u * binaryTransvection hB x * binaryTransvection hB u) := by
        rw [h1, h2]
    _ = binaryTransvection hB u * binaryTransvection hB x *
          (binaryTransvection hB u * binaryTransvection hB u) * binaryTransvection hB x *
          binaryTransvection hB u := by group
    _ = 1 := by
        rw [binaryTransvection_mul_self, mul_one, mul_assoc (binaryTransvection hB u),
          binaryTransvection_mul_self, mul_one, binaryTransvection_mul_self]

theorem commute_of_fix_of_sub_mem {W L : Submodule K V} {s c : isometryGroup B}
    (hsL : ∀ v ∈ L, (s : V ≃ₗ[K] V) v = v) (hsW : ∀ v, (s : V ≃ₗ[K] V) v - v ∈ W)
    (hcW : ∀ w ∈ W, (c : V ≃ₗ[K] V) w = w) (hcL : ∀ v, (c : V ≃ₗ[K] V) v - v ∈ L) :
    c * s = s * c :=
  isometryGroup_ext fun v => by
    rw [isometryGroup_mul_apply, isometryGroup_mul_apply]
    have h1 := hcW _ (hsW v)
    have h2 := hsL _ (hcL v)
    rw [map_sub] at h1 h2
    linear_combination (norm := module) h1 - h2

theorem exists_apply_eq_one_of_not_mem [FiniteDimensional K V]
    (hBn : ∀ a : V, (∀ x, B x a = 0) → a = 0) (hB : B.IsAlt) {W L : Submodule K V}
    (hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, B w v = 0) {u : V} (huW : u ∉ W) :
    ∃ x ∈ L, B x u = 1 := by
  have h : ¬ ∀ l ∈ L, B l u = 0 := fun h =>
    huW ((ShearRigidity.mem_iff_forall_of_perp hBn hB hL u).2 h)
  push Not at h
  obtain ⟨l, hl, hlu⟩ := h
  exact ⟨(B l u)⁻¹ • l, L.smul_mem _ hl, by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hlu]⟩

theorem exists_shear_of_commute_odd [CharP K 2] [FiniteDimensional K V]
    (hBn : ∀ a : V, (∀ x, B x a = 0) → a = 0) (hB : B.IsAlt) {W L : Submodule K V}
    (hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, B w v = 0) (hWL : W ≤ L) {s : isometryGroup B}
    (hsL : ∀ v ∈ L, (s : V ≃ₗ[K] V) v = v) (hsW : ∀ v, (s : V ≃ₗ[K] V) v - v ∈ W)
    {F : Type*} [FunLike F V V] {T : F}
    (hTc : ∀ c : isometryGroup B, c * s = s * c → Odd (orderOf c) →
      ∀ v, T ((c : V ≃ₗ[K] V) v) = (c : V ≃ₗ[K] V) (T v))
    {w u : V} (hw : w ∈ W) (hu : u ∈ L) :
    ∃ g : V →+ V, (∀ v, T (g v) = g (T v)) ∧ (∀ v ∈ L, g v = v + B v u • w) ∧
      ∀ v, g v - v - B v w • u ∈ W := by
  by_cases huW : u ∈ W
  · refine ⟨AddMonoidHom.id V, fun v => rfl, fun v hv => ?_, fun v => ?_⟩
    · have hvu : B v u = 0 := by rw [← hB.neg_eq, (hL v).1 hv u huW, neg_zero]
      rw [AddMonoidHom.id_apply, hvu, zero_smul, add_zero]
    · rw [AddMonoidHom.id_apply, sub_self, zero_sub]
      exact W.neg_mem (W.smul_mem _ huW)
  obtain ⟨x, hx, hxu⟩ := exists_apply_eq_one_of_not_mem hBn hB hL huW
  have hh : x + u ∈ L := L.add_mem hx hu
  have hwh : B w (x + u) = 0 := (hL _).1 hh w hw
  set y := binaryTransvection hB x * binaryTransvection hB u with hy
  set X := shearIsometry hB hwh with hX
  have hτs : ∀ a ∈ L, binaryTransvection hB a * s = s * binaryTransvection hB a := by
    intro a ha
    refine commute_of_fix_of_sub_mem hsL hsW (fun w' hw' => ?_) (fun v => ?_)
    · rw [binaryTransvection_apply, (hL a).1 ha w' hw', zero_smul, add_zero]
    · rw [binaryTransvection_apply, add_sub_cancel_left]
      exact L.smul_mem _ ha
  have hys : y * s = s * y := by
    rw [hy, mul_assoc, hτs u hu, ← mul_assoc, hτs x hx, mul_assoc]
  have hyodd : Odd (orderOf y) :=
    Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one
      (binaryTransvection_mul_pow_three hB hxu))
  have hXs : X * s = s * X := by
    refine commute_of_fix_of_sub_mem hsL hsW (fun w' hw' => ?_) (fun v => ?_)
    · rw [hX, shearIsometry_apply, (hL _).1 hh w' hw', (hL w).1 (hWL hw) w' hw', zero_smul,
        zero_smul, add_zero, add_zero]
    · rw [hX, shearIsometry_apply, add_assoc, add_sub_cancel_left]
      exact L.add_mem (L.smul_mem _ (hWL hw)) (L.smul_mem _ hh)
  have hzs : X * y⁻¹ * X⁻¹ * s = s * (X * y⁻¹ * X⁻¹) := by
    have hXc : Commute X s := hXs
    have hyc : Commute y s := hys
    exact ((hXc.mul_left hyc.inv_left).mul_left hXc.inv_left).eq
  have hzodd : Odd (orderOf (X * y⁻¹ * X⁻¹)) := by
    rw [show X * y⁻¹ * X⁻¹ = MulAut.conj X y⁻¹ from rfl, MulEquiv.orderOf_eq, orderOf_inv]
    exact hyodd
  have hyw : (y : V ≃ₗ[K] V) w = w := by
    rw [hy, isometryGroup_mul_apply, binaryTransvection_apply, binaryTransvection_apply,
      (hL u).1 hu w hw, zero_smul, add_zero, (hL x).1 hx w hw, zero_smul, add_zero]
  have hyh : (y : V ≃ₗ[K] V) (x + u) = x := by
    rw [hy, isometryGroup_mul_apply, binaryTransvection_apply, binaryTransvection_apply]
    simp only [map_add, LinearMap.add_apply, hxu, hB.self_eq_zero, add_zero, one_smul, zero_add,
      CharTwo.add_self_eq_zero, zero_smul]
    rw [add_assoc, ShearRigidity.add_self_eq_zero K u, add_zero]
  have hact : ∀ v, ((y * (X * y⁻¹ * X⁻¹) : isometryGroup B) : V ≃ₗ[K] V) v =
      shearMap B w x (shearMap B w (x + u) v) := by
    intro v
    have hXinv : X⁻¹ = X := inv_eq_of_mul_eq_one_right (shearIsometry_mul_self hB hwh)
    rw [show y * (X * y⁻¹ * X⁻¹) = y * X * y⁻¹ * X by rw [hXinv]; group,
      isometryGroup_mul_apply, hX, conj_shearIsometry_apply, ← hX, hyw, hyh, hX,
      shearIsometry_apply, ← shearMap_apply]
  obtain ⟨hS1, hS2⟩ := shear_comp_shear hB hWL hL hw hx hh (shearMap_shear hB hL hw x).1
    (shearMap_shear hB hL hw x).2 (shearMap_shear hB hL hw (x + u)).1
    (shearMap_shear hB hL hw (x + u)).2
  have hxxu : x + (x + u) = u := by
    rw [← add_assoc, ShearRigidity.add_self_eq_zero K x, zero_add]
  refine ⟨((y * (X * y⁻¹ * X⁻¹) : isometryGroup B) : V ≃ₗ[K] V).toLinearMap.toAddMonoidHom,
    fun v => ?_, fun v hv => ?_, fun v => ?_⟩
  · change T (((y * (X * y⁻¹ * X⁻¹) : isometryGroup B) : V ≃ₗ[K] V) v) =
      ((y * (X * y⁻¹ * X⁻¹) : isometryGroup B) : V ≃ₗ[K] V) (T v)
    rw [isometryGroup_mul_apply y (X * y⁻¹ * X⁻¹) v, isometryGroup_mul_apply y _ (T v),
      hTc y hys hyodd, hTc _ hzs hzodd]
  · change ((y * (X * y⁻¹ * X⁻¹) : isometryGroup B) : V ≃ₗ[K] V) v = _
    rw [hact, hS1 v hv, hxxu]
  · change ((y * (X * y⁻¹ * X⁻¹) : isometryGroup B) : V ≃ₗ[K] V) v - v - B v w • u ∈ W
    have h := hS2 v
    rw [hxxu] at h
    rw [hact]
    exact h

end Abstract

end SpShear

open SpShear

section Abstract

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : LinearMap.BilinForm K V}

theorem semilinear_shear_rigidity_of_commute_odd [CharP K 2] [FiniteDimensional K V]
    (hBn : ∀ a : V, (∀ x, B x a = 0) → a = 0) (hB : B.IsAlt) {W L : Submodule K V}
    (hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, B w v = 0) (hWL : W ≤ L) (hW0 : W ≠ ⊥) (hWne : W ≠ L)
    {s : isometryGroup B} (hsL : ∀ v ∈ L, (s : V ≃ₗ[K] V) v = v)
    (hsW : ∀ v, (s : V ≃ₗ[K] V) v - v ∈ W)
    {F : Type*} [FunLike F V V] [AddMonoidHomClass F V V] {φ : K ≃+* K} (T : F)
    (hT : ∀ (a : K) v, T (a • v) = φ a • T v) (hTB : ∀ x y, B (T x) (T y) = φ (B x y))
    (hTL : ∀ v ∈ L, T v ∈ L)
    (hTc : ∀ c : isometryGroup B, c * s = s * c → Odd (orderOf c) →
      ∀ v, T ((c : V ≃ₗ[K] V) v) = (c : V ≃ₗ[K] V) (T v)) :
    (∀ a, φ a = a) ∧ ∀ v, T (T v) = v := by
  have hLW : ∃ x ∈ L, ∃ u ∈ L, B x u = 1 := by
    obtain ⟨u, huL, huW⟩ : ∃ u ∈ L, u ∉ W := by
      by_contra h
      push Not at h
      exact hWne (le_antisymm hWL h)
    obtain ⟨x, hx, hxu⟩ := exists_apply_eq_one_of_not_mem hBn hB hL huW
    exact ⟨x, hx, u, huL, hxu⟩
  exact semilinear_shear_rigidity_sq hBn hB hL hLW hW0 T hT hTB hTL
    fun w hw u hu => exists_shear_of_commute_odd hBn hB hL hWL hsL hsW hTc hw hu

end Abstract

section Standard

variable {r : ℕ} {K : Type} [Field K]

theorem SpShear.statedSpIsometryEquiv_apply (g : StatedSp r K) (v : Fin r ⊕ Fin r → K) :
    ((statedSpIsometryEquiv g : isometryGroup (pairedSympForm K r)) :
        (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) v = spMat g *ᵥ v :=
  rfl

theorem statedSp_semilinear_shear_rigidity_of_commute_odd [CharP K 2] {s : StatedSp r K}
    (hs : s * s = 1) (hs1 : s ≠ 1)
    (hW : displacement s ≠ (pairedSympForm K r).orthogonal (displacement s))
    {F : Type*} [FunLike F (Fin r ⊕ Fin r → K) (Fin r ⊕ Fin r → K)]
    [AddMonoidHomClass F (Fin r ⊕ Fin r → K) (Fin r ⊕ Fin r → K)] {φ : K ≃+* K} (T : F)
    (hT : ∀ (a : K) v, T (a • v) = φ a • T v)
    (hTB : ∀ x y, pairedSympForm K r (T x) (T y) = φ (pairedSympForm K r x y))
    (hTs : ∀ v, T (spMat s *ᵥ v) = spMat s *ᵥ T v)
    (hTc : ∀ c : StatedSp r K, c * s = s * c → Odd (orderOf c) →
      ∀ v, T (spMat c *ᵥ v) = spMat c *ᵥ T v) :
    (∀ a, φ a = a) ∧ ∀ v, T (T v) = v := by
  have hBn : ∀ a : Fin r ⊕ Fin r → K, (∀ x, pairedSympForm K r x a = 0) → a = 0 :=
    fun a h => SymplecticFlag.pairedSympForm_nondegenerate.2 a h
  have hL : ∀ v, v ∈ (pairedSympForm K r).orthogonal (displacement s) ↔
      ∀ w ∈ displacement s, pairedSympForm K r w v = 0 :=
    fun v => LinearMap.BilinForm.mem_orthogonal_iff
  have hWL : displacement s ≤ (pairedSympForm K r).orthogonal (displacement s) :=
    fun w hw => LinearMap.BilinForm.mem_orthogonal_iff.mpr fun n hn =>
      isTotallyIsotropic_displacement hs n hn w hw
  have hW0 : displacement s ≠ ⊥ := by
    intro hbot
    refine hs1 (statedSp_ext fun v => ?_)
    have h1 : spMat s *ᵥ v - v ∈ displacement s := mem_displacement.mpr ⟨v, rfl⟩
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at h1
    rw [h1]
    exact (one_mulVec v).symm
  have hsL : ∀ v ∈ (pairedSympForm K r).orthogonal (displacement s), spMat s *ᵥ v = v :=
    fun v hv => sub_eq_zero.mp (displacement_eq_zero_of_mem_orthogonal hs hv)
  have hLs : ∀ v, spMat s *ᵥ v = v → v ∈ (pairedSympForm K r).orthogonal (displacement s) := by
    intro v hv
    refine (hL v).2 fun w hw => ?_
    obtain ⟨x, rfl⟩ := mem_displacement.mp hw
    rw [pairedSympForm_displacement hs, hv, sub_self, map_zero]
  have hTL : ∀ v ∈ (pairedSympForm K r).orthogonal (displacement s),
      T v ∈ (pairedSympForm K r).orthogonal (displacement s) :=
    fun v hv => hLs _ (by rw [← hTs, hsL v hv])
  refine semilinear_shear_rigidity_of_commute_odd hBn pairedSympForm_isAlt hL hWL hW0 hW
    (s := statedSpIsometryEquiv s) (fun v hv => by rw [statedSpIsometryEquiv_apply, hsL v hv])
    (fun v => by rw [statedSpIsometryEquiv_apply]; exact mem_displacement.mpr ⟨v, rfl⟩)
    T hT hTB hTL ?_
  intro c hcs hodd v
  have h1 : statedSpIsometryEquiv.symm c * s = s * statedSpIsometryEquiv.symm c := by
    apply statedSpIsometryEquiv.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hcs]
  have h2 : Odd (orderOf (statedSpIsometryEquiv.symm c)) := by
    rwa [MulEquiv.orderOf_eq]
  have h3 := hTc _ h1 h2 v
  rwa [spMat_symm_mulVec, spMat_symm_mulVec] at h3

theorem sq_eq_one_of_mem_spSemilinearAutGroup_of_ne [Finite K] [CharP K 2] [NeZero r]
    {s : StatedSp r K} (hs : s * s = 1) (hs1 : s ≠ 1)
    (hW : displacement s ≠ (pairedSympForm K r).orthogonal (displacement s))
    {β : MulAut (StatedProj (StatedSp r K))} (hβE : β ∈ spSemilinearAutGroup r K)
    (hβx : β * spInner r K s = spInner r K s * β)
    (hβc : ∀ c : StatedProj (StatedSp r K), spInner r K s c = c → Odd (orderOf c) → β c = c) :
    β ^ 2 = 1 := by
  obtain ⟨g, φ, rfl⟩ := exists_eq_spInner_mul_fieldAut hβE
  have hcomm : ∀ x : StatedSp r K, spInner r K g * fieldAut r K φ * spInner r K x *
      (spInner r K g * fieldAut r K φ)⁻¹ = spInner r K x → g * fieldSp r K φ x = x * g := by
    intro x h
    rw [conj_spInner] at h
    have h1 := spInner_injective h
    calc g * fieldSp r K φ x = g * fieldSp r K φ x * g⁻¹ * g := by group
      _ = x * g := by rw [h1]
  have hgs : g * fieldSp r K φ s = s * g := hcomm s (by rw [hβx, mul_inv_cancel_right])
  have hgc : ∀ c : StatedSp r K, c * s = s * c → Odd (orderOf c) →
      g * fieldSp r K φ c = c * g := by
    intro c hcs hodd
    refine hcomm c ?_
    have hfix : (spInner r K g * fieldAut r K φ) (proj r K c) = proj r K c := by
      refine hβc _ ?_ (Odd.of_dvd_nat hodd (orderOf_map_dvd _ c))
      rw [spInner_eq_conj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, ← hcs,
        mul_inv_cancel_right]
    rw [spInner_eq_conj c, mul_conj_mul_inv_eq_conj, hfix]
  obtain ⟨hφ, hTT⟩ := statedSp_semilinear_shear_rigidity_of_commute_odd hs hs1 hW
    (semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ) (semilinearCoordMap_smul _ φ)
    (pairedSympForm_semilinearCoordMap g φ) (semilinearCoordMap_mulVec_of_mul_eq hgs)
    fun c hcs hodd => semilinearCoordMap_mulVec_of_mul_eq (hgc c hcs hodd)
  obtain rfl : φ = 1 := RingEquiv.ext hφ
  have hgg : g * g = 1 := statedSp_ext fun v => by
    rw [spMat_mul_mulVec]
    exact (hTT v).trans (one_mulVec v).symm
  rw [sq, spInner_mul_fieldAut_mul, map_one, MulAut.one_apply, hgg, mul_one, map_one, map_one,
    mul_one]

theorem involutionCriterion_spInner_of_ne [Finite K] [CharP K 2] (hr : 3 ≤ r)
    {s : StatedSp r K} (hs : s * s = 1) (hs1 : s ≠ 1)
    (hW : displacement s ≠ (pairedSympForm K r).orthogonal (displacement s)) :
    InvolutionCriterion (spInner r K s) := by
  have : NeZero r := ⟨by omega⟩
  intro β hβx hβc
  exact sq_eq_one_of_mem_spSemilinearAutGroup_of_ne hs hs1 hW
    (by rw [(automorphism_generation hr).1]; exact mem_top β) hβx hβc

end Standard

end CFSG.SeitzReduction
