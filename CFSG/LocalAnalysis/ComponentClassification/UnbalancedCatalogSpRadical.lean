module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpCommon
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenSymplectic

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher CatalogueBAlternatingIsometry CatalogueBSymplecticB
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace SpChain

section Abstract

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : LinearMap.BilinForm K V}

theorem exists_pair_eq_one (hBn : ∀ a : V, (∀ x, B x a = 0) → a = 0) {w : V} (hw : w ≠ 0) :
    ∃ x, B x w = 1 := by
  obtain ⟨x, hx⟩ : ∃ x, B x w ≠ 0 := by
    by_contra! h
    exact hw (hBn w h)
  exact ⟨(B x w)⁻¹ • x, by rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hx]⟩

theorem eq_one_of_mul_self_eq_one [CharP K 2] {c : K} (h : c * c = 1) : c = 1 := by
  have h2 : (c - 1) * (c - 1) = 0 := by
    linear_combination h + (1 - c) * (CharTwo.two_eq_zero : (2 : K) = 0)
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h2)

theorem eq_of_forall_smul_eq [CharP K 2] (hBn : ∀ a : V, (∀ x, B x a = 0) → a = 0) {u w : V}
    (hw : w ≠ 0) (h : ∀ x, B x u • u = B x w • w) : u = w := by
  obtain ⟨x, hx⟩ := exists_pair_eq_one hBn hw
  have hwu : w = B x u • u := by rw [h x, hx, one_smul]
  have hu : u ≠ 0 := by
    rintro rfl
    rw [smul_zero] at hwu
    exact hw hwu
  obtain ⟨y, hy⟩ := exists_pair_eq_one hBn hu
  have h2 := h y
  rw [hy, one_smul, hwu, map_smul, smul_eq_mul, hy, mul_one, smul_smul] at h2
  have hc : B x u * B x u = 1 := by
    have h3 : (1 - B x u * B x u) • u = 0 := by
      rw [sub_smul, one_smul, ← h2, sub_self]
    exact (sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hu)).symm
  rw [hwu, eq_one_of_mul_self_eq_one hc, one_smul]

theorem mem_span_of_forall_add_eq_zero (hBn : ∀ a : V, (∀ x, B x a = 0) → a = 0) {w x : V}
    (hw : w ≠ 0) (h : ∀ v, B v x • w + B v w • x = 0) : x ∈ K ∙ w := by
  obtain ⟨v, hv⟩ := exists_pair_eq_one hBn hw
  have h1 := h v
  rw [hv, one_smul] at h1
  exact Submodule.mem_span_singleton.mpr
    ⟨-B v x, by rw [neg_smul, neg_eq_iff_add_eq_zero]; exact h1⟩

theorem semilinear_flag_rigidity [CharP K 2] (hBn : ∀ a : V, (∀ x, B x a = 0) → a = 0)
    {W L : Submodule K V} (hW0 : W ≠ ⊥) (hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, B w v = 0)
    {φ : K ≃+* K} (T : V ≃+ V) (hT : ∀ (a : K) (v : V), T (a • v) = φ a • T v)
    (hTB : ∀ x y, B (T x) (T y) = φ (B x y))
    (htr : ∀ w ∈ W, ∀ v, T (v + B v w • w) = T v + B (T v) w • w)
    (hsh : ∀ w ∈ W, ∀ u ∈ L, ∀ v,
      T (v + B v u • w + B v w • u) = T v + B (T v) u • w + B (T v) w • u) :
    (∀ a, φ a = a) ∧ (∀ w ∈ W, T w = w) ∧ (∀ l ∈ L, T l - l ∈ W) ∧ ∀ v, T v - v ∈ L := by
  have hTW : ∀ w ∈ W, T w = w := by
    intro w hw
    by_cases hw0 : w = 0
    · rw [hw0, map_zero]
    refine eq_of_forall_smul_eq hBn hw0 fun y => ?_
    obtain ⟨v, rfl⟩ := T.surjective y
    have h1 := htr w hw v
    rw [map_add, hT, ← hTB, add_right_inj] at h1
    exact h1
  obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hφ : ∀ a, φ a = a := by
    intro a
    have h1 := hTW _ (W.smul_mem a hw₀)
    rw [hT, hTW w₀ hw₀] at h1
    exact smul_left_injective K hw₀0 h1
  have hTB' : ∀ x y, B (T x) (T y) = B x y := fun x y => by rw [hTB, hφ]
  have hTL : ∀ v, T v - v ∈ L := by
    intro v
    rw [hL]
    intro w hw
    have h1 := hTB' w v
    rw [hTW w hw] at h1
    rw [map_sub, h1, sub_self]
  refine ⟨hφ, hTW, fun l hl => ?_, hTL⟩
  have key : ∀ y, B y (T l - l) • w₀ + B y w₀ • (T l - l) = 0 := by
    intro y
    obtain ⟨v, rfl⟩ := T.surjective y
    have h1 := hsh w₀ hw₀ l hl v
    rw [map_add, map_add, hT, hT, hTW w₀ hw₀, hφ, hφ] at h1
    have e1 : B (T v) (T l) = B v l := hTB' v l
    have e2 : B (T v) w₀ = B v w₀ := by
      have h2 := hTB' v w₀
      rwa [hTW w₀ hw₀] at h2
    rw [map_sub, e1, e2]
    rw [e2] at h1
    linear_combination (norm := module) h1
  exact (Submodule.span_singleton_le_iff_mem _ _).mpr hw₀
    (mem_span_of_forall_add_eq_zero hBn hw₀0 key)

@[expose] def shearMap (B : LinearMap.BilinForm K V) (w u : V) : V →ₗ[K] V :=
  LinearMap.id + (B.flip u).smulRight w + (B.flip w).smulRight u

theorem shearMap_apply (w u v : V) :
    shearMap B w u v = v + B v u • w + B v w • u :=
  rfl

theorem shearMap_involutive [CharP K 2] (hB : B.IsAlt) {w u : V} (hwu : B w u = 0) :
    Function.Involutive (shearMap B w u) := by
  intro v
  have huw : B u w = 0 := by rw [← hB.neg_eq w u, hwu, neg_zero]
  simp only [shearMap_apply, map_add, map_smul, hwu, huw, hB.self_eq_zero]
  linear_combination (norm := module) (CharTwo.two_eq_zero : (2 : K) = 0) • (B v u • w + B v w • u)

theorem shearMap_isometry (hB : B.IsAlt) {w u : V} (hwu : B w u = 0) (x y : V) :
    B (shearMap B w u x) (shearMap B w u y) = B x y := by
  have huw : B u w = 0 := by rw [← hB.neg_eq w u, hwu, neg_zero]
  have hwy : B w y = -B y w := (hB.neg_eq y w).symm
  have huy : B u y = -B y u := (hB.neg_eq y u).symm
  simp only [shearMap_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hwu, huw, hB.self_eq_zero, hwy, huy]
  ring

@[expose] def shearIsometry [CharP K 2] (hB : B.IsAlt) {w u : V} (hwu : B w u = 0) :
    isometryGroup B :=
  ⟨LinearEquiv.ofInvolutive (shearMap B w u) (shearMap_involutive hB hwu),
    (mem_isometryGroup_iff B _).mpr (shearMap_isometry hB hwu)⟩

theorem shearIsometry_apply [CharP K 2] (hB : B.IsAlt) {w u : V} (hwu : B w u = 0) (v : V) :
    ((shearIsometry hB hwu : isometryGroup B) : V ≃ₗ[K] V) v = v + B v u • w + B v w • u :=
  rfl

end Abstract

section Standard

variable {r : ℕ} {K : Type} [Field K]

variable (W L : Submodule K (Fin r ⊕ Fin r → K))

@[expose] def flagKernel : Subgroup (StatedSp r K) where
  carrier := {g | (∀ w ∈ W, spMat g *ᵥ w = w) ∧ (∀ l ∈ L, spMat g *ᵥ l - l ∈ W) ∧
    ∀ v, spMat g *ᵥ v - v ∈ L}
  one_mem' := ⟨fun w _ => one_mulVec w, fun l _ => by
      rw [show spMat (1 : StatedSp r K) *ᵥ l = l from one_mulVec l, sub_self]
      exact W.zero_mem, fun v => by
      rw [show spMat (1 : StatedSp r K) *ᵥ v = v from one_mulVec v, sub_self]
      exact L.zero_mem⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2, hg3⟩ ⟨hh1, hh2, hh3⟩
    refine ⟨fun w hw => by rw [spMat_mul_mulVec, hh1 w hw, hg1 w hw], fun l hl => ?_, fun v => ?_⟩
    · have hhl : spMat h *ᵥ l ∈ L := by
        have h1 := add_mem (hh3 l) hl
        rwa [sub_add_cancel] at h1
      have h1 := add_mem (hg2 _ hhl) (hh2 l hl)
      rwa [sub_add_sub_cancel, ← spMat_mul_mulVec] at h1
    · have h1 := add_mem (hg3 (spMat h *ᵥ v)) (hh3 v)
      rwa [sub_add_sub_cancel, ← spMat_mul_mulVec] at h1
  inv_mem' := by
    rintro g ⟨hg1, hg2, hg3⟩
    have h3 : ∀ v, spMat g⁻¹ *ᵥ v - v ∈ L := fun v => by
      have h1 := neg_mem (hg3 (spMat g⁻¹ *ᵥ v))
      rwa [spMat_mulVec_inv_mulVec, neg_sub] at h1
    refine ⟨fun w hw => ?_, fun l hl => ?_, h3⟩
    · conv_lhs => rw [← hg1 w hw]
      exact spMat_inv_mulVec_mulVec g w
    · have hl' : spMat g⁻¹ *ᵥ l ∈ L := by
        have h1 := add_mem (h3 l) hl
        rwa [sub_add_cancel] at h1
      have h1 := neg_mem (hg2 _ hl')
      rwa [spMat_mulVec_inv_mulVec, neg_sub] at h1

variable {W L}

theorem mem_flagKernel {g : StatedSp r K} :
    g ∈ flagKernel W L ↔ (∀ w ∈ W, spMat g *ᵥ w = w) ∧ (∀ l ∈ L, spMat g *ᵥ l - l ∈ W) ∧
      ∀ v, spMat g *ᵥ v - v ∈ L :=
  Iff.rfl

theorem pow_four_eq_one_of_mem_flagKernel [CharP K 2] {g : StatedSp r K}
    (hg : g ∈ flagKernel W L) : g ^ 4 = 1 := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  have h2 : ∀ x : Fin r ⊕ Fin r → K, x + x = 0 := fun x => by
    rw [← two_smul K x, CharTwo.two_eq_zero, zero_smul]
  refine statedSp_ext fun v => ?_
  set a := spMat g *ᵥ v - v with ha
  set b := spMat g *ᵥ a - a with hb
  have hAv : spMat g *ᵥ v = v + a := by rw [ha]; abel
  have hAa : spMat g *ᵥ a = a + b := by rw [hb]; abel
  have hAb : spMat g *ᵥ b = b := hg1 b (hg2 a (hg3 v))
  have hpow : g ^ 4 = g * (g * (g * g)) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have e2 : spMat g *ᵥ (spMat g *ᵥ v) = v + b := by
    rw [hAv, mulVec_add, hAv, hAa, show v + a + (a + b) = v + b + (a + a) by abel, h2, add_zero]
  have e3 : spMat g *ᵥ (spMat g *ᵥ (spMat g *ᵥ v)) = v + a + b := by
    rw [e2, mulVec_add, hAv, hAb]
  have e4 : spMat g *ᵥ (spMat g *ᵥ (spMat g *ᵥ (spMat g *ᵥ v))) = v := by
    rw [e3, mulVec_add, mulVec_add, hAv, hAa, hAb,
      show v + a + (a + b) + b = v + (a + a) + (b + b) by abel, h2, h2, add_zero, add_zero]
  rw [hpow, spMat_mul_mulVec, spMat_mul_mulVec, spMat_mul_mulVec, e4]
  exact (one_mulVec v).symm

theorem isPGroup_flagKernel [CharP K 2] : IsPGroup 2 (flagKernel W L) := fun g =>
  ⟨2, Subtype.ext (by
    rw [Subgroup.coe_pow, show 2 ^ 2 = 4 by norm_num, pow_four_eq_one_of_mem_flagKernel g.2]
    rfl)⟩

theorem spMat_symm_mulVec (h : isometryGroup (pairedSympForm K r)) (v : Fin r ⊕ Fin r → K) :
    spMat (statedSpIsometryEquiv.symm h) *ᵥ v = (h : (Fin r ⊕ Fin r → K) ≃ₗ[K] _) v := by
  change matrixLinIso (matrixLinIso.symm h.val) v = h.val v
  rw [MulEquiv.apply_symm_apply]

theorem pairedSympForm_semilinearCoordMap (g : StatedSp r K) (φ : K ≃+* K)
    (x y : Fin r ⊕ Fin r → K) :
    pairedSympForm K r (semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ x)
        (semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ y) = φ (pairedSympForm K r x y) := by
  rw [semilinearCoordMap_form _ φ 1 (by
    rw [Units.val_one, one_smul]
    exact SymplecticTorusWeyl.mem_statedSp_iff.mp g.2), Units.val_one, one_mul]

theorem semilinearCoordMap_mulVec_of_mul_eq {g s : StatedSp r K} {φ : K ≃+* K}
    (h : g * fieldSp r K φ s = s * g) (v : Fin r ⊕ Fin r → K) :
    semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ (spMat s *ᵥ v) =
      spMat s *ᵥ semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ v := by
  rw [semilinearCoordMap_apply, semilinearCoordMap_apply, coord_mulVec, mulVec_mulVec,
    mulVec_mulVec]
  have h1 := congrArg spMat h
  rw [show spMat (g * fieldSp r K φ s) = spMat g * (spMat s).map φ from rfl,
    show spMat (s * g) = spMat s * spMat g from rfl] at h1
  rw [h1]

theorem spMat_conj_mulVec (g s : StatedSp r K) (φ : K ≃+* K) (v : Fin r ⊕ Fin r → K) :
    spMat (g * fieldSp r K φ s * g⁻¹) *ᵥ v =
      semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ
        (spMat s *ᵥ (semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ).symm v) := by
  rw [semilinearCoordMap_apply, coord_mulVec, semilinearCoordMap_symm_apply]
  have hσ : (fun i => φ (φ.symm ((matrixLinIso (g : GL (Fin r ⊕ Fin r) K)).symm v i))) =
      (matrixLinIso (g : GL (Fin r ⊕ Fin r) K)).symm v :=
    funext fun i => φ.apply_symm_apply _
  rw [hσ, matrixLinIso_symm_apply, mulVec_mulVec, mulVec_mulVec]
  rfl

theorem transvection_mem_flagKernel {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : IsTotallyIsotropic (pairedSympForm K r) W) {w : Fin r ⊕ Fin r → K} (hw : w ∈ W) :
    statedSpIsometryEquiv.symm (EvenCatalog.binaryTransvection pairedSympForm_isAlt w) ∈
      flagKernel W ((pairedSympForm K r).orthogonal W) := by
  have hWL : ∀ x ∈ W, x ∈ (pairedSympForm K r).orthogonal W := fun x hx =>
    LinearMap.BilinForm.mem_orthogonal_iff.mpr fun n hn => hW n hn x hx
  refine ⟨fun w' hw' => ?_, fun l _ => ?_, fun v => ?_⟩
  · rw [spMat_symm_mulVec, EvenCatalog.binaryTransvection_apply, hW w' hw' w hw, zero_smul,
      add_zero]
  · rw [spMat_symm_mulVec, EvenCatalog.binaryTransvection_apply, add_sub_cancel_left]
    exact W.smul_mem _ hw
  · rw [spMat_symm_mulVec, EvenCatalog.binaryTransvection_apply, add_sub_cancel_left]
    exact hWL _ (W.smul_mem _ hw)

variable [CharP K 2]

theorem shear_mem_flagKernel {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : IsTotallyIsotropic (pairedSympForm K r) W) {w u : Fin r ⊕ Fin r → K} (hw : w ∈ W)
    (hu : u ∈ (pairedSympForm K r).orthogonal W) :
    statedSpIsometryEquiv.symm (shearIsometry pairedSympForm_isAlt
        (LinearMap.BilinForm.mem_orthogonal_iff.mp hu w hw)) ∈
      flagKernel W ((pairedSympForm K r).orthogonal W) := by
  have hWL : ∀ x ∈ W, x ∈ (pairedSympForm K r).orthogonal W := fun x hx =>
    LinearMap.BilinForm.mem_orthogonal_iff.mpr fun n hn => hW n hn x hx
  have hBalt := (pairedSympForm_isAlt : (pairedSympForm K r).IsAlt)
  refine ⟨fun w' hw' => ?_, fun l hl => ?_, fun v => ?_⟩
  · rw [spMat_symm_mulVec, shearIsometry_apply,
      LinearMap.BilinForm.mem_orthogonal_iff.mp hu w' hw', hW w' hw' w hw, zero_smul, zero_smul,
      add_zero, add_zero]
  · have hlw : pairedSympForm K r l w = 0 := by
      rw [← hBalt.neg_eq w l, LinearMap.BilinForm.mem_orthogonal_iff.mp hl w hw, neg_zero]
    rw [spMat_symm_mulVec, shearIsometry_apply, hlw, zero_smul, add_zero, add_sub_cancel_left]
    exact W.smul_mem _ hw
  · rw [spMat_symm_mulVec, shearIsometry_apply, add_assoc, add_sub_cancel_left]
    exact add_mem (hWL _ (W.smul_mem _ hw)) (Submodule.smul_mem _ _ hu)

theorem eq_one_and_mem_flagKernel_of_commute [NeZero r] {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW0 : W ≠ ⊥) (hW : IsTotallyIsotropic (pairedSympForm K r) W) {g : StatedSp r K}
    {φ : K ≃+* K}
    (hcomm : ∀ s ∈ flagKernel W ((pairedSympForm K r).orthogonal W),
      g * fieldSp r K φ s = s * g) :
    φ = 1 ∧ g ∈ flagKernel W ((pairedSympForm K r).orthogonal W) := by
  set T := semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ with hTdef
  have hBn : ∀ a : Fin r ⊕ Fin r → K, (∀ x, pairedSympForm K r x a = 0) → a = 0 :=
    fun a h => SymplecticFlag.pairedSympForm_nondegenerate.2 a h
  obtain ⟨hφ, hTW, hTL, hTV⟩ := semilinear_flag_rigidity hBn hW0
    (fun v => LinearMap.BilinForm.mem_orthogonal_iff) T (semilinearCoordMap_smul _ φ)
    (pairedSympForm_semilinearCoordMap g φ)
    (fun w hw v => by
      have h1 := semilinearCoordMap_mulVec_of_mul_eq (hcomm _ (transvection_mem_flagKernel hW hw))
        v
      rw [spMat_symm_mulVec, spMat_symm_mulVec, EvenCatalog.binaryTransvection_apply,
        EvenCatalog.binaryTransvection_apply] at h1
      exact h1)
    (fun w hw u hu v => by
      have h1 := semilinearCoordMap_mulVec_of_mul_eq
        (hcomm _ (shear_mem_flagKernel hW hw hu)) v
      rw [spMat_symm_mulVec, spMat_symm_mulVec, shearIsometry_apply, shearIsometry_apply] at h1
      exact h1)
  have hφ1 : φ = 1 := RingEquiv.ext hφ
  subst hφ1
  have hTg : ∀ v, T v = spMat g *ᵥ v := fun v => by
    rw [hTdef, semilinearCoordMap_apply]
    rfl
  refine ⟨rfl, fun w hw => ?_, fun l hl => ?_, fun v => ?_⟩
  · rw [← hTg]
    exact hTW w hw
  · rw [← hTg]
    exact hTL l hl
  · rw [← hTg]
    exact hTV v

end Standard

end SpChain

open SpChain

theorem even_symplectic_isotropic_radical_centralizer {r f : ℕ} (hr : 1 ≤ r) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (W : Submodule K (Fin r ⊕ Fin r → K))
    (hW0 : W ≠ ⊥) (hW : IsTotallyIsotropic (pairedSympForm K r) W) :
    Finite (flagKernel W ((pairedSympForm K r).orthogonal W)) ∧
    IsPGroup 2 (flagKernel W ((pairedSympForm K r).orthogonal W)) ∧
    (∀ (g : StatedSp r K) (φ : K ≃+* K),
      (∀ w ∈ W, ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        (fun i => φ (w i)) ∈ W) →
      spInner r K g * fieldAut r K φ ∈ Subgroup.normalizer
        (((flagKernel W ((pairedSympForm K r).orthogonal W)).map (spInner r K) :
          Subgroup (MulAut (StatedProj (StatedSp r K)))) : Set _)) ∧
    spSemilinearAutGroup r K ⊓ Subgroup.centralizer
        (((flagKernel W ((pairedSympForm K r).orthogonal W)).map (spInner r K) :
          Subgroup (MulAut (StatedProj (StatedSp r K)))) : Set _) =
      (Subgroup.center (flagKernel W ((pairedSympForm K r).orthogonal W))).map
        ((spInner r K).comp (flagKernel W ((pairedSympForm K r).orthogonal W)).subtype) ∧
    IsPGroup 2 ↥(spSemilinearAutGroup r K ⊓ Subgroup.centralizer
        (((flagKernel W ((pairedSympForm K r).orthogonal W)).map (spInner r K) :
          Subgroup (MulAut (StatedProj (StatedSp r K)))) : Set _)) := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : NeZero r := ⟨by omega⟩
  set B := pairedSympForm K r with hBdef
  set L := B.orthogonal W with hLdef
  set R := flagKernel W L with hRdef
  have hBn : ∀ a : Fin r ⊕ Fin r → K, (∀ x, B x a = 0) → a = 0 :=
    fun a h => SymplecticFlag.pairedSympForm_nondegenerate.2 a h
  have hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, B w v = 0 := fun v => LinearMap.BilinForm.mem_orthogonal_iff
  have hιinj := spInner_injective (r := r) (K := K)
  have hconjeq : ∀ (g s : StatedSp r K) (φ : K ≃+* K),
      spInner r K g * fieldAut r K φ * spInner r K s * (spInner r K g * fieldAut r K φ)⁻¹ =
        spInner r K s → g * fieldSp r K φ s = s * g := by
    intro g s φ h
    rw [conj_spInner] at h
    have h1 := hιinj h
    calc g * fieldSp r K φ s = g * fieldSp r K φ s * g⁻¹ * g := by group
      _ = s * g := by rw [h1]
  have hcent : spSemilinearAutGroup r K ⊓ Subgroup.centralizer
      ((R.map (spInner r K) : Subgroup (MulAut (StatedProj (StatedSp r K)))) : Set _) =
      (Subgroup.center R).map ((spInner r K).comp R.subtype) := by
    apply le_antisymm
    · intro α hα
      obtain ⟨hαE, hαC⟩ := Subgroup.mem_inf.mp hα
      obtain ⟨g, φ, rfl⟩ := exists_eq_spInner_mul_fieldAut hαE
      have hcomm : ∀ s ∈ R, g * fieldSp r K φ s = s * g := by
        intro s hs
        refine hconjeq g s φ ?_
        have h1 := Subgroup.mem_centralizer_iff.mp hαC (spInner r K s) ⟨s, hs, rfl⟩
        rw [← h1, mul_inv_cancel_right]
      obtain ⟨rfl, hgR⟩ := eq_one_and_mem_flagKernel_of_commute hW0 hW hcomm
      refine ⟨⟨g, hgR⟩, Subgroup.mem_center_iff.mpr fun s => Subtype.ext ?_, ?_⟩
      · have h1 := hcomm s s.2
        rw [map_one] at h1
        exact h1.symm
      · rw [map_one, mul_one]
        rfl
    · rintro _ ⟨z, hz, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨spInner_mem_spSemilinearAutGroup _,
        Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨s, hs⟩)
      change spInner r K s * spInner r K (z : StatedSp r K) =
        spInner r K (z : StatedSp r K) * spInner r K s
      rw [← map_mul, ← map_mul]
      exact congrArg (spInner r K) h1
  refine ⟨inferInstance, isPGroup_flagKernel, fun g φ hgW => ?_, hcent, ?_⟩
  ·
    set T := semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ with hTdef
    have hTW : ∀ w ∈ W, T w ∈ W := fun w hw => hgW w hw
    have hTWsurj : ∀ w ∈ W, T.symm w ∈ W := by
      intro w hw
      let f : W → W := fun x => ⟨T x, hTW x x.2⟩
      have hfinj : Function.Injective f := fun x y hxy =>
        Subtype.ext (T.injective (congrArg Subtype.val hxy))
      obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hfinj) ⟨w, hw⟩
      have h1 : T x = w := congrArg Subtype.val hx
      rw [← h1, AddEquiv.symm_apply_apply]
      exact x.2
    have hTform := pairedSympForm_semilinearCoordMap g φ
    have hTL : ∀ l ∈ L, T l ∈ L := by
      intro l hl
      rw [hL] at hl ⊢
      intro w hw
      rw [← AddEquiv.apply_symm_apply T w, hTform, hl _ (hTWsurj w hw), map_zero]
    have hTLsurj : ∀ l ∈ L, T.symm l ∈ L := by
      intro l hl
      rw [hL] at hl ⊢
      intro w hw
      have h1 := hTform w (T.symm l)
      rw [AddEquiv.apply_symm_apply, hl _ (hTW w hw)] at h1
      exact (map_eq_zero_iff φ φ.injective).mp h1.symm
    have hconjR : ∀ s ∈ R, g * fieldSp r K φ s * g⁻¹ ∈ R := by
      intro s hs
      obtain ⟨hs1, hs2, hs3⟩ := hs
      refine ⟨fun w hw => ?_, fun l hl => ?_, fun v => ?_⟩
      · rw [spMat_conj_mulVec, hs1 _ (hTWsurj w hw), AddEquiv.apply_symm_apply]
      · rw [spMat_conj_mulVec]
        have h1 := hTW _ (hs2 _ (hTLsurj l hl))
        rwa [map_sub, AddEquiv.apply_symm_apply] at h1
      · rw [spMat_conj_mulVec]
        have h1 := hTL _ (hs3 (T.symm v))
        rwa [map_sub, AddEquiv.apply_symm_apply] at h1
    have : Finite (((R.map (spInner r K) : Subgroup (MulAut (StatedProj (StatedSp r K))))) :
        Set (MulAut (StatedProj (StatedSp r K)))) := inferInstance
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨s, hs, rfl⟩ := hn
    exact ⟨_, hconjR s hs, (conj_spInner g s φ).symm⟩
  ·
    rw [hcent]
    exact (isPGroup_flagKernel (W := W) (L := L)).to_subgroup _ |>.map _
