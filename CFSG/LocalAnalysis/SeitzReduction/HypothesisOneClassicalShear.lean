module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.SeitzReduction

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : LinearMap.BilinForm K V}

namespace ShearRigidity

theorem exists_apply_eq_one (hBn : ∀ a : V, (∀ x, B x a = 0) → a = 0) {w : V} (hw : w ≠ 0) :
    ∃ x, B x w = 1 := by
  obtain ⟨x, hx⟩ : ∃ x, B x w ≠ 0 := by
    by_contra! h
    exact hw (hBn w h)
  exact ⟨(B x w)⁻¹ • x, by rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hx]⟩

theorem eq_one_of_mul_self_eq_one [CharP K 2] {c : K} (h : c * c = 1) : c = 1 := by
  have h2 : (c - 1) * (c - 1) = 0 := by
    linear_combination h + (1 - c) * (CharTwo.two_eq_zero : (2 : K) = 0)
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h2)

variable (K) in
theorem add_self_eq_zero [CharP K 2] (v : V) : v + v = 0 := by
  rw [← two_smul K v, CharTwo.two_eq_zero, zero_smul]

theorem mem_iff_forall_of_perp [FiniteDimensional K V] (hBn : ∀ a : V, (∀ x, B x a = 0) → a = 0)
    (hB : B.IsAlt) {W L : Submodule K V} (hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, B w v = 0) (v : V) :
    v ∈ W ↔ ∀ l ∈ L, B l v = 0 := by
  have hnd : B.Nondegenerate :=
    (LinearMap.IsRefl.nondegenerate_iff_separatingRight hB.isRefl).2 hBn
  have hLeq : L = B.orthogonal W :=
    Submodule.ext fun x => (hL x).trans LinearMap.BilinForm.mem_orthogonal_iff.symm
  have hWeq : B.orthogonal L = W := by
    rw [hLeq, LinearMap.BilinForm.orthogonal_orthogonal hnd hB.isRefl]
  rw [← hWeq]
  exact LinearMap.BilinForm.mem_orthogonal_iff

theorem exists_pair_or_eq_span {W : Submodule K V} (hW : W ≠ ⊥) :
    (∃ w₁ ∈ W, ∃ w₂ ∈ W, LinearIndependent K ![w₁, w₂]) ∨ ∃ w₀ : V, w₀ ≠ 0 ∧ W = K ∙ w₀ := by
  obtain ⟨w₁, hw₁, hw₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  by_cases h : W ≤ K ∙ w₁
  · exact Or.inr ⟨w₁, hw₁0, le_antisymm h ((Submodule.span_singleton_le_iff_mem _ _).2 hw₁)⟩
  · obtain ⟨w₂, hw₂, hw₂S⟩ := IsConcreteLE.not_le_iff_exists.1 h
    refine Or.inl ⟨w₁, hw₁, w₂, hw₂, (LinearIndependent.pair_iff' hw₁0).2 fun a ha => hw₂S ?_⟩
    rw [← ha]
    exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self w₁)

theorem semilinear_core [CharP K 2] (hB : B.IsAlt) {W₀ L : Submodule K V}
    (hLW : ∃ x ∈ L, ∃ u ∈ L, B x u = 1) (hW₀ : W₀ ≠ ⊥)
    {F : Type*} [FunLike F V V] [AddMonoidHomClass F V V] {φ : K ≃+* K} (T : F)
    (hT : ∀ (a : K) v, T (a • v) = φ a • T v) (hTB : ∀ x y, B (T x) (T y) = φ (B x y))
    (hTL : ∀ v ∈ L, T v ∈ L)
    (hsh : ∀ w ∈ W₀, ∀ u ∈ L, ∃ g : V →+ V, (∀ v, T (g v) = g (T v)) ∧
      ∀ v ∈ L, g v = v + B v u • w) :
    (∀ a, φ a = a) ∧ (∀ w ∈ W₀, T w = w) ∧ ∀ x ∈ L, ∀ u ∈ L, B (T x) u = B x u := by
  obtain ⟨x₀, hx₀, u₀, hu₀, hxu⟩ := hLW
  obtain ⟨w₁, hw₁, hw₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW₀
  have key : ∀ w ∈ W₀, ∀ u ∈ L, ∀ x ∈ L, φ (B x u) • T w = B (T x) u • w := by
    intro w hw u hu x hx
    obtain ⟨g, hgT, hgL⟩ := hsh w hw u hu
    have h1 := hgT x
    rw [hgL x hx, hgL (T x) (hTL x hx), map_add, hT, add_right_inj] at h1
    exact h1
  set c := B (T x₀) u₀ with hc
  have h1 : ∀ w ∈ W₀, T w = c • w := by
    intro w hw
    have h := key w hw u₀ hu₀ x₀ hx₀
    rwa [hxu, map_one, one_smul] at h
  have h3 : ∀ x ∈ L, ∀ u ∈ L, B (T x) u = c * φ (B x u) := by
    intro x hx u hu
    have h := key w₁ hw₁ u hu x hx
    rw [h1 w₁ hw₁, smul_smul] at h
    rw [← smul_left_injective K hw₁0 h, mul_comm]
  have hcc : c * φ c = 1 := by
    have e1 : B x₀ (T u₀) = c := by
      rw [← hB.neg_eq, h3 u₀ hu₀ x₀ hx₀, ← hB.neg_eq, hxu, map_neg, map_one]
      ring
    have e2 := h3 x₀ hx₀ (T u₀) (hTL u₀ hu₀)
    rw [hTB, hxu, map_one, e1] at e2
    exact e2.symm
  have hc0 : c ≠ 0 := left_ne_zero_of_mul_eq_one hcc
  have hφ : ∀ a, φ a = a := by
    intro a
    have h := h1 _ (W₀.smul_mem a hw₁)
    rw [hT, h1 w₁ hw₁, smul_smul, smul_smul] at h
    exact mul_right_cancel₀ hc0 ((smul_left_injective K hw₁0 h).trans (mul_comm c a))
  have hc1 : c = 1 := by
    rw [hφ] at hcc
    exact eq_one_of_mul_self_eq_one hcc
  refine ⟨hφ, fun w hw => by rw [h1 w hw, hc1, one_smul], fun x hx u hu => ?_⟩
  rw [h3 x hx u hu, hc1, one_mul, hφ]

theorem sub_mem_of_fix {W L : Submodule K V} (hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, B w v = 0)
    {F : Type*} [FunLike F V V] [AddMonoidHomClass F V V] (T : F)
    (hTB : ∀ x y, B (T x) (T y) = B x y) (hTW : ∀ w ∈ W, T w = w) (v : V) : T v - v ∈ L := by
  rw [hL]
  intro w hw
  have h := hTB w v
  rw [hTW w hw] at h
  rw [map_sub, h, sub_self]

theorem sub_eq_smul_of_shear {W L : Submodule K V} {F : Type*} [FunLike F V V]
    [AddMonoidHomClass F V V] (T : F) (hTW : ∀ w ∈ W, T w = w) (hTV : ∀ v, T v - v ∈ L)
    {w u x : V} (hx : B x w = 1) {g : V →+ V} (hgT : ∀ v, T (g v) = g (T v))
    (hgL : ∀ v ∈ L, g v = v + B v u • w) (hgW : ∀ v, g v - v - B v w • u ∈ W) :
    T u - u = B (T x - x) u • w := by
  have hz := hTW _ (hgW x)
  rw [hx, one_smul, map_sub, map_sub, hgT,
    show g (T x) = g x + g (T x - x) by rw [← map_add, add_sub_cancel], hgL _ (hTV x)] at hz
  have hTu : T u = g x + (T x - x + B (T x - x) u • w) - T x - (g x - x - u) := by
    rw [← hz]
    abel
  rw [hTu]
  abel

theorem shear_rigidity_of_fix (hBn : ∀ a : V, (∀ x, B x a = 0) → a = 0)
    {W W₀ L : Submodule K V} (hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, B w v = 0)
    (hW2 : ∃ w₁ ∈ W₀, ∃ w₂ ∈ W₀, LinearIndependent K ![w₁, w₂])
    {F : Type*} [FunLike F V V] [AddMonoidHomClass F V V] (T : F)
    (hTB : ∀ x y, B (T x) (T y) = B x y) (hTW : ∀ w ∈ W, T w = w)
    (hsh : ∀ w ∈ W₀, ∀ u ∈ L, ∃ g : V →+ V, (∀ v, T (g v) = g (T v)) ∧
      (∀ v ∈ L, g v = v + B v u • w) ∧ ∀ v, g v - v - B v w • u ∈ W) :
    (∀ v ∈ L, T v = v) ∧ (∀ v, T v - v ∈ L) ∧ ∀ v, ∀ l ∈ L, B l (T v - v) = 0 := by
  have h6 : ∀ v, T v - v ∈ L := sub_mem_of_fix hL T hTB hTW
  obtain ⟨w₁, hw₁, w₂, hw₂, hind⟩ := hW2
  have hw₁0 : w₁ ≠ 0 := by simpa using hind.ne_zero 0
  have hw₂0 : w₂ ≠ 0 := by simpa using hind.ne_zero 1
  have h7 : ∀ u ∈ L, ∀ w ∈ W₀, w ≠ 0 → ∃ a : K, T u - u = a • w := by
    intro u hu w hw hw0
    obtain ⟨x, hx⟩ := exists_apply_eq_one hBn hw0
    obtain ⟨g, hgT, hgL, hgW⟩ := hsh w hw u hu
    exact ⟨_, sub_eq_smul_of_shear T hTW h6 hx hgT hgL hgW⟩
  have hTL : ∀ u ∈ L, T u = u := by
    intro u hu
    obtain ⟨a₁, ha₁⟩ := h7 u hu w₁ hw₁ hw₁0
    obtain ⟨a₂, ha₂⟩ := h7 u hu w₂ hw₂ hw₂0
    have h := LinearIndependent.pair_iff.1 hind a₁ (-a₂)
      (by rw [neg_smul, ← ha₁, ← ha₂, add_neg_cancel])
    rw [← sub_eq_zero, ha₁, h.1, zero_smul]
  refine ⟨hTL, h6, fun v l hl => ?_⟩
  have h := hTB l v
  rw [hTL l hl] at h
  rw [map_sub, h, sub_self]

theorem shear_of_sub_mem (hB : B.IsAlt) {W L : Submodule K V}
    (hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, B w v = 0) {w u u' : V} (hu : u' - u ∈ W) {g : V →+ V}
    (hgL : ∀ v ∈ L, g v = v + B v u • w) (hgW : ∀ v, g v - v - B v w • u ∈ W) :
    (∀ v ∈ L, g v = v + B v u' • w) ∧ ∀ v, g v - v - B v w • u' ∈ W := by
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · have h : B v (u' - u) = 0 := by rw [← hB.neg_eq, (hL v).1 hv _ hu, neg_zero]
    rw [map_sub, sub_eq_zero] at h
    rw [hgL v hv, h]
  · rw [show g v - v - B v w • u' = g v - v - B v w • u - B v w • (u' - u) by
      rw [smul_sub]; abel]
    exact W.sub_mem (hgW v) (W.smul_mem _ hu)

theorem forall_shear_of_le_sup (hB : B.IsAlt) {W W₀ L M : Submodule K V}
    (hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, B w v = 0) (hLM : L ≤ M ⊔ W) {F : Type*} [FunLike F V V]
    {T : F}
    (hsh : ∀ w ∈ W₀, ∀ u ∈ M, ∃ g : V →+ V, (∀ v, T (g v) = g (T v)) ∧
      (∀ v ∈ L, g v = v + B v u • w) ∧ ∀ v, g v - v - B v w • u ∈ W) :
    ∀ w ∈ W₀, ∀ u ∈ L, ∃ g : V →+ V, (∀ v, T (g v) = g (T v)) ∧
      (∀ v ∈ L, g v = v + B v u • w) ∧ ∀ v, g v - v - B v w • u ∈ W := by
  intro w hw u hu
  obtain ⟨m, hm, h, hh, rfl⟩ := Submodule.mem_sup.1 (hLM hu)
  obtain ⟨g, hgT, hgL, hgW⟩ := hsh w hw m hm
  exact ⟨g, hgT, shear_of_sub_mem hB hL (by rwa [add_sub_cancel_left]) hgL hgW⟩

theorem shear_comp_right {W L : Submodule K V} (hWL : W ≤ L)
    (hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, B w v = 0) {w u : V} (hu : u ∈ L) {g z : V →+ V}
    (hgL : ∀ v ∈ L, g v = v + B v u • w) (hgW : ∀ v, g v - v - B v w • u ∈ W)
    (hzL : ∀ v ∈ L, z v = v) (hzW : ∀ v, z v - v ∈ W) :
    (∀ v ∈ L, g (z v) = v + B v u • w) ∧ ∀ v, g (z v) - v - B v w • u ∈ W := by
  have hgy : ∀ y ∈ W, g y = y := fun y hy => by
    rw [hgL y (hWL hy), (hL u).1 hu y hy, zero_smul, add_zero]
  refine ⟨fun v hv => by rw [hzL v hv, hgL v hv], fun v => ?_⟩
  have e : g (z v) = g v + (z v - v) := by
    rw [← hgy _ (hzW v), ← map_add, add_sub_cancel]
  rw [e, show g v + (z v - v) - v - B v w • u = g v - v - B v w • u + (z v - v) by abel]
  exact W.add_mem (hgW v) (hzW v)

theorem shear_comp_left {W L : Submodule K V} (hWL : W ≤ L) {w u : V} (hw : w ∈ W)
    {g z : V →+ V} (hgL : ∀ v ∈ L, g v = v + B v u • w) (hgW : ∀ v, g v - v - B v w • u ∈ W)
    (hzL : ∀ v ∈ L, z v = v) (hzW : ∀ v, z v - v ∈ W) :
    (∀ v ∈ L, z (g v) = v + B v u • w) ∧ ∀ v, z (g v) - v - B v w • u ∈ W := by
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · have hgv : g v ∈ L := by
      rw [hgL v hv]
      exact L.add_mem hv (L.smul_mem _ (hWL hw))
    rw [hzL _ hgv, hgL v hv]
  · rw [show z (g v) - v - B v w • u = (z (g v) - g v) + (g v - v - B v w • u) by abel]
    exact W.add_mem (hzW _) (hgW v)

end ShearRigidity

open ShearRigidity

variable (K) in
theorem apply_apply_eq_of_apply_sub [CharP K 2] {F : Type*} [FunLike F V V]
    [AddMonoidHomClass F V V] {T : F} (h : ∀ v, T (T v - v) = T v - v) : ∀ v, T (T v) = v := by
  intro v
  calc T (T v) = T (T v - v) + T v := by rw [← map_add, sub_add_cancel]
    _ = T v + T v - v := by
        rw [h]
        abel
    _ = v := by
        rw [ShearRigidity.add_self_eq_zero K, zero_sub,
          neg_eq_of_add_eq_zero_left (ShearRigidity.add_self_eq_zero K v)]

theorem apply_apply_eq_of_sub_mem [CharP K 2] {W L : Submodule K V} (hWL : W ≤ L)
    {F : Type*} [FunLike F V V] [AddMonoidHomClass F V V] {T : F}
    (h1 : ∀ v ∈ L, T v = v) (h2 : ∀ v, T v - v ∈ W) : ∀ v, T (T v) = v :=
  apply_apply_eq_of_apply_sub K fun v => h1 _ (hWL (h2 v))

theorem semilinear_shear_rigidity_of_perp [CharP K 2]
    (hBn : ∀ a : V, (∀ x, B x a = 0) → a = 0) (hB : B.IsAlt) {W L : Submodule K V}
    (hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, B w v = 0) (hW : ∀ v, v ∈ W ↔ ∀ l ∈ L, B l v = 0)
    (hLW : ∃ x ∈ L, ∃ u ∈ L, B x u = 1) (hW2 : ∃ w₁ ∈ W, ∃ w₂ ∈ W, LinearIndependent K ![w₁, w₂])
    {F : Type*} [FunLike F V V] [AddMonoidHomClass F V V] {φ : K ≃+* K} (T : F)
    (hT : ∀ (a : K) v, T (a • v) = φ a • T v) (hTB : ∀ x y, B (T x) (T y) = φ (B x y))
    (hTL : ∀ v ∈ L, T v ∈ L)
    (hsh : ∀ w ∈ W, ∀ u ∈ L, ∃ g : V →+ V, (∀ v, T (g v) = g (T v)) ∧
      (∀ v ∈ L, g v = v + B v u • w) ∧ ∀ v, g v - v - B v w • u ∈ W) :
    (∀ a, φ a = a) ∧ (∀ v ∈ L, T v = v) ∧ ∀ v, T v - v ∈ W := by
  obtain ⟨w₁, hw₁, w₂, hw₂, hind⟩ := hW2
  have hW0 : W ≠ ⊥ := (Submodule.ne_bot_iff W).2 ⟨w₁, hw₁, by simpa using hind.ne_zero 0⟩
  obtain ⟨hφ, hTW, -⟩ := semilinear_core hB hLW hW0 T hT hTB hTL
    fun w hw u hu => (hsh w hw u hu).imp fun _ hg => ⟨hg.1, hg.2.1⟩
  have hTB' : ∀ x y, B (T x) (T y) = B x y := fun x y => by rw [hTB, hφ]
  obtain ⟨hTL1, -, hperp⟩ :=
    shear_rigidity_of_fix hBn hL ⟨w₁, hw₁, w₂, hw₂, hind⟩ T hTB' hTW hsh
  exact ⟨hφ, hTL1, fun v => (hW _).2 (hperp v)⟩

theorem semilinear_shear_rigidity [CharP K 2] [FiniteDimensional K V]
    (hBn : ∀ a : V, (∀ x, B x a = 0) → a = 0) (hB : B.IsAlt) {W L : Submodule K V}
    (hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, B w v = 0) (hLW : ∃ x ∈ L, ∃ u ∈ L, B x u = 1)
    (hW2 : ∃ w₁ ∈ W, ∃ w₂ ∈ W, LinearIndependent K ![w₁, w₂])
    {F : Type*} [FunLike F V V] [AddMonoidHomClass F V V] {φ : K ≃+* K} (T : F)
    (hT : ∀ (a : K) v, T (a • v) = φ a • T v) (hTB : ∀ x y, B (T x) (T y) = φ (B x y))
    (hTL : ∀ v ∈ L, T v ∈ L)
    (hsh : ∀ w ∈ W, ∀ u ∈ L, ∃ g : V →+ V, (∀ v, T (g v) = g (T v)) ∧
      (∀ v ∈ L, g v = v + B v u • w) ∧ ∀ v, g v - v - B v w • u ∈ W) :
    (∀ a, φ a = a) ∧ (∀ v ∈ L, T v = v) ∧ ∀ v, T v - v ∈ W :=
  semilinear_shear_rigidity_of_perp hBn hB hL (mem_iff_forall_of_perp hBn hB hL) hLW hW2 T hT
    hTB hTL hsh

theorem semilinear_shear_rigidity_line [CharP K 2]
    (hBn : ∀ a : V, (∀ x, B x a = 0) → a = 0) (hB : B.IsAlt) {W L : Submodule K V}
    (hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, B w v = 0) (hLW : ∃ x ∈ L, ∃ u ∈ L, B x u = 1)
    {w₀ : V} (hw₀ : w₀ ≠ 0) (hW1 : W = K ∙ w₀)
    {F : Type*} [FunLike F V V] [AddMonoidHomClass F V V] {φ : K ≃+* K} (T : F)
    (hT : ∀ (a : K) v, T (a • v) = φ a • T v) (hTB : ∀ x y, B (T x) (T y) = φ (B x y))
    (hTL : ∀ v ∈ L, T v ∈ L)
    (hsh : ∀ w ∈ W, ∀ u ∈ L, ∃ g : V →+ V, (∀ v, T (g v) = g (T v)) ∧
      (∀ v ∈ L, g v = v + B v u • w) ∧ ∀ v, g v - v - B v w • u ∈ W) :
    (∀ a, φ a = a) ∧ ∀ v, T (T v) = v := by
  have hw₀W : w₀ ∈ W := hW1 ▸ Submodule.mem_span_singleton_self w₀
  have hW0 : W ≠ ⊥ := (Submodule.ne_bot_iff W).2 ⟨w₀, hw₀W, hw₀⟩
  obtain ⟨hφ, hTW, -⟩ := semilinear_core hB hLW hW0 T hT hTB hTL
    fun w hw u hu => (hsh w hw u hu).imp fun _ hg => ⟨hg.1, hg.2.1⟩
  have hTB' : ∀ x y, B (T x) (T y) = B x y := fun x y => by rw [hTB, hφ]
  have hTlin : ∀ (a : K) v, T (a • v) = a • T v := fun a v => by rw [hT, hφ]
  have h6 : ∀ v, T v - v ∈ L := sub_mem_of_fix hL T hTB' hTW
  obtain ⟨x₁, hx₁⟩ := exists_apply_eq_one hBn hw₀
  have h7 : ∀ u ∈ L, T u - u = B (T x₁ - x₁) u • w₀ := by
    intro u hu
    obtain ⟨g, hgT, hgL, hgW⟩ := hsh w₀ hw₀W u hu
    exact sub_eq_smul_of_shear T hTW h6 hx₁ hgT hgL hgW
  have hXw : B (T x₁ - x₁) w₀ = 0 := by
    rw [← hB.neg_eq, (hL _).1 (h6 x₁) w₀ hw₀W, neg_zero]
  have hperp : ∀ v, B (T x₁ - x₁) (T v - v) = 0 := by
    intro v
    have hlL : v + B w₀ v • x₁ ∈ L := by
      rw [hL]
      intro w hw
      rw [hW1] at hw
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, map_add, map_smul, smul_eq_mul,
        ← hB.neg_eq x₁ w₀, hx₁]
      ring
    have hTv : T v - v = (T (v + B w₀ v • x₁) - (v + B w₀ v • x₁)) - B w₀ v • (T x₁ - x₁) := by
      rw [map_add, hTlin, smul_sub]
      abel
    rw [hTv, h7 _ hlL, map_sub (B (T x₁ - x₁)), map_smul (B (T x₁ - x₁)),
      map_smul (B (T x₁ - x₁)), hXw, hB.self_eq_zero, smul_zero, smul_zero, sub_zero]
  refine ⟨hφ, apply_apply_eq_of_apply_sub K fun v => ?_⟩
  have h := h7 _ (h6 v)
  rwa [hperp v, zero_smul, sub_eq_zero] at h

theorem semilinear_shear_rigidity_sq [CharP K 2]
    (hBn : ∀ a : V, (∀ x, B x a = 0) → a = 0) (hB : B.IsAlt) {W L : Submodule K V}
    (hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, B w v = 0) (hLW : ∃ x ∈ L, ∃ u ∈ L, B x u = 1) (hW0 : W ≠ ⊥)
    {F : Type*} [FunLike F V V] [AddMonoidHomClass F V V] {φ : K ≃+* K} (T : F)
    (hT : ∀ (a : K) v, T (a • v) = φ a • T v) (hTB : ∀ x y, B (T x) (T y) = φ (B x y))
    (hTL : ∀ v ∈ L, T v ∈ L)
    (hsh : ∀ w ∈ W, ∀ u ∈ L, ∃ g : V →+ V, (∀ v, T (g v) = g (T v)) ∧
      (∀ v ∈ L, g v = v + B v u • w) ∧ ∀ v, g v - v - B v w • u ∈ W) :
    (∀ a, φ a = a) ∧ ∀ v, T (T v) = v := by
  rcases exists_pair_or_eq_span hW0 with hW2 | ⟨w₀, hw₀, hW1⟩
  · obtain ⟨hφ, hTW, -⟩ := semilinear_core hB hLW hW0 T hT hTB hTL
      fun w hw u hu => (hsh w hw u hu).imp fun _ hg => ⟨hg.1, hg.2.1⟩
    have hTB' : ∀ x y, B (T x) (T y) = B x y := fun x y => by rw [hTB, hφ]
    obtain ⟨hTL1, h6, -⟩ := shear_rigidity_of_fix hBn hL hW2 T hTB' hTW hsh
    exact ⟨hφ, apply_apply_eq_of_apply_sub K fun v => hTL1 _ (h6 v)⟩
  · exact semilinear_shear_rigidity_line hBn hB hL hLW hw₀ hW1 T hT hTB hTL hsh

end CFSG.SeitzReduction
