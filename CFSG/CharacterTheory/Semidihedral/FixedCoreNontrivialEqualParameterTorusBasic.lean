module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterProjective
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialParameterSumClauses
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterData

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Semidihedral.UnitaryBranch
  CFSG.Semidihedral.Principal

section Swap

variable {K : Type} [Field K]

theorem inversion_mul_self : inversion K * inversion K = 1 := by
  classical
  ext z
  rcases z with _ | z
  · simp [Equiv.Perm.mul_apply]
  · by_cases hz : z = 0
    · subst hz
      simp [Equiv.Perm.mul_apply]
    · rw [Equiv.Perm.mul_apply, inversion_nonzero K z hz,
        inversion_nonzero K _ (neg_ne_zero.mpr (inv_ne_zero hz))]
      simp

theorem inversion_mul_multiplier_mul_self (μ : Kˣ) :
    inversion K * multiplier K μ * (inversion K * multiplier K μ) = 1 := by
  classical
  ext z
  rcases z with _ | z
  · simp [Equiv.Perm.mul_apply]
  · by_cases hz : z = 0
    · subst hz
      simp [Equiv.Perm.mul_apply]
    · have hμz : (μ : K) * z ≠ 0 := mul_ne_zero μ.ne_zero hz
      have h1 : (μ : K) * -((μ : K) * z)⁻¹ = -z⁻¹ := by
        field_simp
      have hz' : -z⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hz)
      simp only [Equiv.Perm.mul_apply, multiplier_some, Equiv.Perm.one_apply]
      rw [inversion_nonzero K _ hμz, multiplier_some, h1, inversion_nonzero K _ hz']
      simp

theorem mul_self_eq_one_of_swap {x y : Omega K} (hxy : x ≠ y) {n : Equiv.Perm (Omega K)}
    (hnD : n ∈ coordinateD K) (hnx : n x = y) (hny : n y = x) : n * n = 1 := by
  obtain ⟨g, hg, hgx, hgy⟩ := exists_coordinateG_infinity_zero (F := K) hxy
  have hgD : g ∈ coordinateD K := coordinateG_le_D K hg
  have hn'D : g⁻¹ * n * g ∈ coordinateD K :=
    (coordinateD K).mul_mem ((coordinateD K).mul_mem ((coordinateD K).inv_mem hgD) hnD) hgD
  have h1 : (g⁻¹ * n * g) none = some 0 := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgx, hnx, ← hgy, ← Equiv.Perm.mul_apply,
      inv_mul_cancel, Equiv.Perm.one_apply]
  have h2 : (g⁻¹ * n * g) (some 0) = none := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgy, hny, ← hgx, ← Equiv.Perm.mul_apply,
      inv_mul_cancel, Equiv.Perm.one_apply]
  have hm : inversion K * (g⁻¹ * n * g) ∈ coordinateD K :=
    (coordinateD K).mul_mem (inversion_mem_coordinateD (F := K)) hn'D
  have hm1 : (inversion K * (g⁻¹ * n * g)) none = none := by
    rw [Equiv.Perm.mul_apply, h1, inversion_zero]
  have hm2 : (inversion K * (g⁻¹ * n * g)) (some 0) = some 0 := by
    rw [Equiv.Perm.mul_apply, h2, inversion_none]
  obtain ⟨μ, hμ⟩ := eq_multiplier_of_fixes_infty_zero hm hm1 hm2
  have hn' : g⁻¹ * n * g = inversion K * multiplier K μ := by
    calc g⁻¹ * n * g = inversion K * inversion K * (g⁻¹ * n * g) := by
          rw [inversion_mul_self, one_mul]
      _ = inversion K * multiplier K μ := by rw [mul_assoc, hμ]
  have hsq : g⁻¹ * n * g * (g⁻¹ * n * g) = 1 := by
    rw [hn']
    exact inversion_mul_multiplier_mul_self μ
  calc n * n = g * (g⁻¹ * n * g * (g⁻¹ * n * g)) * g⁻¹ := by group
    _ = 1 := by rw [hsq]; group

end Swap

@[expose] noncomputable def torusPsiD {G : Type} [Group G] {t s₀ : G} {F' : Type} [Field F']
    [Finite F']
    (φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F') :
    torusH G t s₀ →* Equiv.Perm (Omega F') :=
  (coordinateD F').subtype.comp ((pglEquivCoordinateD F').toMonoidHom.comp (torusPsi φ))

namespace EqualParameterData

variable {G : Type} [Group G] [Finite G] {t s₀ d d₁ : G} {J : Subgroup G} {p f : ℕ}
  {F : Type} [Field F] [Finite F] {κ : C t →* Equiv.Perm (Omega F)}
  {F' : Type} [Field F'] [Finite F']
  {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}
  (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ)
include h

theorem W_cyclic' : IsCyclic (torusW G t s₀) := by
  obtain ⟨h1, -⟩ := h.clauses
  exact h1

theorem card_W_int' : (Nat.card (torusW G t s₀) : ℤ) =
    ((p ^ f : ℕ) + (if p ^ f % 4 = 1 then 1 else -1) : ℤ) / 2 := by
  obtain ⟨-, h2, -⟩ := h.clauses
  exact h2

theorem B_le_K' : (N t).map (C t).subtype ≤ torusK G t s₀ := by
  obtain ⟨-, -, -, -, h5, -⟩ := h.clauses
  exact h5

theorem relIndex_K_H' : (torusK G t s₀).relIndex (torusH G t s₀) = 2 := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := h.clauses
  exact h6

theorem inv_of_not_mem_K' :
    ∀ x ∈ torusH G t s₀, x ∉ torusK G t s₀ → ∀ w ∈ torusW G t s₀, x * w * x⁻¹ = w⁻¹ := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := h.clauses
  exact h7

theorem oddCore_H' :
    (CFSG.pPrimeCore 2 (torusH G t s₀)).map (torusH G t s₀).subtype = torusW G t s₀ := by
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := h.clauses
  exact h8

theorem d_orderOf : orderOf d = 4 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h14, -⟩ := h.clauses
  exact h14

theorem d_sq : d ^ 2 = t := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h15, -⟩ := h.clauses
  exact h15

theorem d_inv_W : ∀ w ∈ torusW G t s₀, d * w * d⁻¹ = w⁻¹ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h17, -⟩ := h.clauses
  exact h17

theorem d_comm_B : ∀ x ∈ (N t).map (C t).subtype, d * x = x * d := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h18, -⟩ := h.clauses
  exact h18

theorem image_K' :
    (((torusK G t s₀).subgroupOf (torusH G t s₀)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 2 (torusH G t s₀)))).map φ.toMonoidHom =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F')).range := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h22, -⟩ := h.clauses
  exact h22

theorem card_B_int' : 4 * (Nat.card ((N t).map (C t).subtype) : ℤ) =
    Nat.card F' - (if Nat.card F' % 4 = 1 then 1 else -1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h23, -⟩ :=
    h.clauses
  exact h23

theorem W_le_K' : torusW G t s₀ ≤ torusK G t s₀ := by
  have := h.W_cyclic'
  intro w hw
  rw [torusK, Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val
    ((IsCyclic.commGroup (α := torusW G t s₀)).mul_comm ⟨y, hy⟩ ⟨w, hw⟩)

theorem W_le_H' : torusW G t s₀ ≤ torusH G t s₀ := h.W_le_K'.trans CaseIData.K_le_H

theorem B_le_H' : (N t).map (C t).subtype ≤ torusH G t s₀ := h.B_le_K'.trans CaseIData.K_le_H

theorem q_odd' : Odd (p ^ f) := h.odd.pow

theorem W_inf_B : torusW G t s₀ ⊓ (N t).map (C t).subtype = ⊥ := by
  have hL := h.localData
  rw [eq_bot_iff]
  intro x ⟨hxW, hxB⟩
  have hxJ : x ∈ J := hL.W_le_J hxW
  have : x ∈ J ⊓ (N t).map (C t).subtype := ⟨hxJ, hxB⟩
  rwa [hL.JB_disj] at this

theorem d_mem_H : d ∈ torusH G t s₀ := by
  apply mem_normalizer_of_conj_mem
  intro w hw
  rw [h.d_inv_W w hw]
  exact (torusW G t s₀).inv_mem hw

theorem t_mem_K : t ∈ torusK G t s₀ := by
  have hL := h.localData
  rw [torusK, Subgroup.mem_centralizer_iff]
  intro w hw
  exact (hL.t_comm_W w hw).symm

omit [Finite G] h in
theorem torusPsiD_apply (x : torusH G t s₀) :
    torusPsiD φ x = ((pglEquivCoordinateD F' (torusPsi φ x) : coordinateD F') :
      Equiv.Perm (Omega F')) := rfl

omit [Finite G] h in
theorem torusPsiD_mem_coordinateD (x : torusH G t s₀) : torusPsiD φ x ∈ coordinateD F' :=
  (pglEquivCoordinateD F' (torusPsi φ x)).2

theorem torusPsiD_eq_one_iff (x : torusH G t s₀) :
    torusPsiD φ x = 1 ↔ (x : G) ∈ torusW G t s₀ := by
  have h1 : torusPsiD φ x = 1 ↔ torusPsi φ x = 1 := by
    rw [torusPsiD_apply]
    constructor
    · intro hx
      have : pglEquivCoordinateD F' (torusPsi φ x) = 1 := Subtype.ext hx
      exact (map_eq_one_iff _ (pglEquivCoordinateD F').injective).mp this
    · intro hx
      rw [hx, map_one]
      rfl
  rw [h1, CaseIData.torusPsi_apply, map_eq_one_iff _ φ.injective, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, ← h.oddCore_H']
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.ext hyx]

omit [Finite G] h in
theorem exists_torusPsiD_eq {y : Equiv.Perm (Omega F')} (hy : y ∈ coordinateD F') :
    ∃ x : torusH G t s₀, torusPsiD φ x = y := by
  obtain ⟨z, hz⟩ := (pglEquivCoordinateD F').surjective ⟨y, hy⟩
  obtain ⟨w, rfl⟩ := φ.surjective z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ w
  refine ⟨x, ?_⟩
  rw [torusPsiD_apply, CaseIData.torusPsi_apply, hz]

theorem torusPsiD_mem_coordinateG_iff (x : torusH G t s₀) :
    torusPsiD φ x ∈ coordinateG F' ↔ (x : G) ∈ torusK G t s₀ := by
  have hR := pglPSLRange_map_coordinateD F'
  have h1 : torusPsiD φ x ∈ coordinateG F' ↔
      torusPsi φ x ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F')).range := by
    rw [torusPsiD_apply]
    constructor
    · intro hx
      have hmem : pglEquivCoordinateD F' (torusPsi φ x) ∈
          (coordinateG F').subgroupOf (coordinateD F') := Subgroup.mem_subgroupOf.mpr hx
      rw [← hR] at hmem
      obtain ⟨z, hz, hzx⟩ := hmem
      have : z = torusPsi φ x := (pglEquivCoordinateD F').injective hzx
      exact this ▸ hz
    · intro hx
      have hmem : pglEquivCoordinateD F' (torusPsi φ x) ∈
          (coordinateG F').subgroupOf (coordinateD F') := by
        rw [← hR]
        exact ⟨_, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hmem
  rw [h1, ← h.image_K']
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, hkx⟩
    have hkx' : torusPsi φ k = torusPsi φ x := hkx
    have h2 : torusPsiD φ (k⁻¹ * x) = 1 := by
      rw [torusPsiD_apply, map_mul, map_inv, hkx', inv_mul_cancel, map_one]
      rfl
    rw [h.torusPsiD_eq_one_iff] at h2
    have h3 : (x : G) = k * (k⁻¹ * x : torusH G t s₀) := by simp
    rw [h3]
    exact (torusK G t s₀).mul_mem (Subgroup.mem_subgroupOf.mp hk) (h.W_le_K' h2)
  · intro hx
    exact ⟨_, ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩, rfl⟩

theorem mul_inv_mem_W_of_torusPsiD_eq {x y : torusH G t s₀}
    (hxy : torusPsiD φ x = torusPsiD φ y) : ((x * y⁻¹ : torusH G t s₀) : G) ∈ torusW G t s₀ := by
  rw [← h.torusPsiD_eq_one_iff, map_mul, map_inv, hxy, mul_inv_cancel]

theorem card_H : Nat.card (torusH G t s₀) =
    Nat.card (torusW G t s₀) * (p ^ f * ((p ^ f) ^ 2 - 1)) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.pPrimeCore 2 (torusH G t s₀))
  rw [Nat.card_congr φ.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula, h.card_F'] at h1
  have h2 : Nat.card (CFSG.pPrimeCore 2 (torusH G t s₀)) = Nat.card (torusW G t s₀) := by
    rw [← h.oddCore_H', Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  rw [h1, h2, mul_comm]

end EqualParameterData

end CFSG.Semidihedral.FixedCoreNontrivial
