module

public import CFSG.LargeExtraspecial.DWCaseIIBBound

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

theorem sub_eq_polar_smul {t : S.O} {c w v : S.Qt}
    (htc : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) c = c) (hw : polar S.q c w = 1)
    (hv : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ ZMod 2 ∙ c) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v = polar S.q v ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) • c := by
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hv
  rw [← hμ]
  congr 1
  have h1 := polar_apply_apply t v w
  have htv : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v + μ • c := by rw [hμ]; abel
  have hcw : polar S.q c ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w) = 1 := by
    rw [← htc, polar_apply_apply, hw]
  rw [htv, polar_add_left, polar_smul_left, hcw, smul_eq_mul, mul_one] at h1
  rw [polar_sub_right, ← h1]
  ring_nf
  rcases zmod2_dichotomy μ with rfl | rfl <;> decide

namespace MaxEA

variable {A : Subgroup G} [IsElementaryAbelian 2 A] (hA : MaxEA S A)
  (hM : S.M ≤ normalizer (A : Set G))
  (hII : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ∈ A)
  (hbad : ∀ g : G, g * S.z * g⁻¹ ∈ A → g * S.z * g⁻¹ ≠ S.z → ¬ A ≤ S.Qa g)
  (hD : spanD S = S.clSub A)
  {g : G} (hxA : g * S.z * g⁻¹ ∈ A) (hxz : g * S.z * g⁻¹ ≠ S.z)
  (hsl : axisA S A g = ZMod 2 ∙ S.cl (g * S.z * g⁻¹))

omit [IsElementaryAbelian 2 A] in
include hA hxA hxz in
theorem z_mem_E : S.z ∈ S.QG ⊓ S.Qa g :=
  ⟨S.z_mem_QG, S.z_mem_Qa_of_mem_QG rfl (hA.le_QG hxA) hxz⟩

omit [Finite G] [IsElementaryAbelian 2 A] in
include hA hxA in
theorem conj_mem_E : g * S.z * g⁻¹ ∈ S.QG ⊓ S.Qa g :=
  ⟨hA.le_QG hxA, by
    rw [Setting.Qa_eq_map]
    exact ⟨S.z, S.z_mem_QG, rfl⟩⟩

include hA hM hII hbad hD hxA hxz in
theorem card_E : Nat.card (S.QG ⊓ S.Qa g : Subgroup G) = 2 ^ (S.width + 1) := by
  have hb := hA.two_mul_card_Lbar_le hM hII hxA hxz hbad
  rw [hD, S.card_submodule, hA.finrank_clSub] at hb
  have hmul := S.card_Lbar_mul g
  rw [S.card_L0 (hA.le_QG hxA) hxz] at hmul
  have hle := S.card_QG_inf_Qa_le hxz
  refine le_antisymm hle ?_
  have h2 : 2 ^ S.width * 2 ^ (S.width + 1) ≤
      2 ^ S.width * Nat.card (S.QG ⊓ S.Qa g : Subgroup G) := by
    calc 2 ^ S.width * 2 ^ (S.width + 1) = 2 * 2 ^ (2 * S.width) := by ring
      _ = 2 * (Nat.card (S.Lbar g) * Nat.card (S.QG ⊓ S.Qa g : Subgroup G)) := by rw [hmul]
      _ = (2 * Nat.card (S.Lbar g)) * Nat.card (S.QG ⊓ S.Qa g : Subgroup G) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hb
  exact Nat.le_of_mul_le_mul_left h2 (by positivity)

include hA hM hII hbad hD hxA hxz in
theorem finrank_clSub_E :
    finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) = S.width := by
  have h := S.card_clPre (S.clSub (S.QG ⊓ S.Qa g))
  rw [S.clPre_clSub inf_le_left (hA.z_mem_E hxA hxz), hA.card_E hM hII hbad hD hxA hxz,
    S.card_submodule, pow_succ, mul_comm] at h
  exact (Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_left two_pos h)).symm

include hA hM hII hsl in
theorem mem_span_of_mem_clSub_E {v : S.Qt} (hvA : v ∈ S.clSub A)
    (hvE : v ∈ S.clSub (S.QG ⊓ S.Qa g)) : v ∈ ZMod 2 ∙ S.cl (g * S.z * g⁻¹) := by
  obtain ⟨e, he, heQ, rfl⟩ := S.mem_clSub_iff.mp hvE
  obtain ⟨a, haA, haQ, hae⟩ := S.mem_clSub_iff.mp hvA
  have heA : e ∈ A := by
    rcases (S.cl_eq_cl_iff haQ heQ).mp hae with h | h
    · rw [h]
      exact haA
    · rw [h]
      exact A.mul_mem haA hA.z_mem
  rw [← hsl]
  exact S.cl_mem_clSub ⟨heA, hA.mem_conjSub_of_mem_Qa' hM hII he.2 heA⟩ heQ

omit [IsElementaryAbelian 2 A] in
include hA hxA in
theorem polar_cl_E {e : G} (he : e ∈ S.QG ⊓ S.Qa g) :
    polar S.q (S.cl (g * S.z * g⁻¹)) (S.cl e) = 0 := by
  rw [S.polar_cl_eq_zero_iff (hA.le_QG hxA) he.1]
  exact (mem_centralizer_singleton_iff.mp ((S.conjBy g).QG_le_M he.2)).symm

include hA hxA in
theorem polar_cl_A {v : S.Qt} (hv : v ∈ S.clSub A) : polar S.q (S.cl (g * S.z * g⁻¹)) v = 0 :=
  polar_clSub (S.cl_mem_clSub hxA (hA.le_QG hxA)) hv

omit [IsElementaryAbelian 2 A] in
include hxz in
theorem polar_E_E {v v' : S.Qt} (hv : v ∈ S.clSub (S.QG ⊓ S.Qa g))
    (hv' : v' ∈ S.clSub (S.QG ⊓ S.Qa g)) : polar S.q v v' = 0 := by
  obtain ⟨e, he, heQ, rfl⟩ := S.mem_clSub_iff.mp hv
  obtain ⟨e', he', he'Q, rfl⟩ := S.mem_clSub_iff.mp hv'
  rw [S.polar_cl_eq_zero_iff heQ he'Q]
  exact S.QG_inf_Qa_comm hxz he he'

include hA hM hII hbad hD hxA hxz hsl in
theorem mem_sup_of_polar {v : S.Qt}
    (hv : polar S.q (S.cl (g * S.z * g⁻¹)) v = 0) :
    v ∈ S.clSub A ⊔ S.clSub (S.QG ⊓ S.Qa g) := by
  have := finiteDimensional_Qt (S := S)
  set c := S.cl (g * S.z * g⁻¹)
  have hc0 : c ≠ 0 := (cl_ne_zero_iff (hA.le_QG hxA)).mpr hxz
  set P := LinearMap.BilinForm.orthogonal S.q.polarBilin (ZMod 2 ∙ c)
  have hmemP : ∀ u, u ∈ P ↔ polar S.q c u = 0 := fun u => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      exact h c (Submodule.mem_span_singleton_self c)
    · intro h y hy
      obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hy
      change polar S.q (μ • c) u = 0
      rw [polar_smul_left, h, smul_zero]
  have hle : S.clSub A ⊔ S.clSub (S.QG ⊓ S.Qa g) ≤ P := by
    refine sup_le (fun v hv => (hmemP v).mpr (hA.polar_cl_A hxA hv)) fun v hv => ?_
    obtain ⟨e, he, -, rfl⟩ := S.mem_clSub_iff.mp hv
    exact (hmemP _).mpr (hA.polar_cl_E hxA he)
  have hP : finrank (ZMod 2) P = 2 * S.width - 1 := by
    have := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate (ZMod 2 ∙ c)
    rw [S.finrank_Qt_eq_two_mul_width, finrank_span_singleton hc0] at this
    exact this
  have hinf : finrank (ZMod 2) (S.clSub A ⊓ S.clSub (S.QG ⊓ S.Qa g) :
      Submodule (ZMod 2) S.Qt) ≤ 1 := by
    have : S.clSub A ⊓ S.clSub (S.QG ⊓ S.Qa g) ≤ ZMod 2 ∙ c := fun u ⟨hu, hu'⟩ =>
      hA.mem_span_of_mem_clSub_E hM hII hsl hu hu'
    exact (Submodule.finrank_mono this).trans (finrank_span_singleton hc0).le
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (S.clSub A) (S.clSub (S.QG ⊓ S.Qa g))
  rw [hA.finrank_clSub, hA.finrank_clSub_E hM hII hbad hD hxA hxz] at hsum
  have heq : S.clSub A ⊔ S.clSub (S.QG ⊓ S.Qa g) = P :=
    Submodule.eq_of_le_of_finrank_le hle (by omega)
  rw [heq]
  exact (hmemP v).mpr hv

include hA hM hII hxA hsl in
theorem Lbar_sub_mem_span_of_mem_A {t : S.O} (ht : t ∈ S.Lbar g) {v : S.Qt}
    (hv : v ∈ S.clSub A) : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ ZMod 2 ∙ S.cl (g * S.z * g⁻¹) := by
  rw [← hsl]
  exact hA.Lbar_sub_mem_axisA hM hII hxA ht hv

omit [IsElementaryAbelian 2 A] in
theorem Lbar_sub_mem_span_of_mem_E {t : S.O} (ht : t ∈ S.Lbar g) {v : S.Qt}
    (hv : v ∈ S.clSub (S.QG ⊓ S.Qa g)) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ ZMod 2 ∙ S.cl (g * S.z * g⁻¹) := by
  obtain ⟨k, hk, rfl⟩ := mem_Lbar.mp ht
  obtain ⟨e, he, heQ, rfl⟩ := S.mem_clSub_iff.mp hv
  rw [ρ_cl_sub hk.2 heQ]
  rcases (S.conjBy g).commutator_eq_one_or_z hk.1 he.2 with h | h
  · rw [h, S.cl_one]
    exact zero_mem _
  · rw [h, Setting.conjBy_z]
    exact Submodule.mem_span_singleton_self _

include hA hM hII hbad hD hxA hxz hsl in
theorem Lbar_sub_mem_span_of_polar {t : S.O} (ht : t ∈ S.Lbar g)
    {v : S.Qt} (hv : polar S.q (S.cl (g * S.z * g⁻¹)) v = 0) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ ZMod 2 ∙ S.cl (g * S.z * g⁻¹) := by
  obtain ⟨a, ha, e, he, rfl⟩ :=
    Submodule.mem_sup.mp (hA.mem_sup_of_polar hM hII hbad hD hxA hxz hsl hv)
  rw [map_add, show (t : S.Qt ≃ₗ[ZMod 2] S.Qt) a + (t : S.Qt ≃ₗ[ZMod 2] S.Qt) e - (a + e) =
    ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) a - a) + ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) e - e) by abel]
  exact add_mem (hA.Lbar_sub_mem_span_of_mem_A hM hII hxA hsl ht ha)
    (Lbar_sub_mem_span_of_mem_E ht he)

end MaxEA

end CFSG.LargeExtraspecial.DW
