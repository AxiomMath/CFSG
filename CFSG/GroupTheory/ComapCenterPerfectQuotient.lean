module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.SetTheory.Cardinal.Finite

import CFSG.GroupTheory.CardDvdTwo
import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {H K : Type*} [Group H] [Group K]

private theorem comap_center_comm
    (φ : H →* K) (hker : φ.ker ≤ Subgroup.center H)
    (hZ : Nat.card ↥(Subgroup.center K) ∣ 2) :
    ∀ x ∈ (Subgroup.center K).comap φ,
      ∀ c ∈ (Subgroup.center K).comap φ, x * c = c * x := by
  intro x hx c hc
  have hker_center : ∀ z : H, φ z = 1 → z ∈ Subgroup.center H := by
    intro z hz
    exact hker (MonoidHom.mem_ker.mpr hz)
  have hxZ : φ x ∈ Subgroup.center K := Subgroup.mem_comap.mp hx
  have hcZ : φ c ∈ Subgroup.center K := Subgroup.mem_comap.mp hc
  by_cases hx1 : φ x = 1
  · exact (Subgroup.mem_center_iff.mp (hker_center x hx1) c).symm
  by_cases hc1 : φ c = 1
  · exact Subgroup.mem_center_iff.mp (hker_center c hc1) x
  have hsub : (⟨φ x, hxZ⟩ : ↥(Subgroup.center K)) = ⟨φ c, hcZ⟩ :=
    CFSG.GroupTheory.eq_of_ne_one_of_card_dvd_two hZ
      (fun h => hx1 (congrArg Subtype.val h))
      (fun h => hc1 (congrArg Subtype.val h))
  have hxc : φ x = φ c := congrArg Subtype.val hsub
  have hz1 : φ (x⁻¹ * c) = 1 := by rw [map_mul, map_inv, hxc, inv_mul_cancel]
  have hzc : x⁻¹ * c ∈ Subgroup.center H := hker_center _ hz1
  have h2 : c = x⁻¹ * c * x := by
    rw [← Subgroup.mem_center_iff.mp hzc x]; group
  calc x * c = x * (x⁻¹ * c * x) := by
        nth_rewrite 1 [h2]
        rfl
    _ = c * x := by group

private theorem comap_center_decomp
    (φ : H →* K) (hφ : Function.Surjective φ)
    (hperf : commutator (K ⧸ Subgroup.center K) = ⊤)
    (hCker : (Subgroup.center K).comap φ =
      ((QuotientGroup.mk' (Subgroup.center K)).comp φ).ker) :
    ∀ y : H, ∃ z ∈ commutator H, ∃ c ∈ (Subgroup.center K).comap φ, y = z * c := by
  let ψ : H →* (K ⧸ Subgroup.center K) := (QuotientGroup.mk' (Subgroup.center K)).comp φ
  have hψ : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective (Subgroup.center K)).comp hφ
  intro y
  have hy : ψ y ∈ (commutator H).map ψ := by
    rw [show commutator H = ⁅(⊤ : Subgroup H), ⊤⁆ from rfl]
    rw [Subgroup.map_commutator ⊤ ⊤ ψ, Subgroup.map_top_of_surjective ψ hψ]
    change ψ y ∈ commutator (K ⧸ Subgroup.center K)
    rw [hperf]
    exact Subgroup.mem_top (ψ y)
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
  refine ⟨z, hz, z⁻¹ * y, ?_, by group⟩
  rw [hCker, MonoidHom.mem_ker, map_mul, map_inv, hzy]
  exact inv_mul_cancel _

private theorem exists_commutator_hom
    (φ : H →* K) (hker : φ.ker ≤ Subgroup.center H)
    (hCcomm : ∀ x ∈ (Subgroup.center K).comap φ,
      ∀ c ∈ (Subgroup.center K).comap φ, x * c = c * x)
    {x : H} (hx : x ∈ (Subgroup.center K).comap φ) :
    ∃ Φ : H →* ↥(Subgroup.center H), (∀ w : H, (Φ w).val = ⁅x, w⁆) ∧
      Φ x = 1 ∧ commutator H ≤ Φ.ker ∧
      ∀ c ∈ (Subgroup.center K).comap φ, Φ c = 1 := by
  have hxZ : φ x ∈ Subgroup.center K := Subgroup.mem_comap.mp hx
  have hcent : ∀ w : H, ⁅x, w⁆ ∈ Subgroup.center H := by
    intro w
    have hcomm : (φ w) * (φ x) = (φ x) * (φ w) :=
      Subgroup.mem_center_iff.mp hxZ (φ w)
    have h1 : φ ⁅x, w⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm
    exact hker (MonoidHom.mem_ker.mpr h1)
  let Φ : H →* ↥(Subgroup.center H) :=
    { toFun := fun w => ⟨⁅x, w⁆, hcent w⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        ext
        simp only [Subgroup.coe_mul]
        have hb := hcent b
        calc ⁅x, a * b⁆
            = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
              simp only [commutatorElement_def]; group
          _ = ⁅x, a⁆ * ⁅x, b⁆ := by
              rw [Subgroup.mem_center_iff.mp hb a]; group }
  have hΦx : Φ x = 1 := by
    ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr rfl
  have hΦcomm : ∀ a b : H, Φ ⁅a, b⁆ = 1 := by
    intro a b
    rw [map_commutatorElement]
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (Φ a).2 (Φ b).1).symm)
  have hΦbot : commutator H ≤ Φ.ker := by
    rw [show commutator H = ⁅(⊤ : Subgroup H), ⊤⁆ from rfl]
    rw [Subgroup.commutator_def]
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro y ⟨a, _, b, _, h⟩
    rw [← h]
    exact MonoidHom.mem_ker.mpr (hΦcomm a b)
  have hΦ_eq : ∀ w : H, Φ w = ⟨⁅x, w⁆, hcent w⟩ := fun w => rfl
  have hΦ_val : ∀ w : H, (Φ w).val = ⁅x, w⁆ := fun w => by rw [hΦ_eq w]
  refine ⟨Φ, hΦ_val, hΦx, hΦbot, ?_⟩
  intro c hc
  ext
  exact commutatorElement_eq_one_iff_mul_comm.mpr (hCcomm x hx c hc)

theorem comap_center_eq_center_of_card_center_dvd_two
    (φ : H →* K) (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center H)
    (hZ : Nat.card ↥(Subgroup.center K) ∣ 2)
    (hperf : commutator (K ⧸ Subgroup.center K) = ⊤) :
    (Subgroup.center K).comap φ = Subgroup.center H := by
  let ψ : H →* (K ⧸ Subgroup.center K) := (QuotientGroup.mk' (Subgroup.center K)).comp φ
  have hCker : (Subgroup.center K).comap φ = ψ.ker := by
    ext x
    rw [Subgroup.mem_comap, MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff (φ x)).symm
  have hCcomm : ∀ x ∈ (Subgroup.center K).comap φ,
      ∀ c ∈ (Subgroup.center K).comap φ, x * c = c * x :=
    comap_center_comm φ hker hZ
  have hdecomp : ∀ y : H, ∃ z ∈ commutator H, ∃ c ∈ (Subgroup.center K).comap φ,
      y = z * c :=
    comap_center_decomp φ hφ hperf hCker
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨Φ, hΦ_val, hΦx, hΦbot, hΦC⟩ := exists_commutator_hom φ hker hCcomm hx
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, hz, c, hc, rfl⟩ := hdecomp y
    have hΦz : Φ z = 1 := MonoidHom.mem_ker.mp (hΦbot hz)
    have hΦzc : Φ (z * c) = 1 := by rw [map_mul, hΦz, hΦC c hc, one_mul]
    have hval : ⁅x, (z * c : H)⁆ = 1 := by
      rw [← hΦ_val (z * c)]
      simpa only [Subgroup.coe_one] using congrArg Subtype.val hΦzc
    exact (commutatorElement_eq_one_iff_mul_comm.mp hval).symm
  · intro z hz
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]

end CFSG.GroupTheory
