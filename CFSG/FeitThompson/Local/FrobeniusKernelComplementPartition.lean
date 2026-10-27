module

public import Mathlib.GroupTheory.Complement
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Setoid.Partition
import Mathlib.Tactic.Group

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

variable {A : Type*} [Group A] {U W : Subgroup A}

private theorem mem_conj_inv_smul_iff {u a : A} :
    a ∈ MulAut.conj u⁻¹ • W ↔ u * a * u⁻¹ ∈ W := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp

private theorem exists_ne_one_of_ne_bot (hW : W ≠ ⊥) : ∃ w ∈ W, w ≠ 1 := by
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW
  exact ⟨w, hw, by simpa using hw1⟩

theorem notMem_of_mem_conj_inv_smul (hU : U.Normal) (hdisj : Disjoint U W)
    {u a : A} (ha : a ∈ MulAut.conj u⁻¹ • W) (ha1 : a ≠ 1) : a ∉ U := by
  intro hmem
  have h1 : u * a * u⁻¹ ∈ W := mem_conj_inv_smul_iff.mp ha
  have h2 : u * a * u⁻¹ ∈ U := hU.conj_mem _ hmem u
  exact ha1 (by simpa using Subgroup.disjoint_def.mp hdisj h2 h1)

private theorem eq_one_of_centralizer
    (hC : ∀ w ∈ W, w ≠ 1 → U ⊓ Subgroup.centralizer {w} = ⊥)
    {w u : A} (hw : w ∈ W) (hw1 : w ≠ 1) (hu : u ∈ U) (h : u * w = w * u) : u = 1 := by
  have hmem : u ∈ U ⊓ Subgroup.centralizer ({w} : Set A) :=
    ⟨hu, by simpa [Subgroup.mem_centralizer_iff] using h.symm⟩
  rw [hC w hw hw1] at hmem
  simpa using hmem

private theorem twist_mem (hU : U.Normal) {w v : A} (hv : v ∈ U) :
    v⁻¹ * (w * v * w⁻¹) ∈ U :=
  U.mul_mem (U.inv_mem hv) (hU.conj_mem _ hv w)

private theorem twist_injOn
    (hC : ∀ w ∈ W, w ≠ 1 → U ⊓ Subgroup.centralizer {w} = ⊥)
    {w : A} (hw : w ∈ W) (hw1 : w ≠ 1) {v v' : A} (hv : v ∈ U) (hv' : v' ∈ U)
    (h : v⁻¹ * (w * v * w⁻¹) = v'⁻¹ * (w * v' * w⁻¹)) : v = v' := by
  have hx : v' * v⁻¹ ∈ U := U.mul_mem hv' (U.inv_mem hv)
  have h1 : v' * v⁻¹ = w * (v' * v⁻¹) * w⁻¹ := by
    calc v' * v⁻¹ = v' * (v⁻¹ * (w * v * w⁻¹)) * (w * v⁻¹ * w⁻¹) := by group
      _ = v' * (v'⁻¹ * (w * v' * w⁻¹)) * (w * v⁻¹ * w⁻¹) := by rw [h]
      _ = w * (v' * v⁻¹) * w⁻¹ := by group
  have h2 : v' * v⁻¹ * w = w * (v' * v⁻¹) := by
    rw [← mul_inv_eq_one, show v' * v⁻¹ * w * (w * (v' * v⁻¹))⁻¹
      = v' * v⁻¹ * (w * (v' * v⁻¹) * w⁻¹)⁻¹ from by group, ← h1]
    simp
  exact (mul_inv_eq_one.mp (eq_one_of_centralizer hC hw hw1 hx h2)).symm

private theorem twist_surjOn [Finite A] (hU : U.Normal)
    (hC : ∀ w ∈ W, w ≠ 1 → U ⊓ Subgroup.centralizer {w} = ⊥)
    {w : A} (hw : w ∈ W) (hw1 : w ≠ 1) {u₀ : A} (hu₀ : u₀ ∈ U) :
    ∃ v ∈ U, v⁻¹ * (w * v * w⁻¹) = u₀ := by
  have hinj : Function.Injective
      (fun v : U => (⟨(v : A)⁻¹ * (w * v * w⁻¹), twist_mem hU v.2⟩ : U)) := by
    intro v v' h
    exact Subtype.ext (twist_injOn hC hw hw1 v.2 v'.2 (Subtype.ext_iff.mp h))
  obtain ⟨v, hv⟩ := Finite.injective_iff_surjective.mp hinj ⟨u₀, hu₀⟩
  exact ⟨v, v.2, congrArg Subtype.val hv⟩

private theorem conj_mem_iff_twist_eq (hU : U.Normal) (hdisj : Disjoint U W)
    {u₀ w v : A} (hu₀ : u₀ ∈ U) (hw : w ∈ W) (hv : v ∈ U) :
    v * (u₀ * w) * v⁻¹ ∈ W ↔ v⁻¹ * (w * v * w⁻¹) = u₀ := by
  constructor
  · intro h
    have hcU : v * u₀ * (w * v⁻¹ * w⁻¹) ∈ U :=
      U.mul_mem (U.mul_mem hv hu₀) (hU.conj_mem _ (U.inv_mem hv) w)
    have hcW : v * u₀ * (w * v⁻¹ * w⁻¹) ∈ W := by
      rw [show v * u₀ * (w * v⁻¹ * w⁻¹) = v * (u₀ * w) * v⁻¹ * w⁻¹ from by group]
      exact W.mul_mem h (W.inv_mem hw)
    have key := Subgroup.disjoint_def.mp hdisj hcU hcW
    rw [← mul_inv_eq_one, show v⁻¹ * (w * v * w⁻¹) * u₀⁻¹
      = v⁻¹ * (v * u₀ * (w * v⁻¹ * w⁻¹))⁻¹ * v from by group, key]
    simp
  · intro h
    rw [← h, show v * (v⁻¹ * (w * v * w⁻¹) * w) * v⁻¹ = w from by group]
    exact hw

theorem existsUnique_mem_conj_inv_smul [Finite A] (hU : U.Normal)
    (hUW : Subgroup.IsComplement' U W)
    (hC : ∀ w ∈ W, w ≠ 1 → U ⊓ Subgroup.centralizer {w} = ⊥)
    {a : A} (ha : a ∉ U) :
    ∃! u : A, u ∈ U ∧ a ∈ MulAut.conj u⁻¹ • W := by
  have _inst : U.Normal := hU
  have hdisj := hUW.disjoint
  have hmem : a ∈ (U : Set A) * (W : Set A) := by
    rw [← Subgroup.normal_mul U W, hUW.sup_eq_top]; simp
  obtain ⟨u₀, hu₀, w, hw, rfl⟩ := Set.mem_mul.mp hmem
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact ha (by simpa using hu₀)
  obtain ⟨v, hv, hvt⟩ := twist_surjOn hU hC hw hw1 hu₀
  refine ⟨v, ⟨hv, ?_⟩, ?_⟩
  · rw [mem_conj_inv_smul_iff]
    exact (conj_mem_iff_twist_eq hU hdisj hu₀ hw hv).mpr hvt
  · rintro y ⟨hy, hya⟩
    rw [mem_conj_inv_smul_iff] at hya
    exact twist_injOn hC hw hw1 hy hv
      (by rw [(conj_mem_iff_twist_eq hU hdisj hu₀ hw hy).mp hya, hvt])

theorem isPartition_insert_coe_sdiff_one [Finite A] (hU : U.Normal)
    (hUW : Subgroup.IsComplement' U W) (hW : W ≠ ⊥)
    (hC : ∀ w ∈ W, w ≠ 1 → U ⊓ Subgroup.centralizer {w} = ⊥) :
    Setoid.IsPartition
      (insert (U : Set A)
        {s : Set A | ∃ u ∈ U, s = ((MulAut.conj u⁻¹ • W : Subgroup A) : Set A) \ {1}}) := by
  have hdisj := hUW.disjoint
  constructor
  ·
    rw [Set.mem_insert_iff]
    rintro (h | ⟨u, hu, h⟩)
    · have h1 : (1 : A) ∈ (∅ : Set A) := by rw [h]; exact U.one_mem
      simp at h1
    · obtain ⟨w, hw, hw1⟩ := exists_ne_one_of_ne_bot hW
      have hmem : u⁻¹ * w * u ∈ (∅ : Set A) := by
        rw [h]
        refine ⟨mem_conj_inv_smul_iff.mpr ?_, ?_⟩
        · rw [show u * (u⁻¹ * w * u) * u⁻¹ = w from by group]
          exact hw
        · simp only [Set.mem_singleton_iff]
          intro hc
          exact hw1 (by rw [show w = u * (u⁻¹ * w * u) * u⁻¹ from by group, hc]; group)
      simp at hmem
  ·
    intro a
    by_cases ha : a ∈ U
    · refine ⟨(U : Set A), ⟨Set.mem_insert _ _, ha⟩, ?_⟩
      rintro b ⟨hb, hab⟩
      rw [Set.mem_insert_iff] at hb
      rcases hb with hb | ⟨u, -, rfl⟩
      · exact hb
      · exact absurd ha (notMem_of_mem_conj_inv_smul hU hdisj hab.1 (by simpa using hab.2))
    · obtain ⟨u, ⟨hu, hau⟩, huniq⟩ := existsUnique_mem_conj_inv_smul hU hUW hC ha
      have ha1 : a ≠ 1 := fun h => ha (h ▸ U.one_mem)
      refine ⟨((MulAut.conj u⁻¹ • W : Subgroup A) : Set A) \ {1},
        ⟨Set.mem_insert_of_mem _ ⟨u, hu, rfl⟩, hau, by simpa using ha1⟩, ?_⟩
      rintro b ⟨hb, hab⟩
      rw [Set.mem_insert_iff] at hb
      rcases hb with rfl | ⟨v, hv, rfl⟩
      · exact absurd hab ha
      · rw [huniq v ⟨hv, hab.1⟩]

theorem indicator_add_finsum_indicator_conj_inv_smul [Finite A] (hU : U.Normal)
    (hUW : Subgroup.IsComplement' U W)
    (hC : ∀ w ∈ W, w ≠ 1 → U ⊓ Subgroup.centralizer {w} = ⊥) (a : A) :
    (U : Set A).indicator (1 : A → ℕ) a
      + ∑ᶠ u : U, (((MulAut.conj (u : A)⁻¹ • W : Subgroup A) : Set A) \ {1}).indicator
          (1 : A → ℕ) a = 1 := by
  have hdisj := hUW.disjoint
  by_cases ha : a ∈ U
  · rw [Set.indicator_of_mem ha, finsum_eq_zero_of_forall_eq_zero, Pi.one_apply]
    · rfl
    · intro u
      refine Set.indicator_of_notMem ?_ _
      rintro ⟨hmem, h1⟩
      exact notMem_of_mem_conj_inv_smul hU hdisj hmem (by simpa using h1) ha
  · obtain ⟨u, ⟨hu, hau⟩, huniq⟩ := existsUnique_mem_conj_inv_smul hU hUW hC ha
    have ha1 : a ≠ 1 := fun h => ha (h ▸ U.one_mem)
    have hmem : a ∈ ((MulAut.conj ((⟨u, hu⟩ : U) : A)⁻¹ • W : Subgroup A) : Set A) \ {1} :=
      ⟨hau, by simpa using ha1⟩
    rw [Set.indicator_of_notMem ha, finsum_eq_single _ (⟨u, hu⟩ : U),
      Set.indicator_of_mem hmem]
    · rfl
    · rintro ⟨v, hv⟩ hne
      refine Set.indicator_of_notMem ?_ _
      rintro ⟨hmemv, -⟩
      exact hne (Subtype.ext (huniq v ⟨hv, hmemv⟩))

theorem injOn_conj_inv_smul [Finite A] (hU : U.Normal)
    (hUW : Subgroup.IsComplement' U W) (hW : W ≠ ⊥)
    (hC : ∀ w ∈ W, w ≠ 1 → U ⊓ Subgroup.centralizer {w} = ⊥) :
    Set.InjOn (fun u : A => MulAut.conj u⁻¹ • W) U := by
  intro u hu v hv huv
  have huv' : MulAut.conj u⁻¹ • W = MulAut.conj v⁻¹ • W := huv
  have hdisj := hUW.disjoint
  obtain ⟨w, hw, hw1⟩ := exists_ne_one_of_ne_bot hW
  have hau : u⁻¹ * w * u ∈ MulAut.conj u⁻¹ • W := by
    refine mem_conj_inv_smul_iff.mpr ?_
    rw [show u * (u⁻¹ * w * u) * u⁻¹ = w from by group]
    exact hw
  have ha1 : u⁻¹ * w * u ≠ 1 := by
    intro hc
    exact hw1 (by rw [show w = u * (u⁻¹ * w * u) * u⁻¹ from by group, hc]; group)
  have haU : u⁻¹ * w * u ∉ U := notMem_of_mem_conj_inv_smul hU hdisj hau ha1
  obtain ⟨_, _, huniq⟩ := existsUnique_mem_conj_inv_smul hU hUW hC haU
  exact (huniq u ⟨hu, hau⟩).trans (huniq v ⟨hv, huv' ▸ hau⟩).symm

end CFSG.FeitThompson
