module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End4d
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End4e1

public section

open CFSG.Open CFSG.Goldschmidt CFSG.GH74.GLS.Th2.P412 Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

theorem perm_image {X : Type} [Group X] [Finite X] {V : Subgroup X} {W : Fin 4 → Subgroup X}
    (hV : Nat.card V = 2 ^ 8) (hW : ∀ i, W i ≤ V) {M : Subgroup X} [M.Normal] (hVM : V ≤ M)
    (hperm : ∀ g ∈ normalizer (V : Set X), ∀ i, ∃ j, ∀ w ∈ W i, g * w * g⁻¹ ∈ W j) :
    ∀ y : Mbar M, (∀ x ∈ (V.subgroupOf M).map (mbarMk M), y * x * y⁻¹ ∈
        (V.subgroupOf M).map (mbarMk M)) →
      ∀ i, ∃ j, ∀ w ∈ ((W i).subgroupOf M).map (mbarMk M),
        y * w * y⁻¹ ∈ ((W j).subgroupOf M).map (mbarMk M) := by
  classical
  intro y hy i
  obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk'_surjective (goldschmidtOddCore ↥M) y
  have hy₀' : mbarMk M y₀ = y := hy₀
  have hVpg : IsPGroup 2 V := IsPGroup.of_card hV
  have hodd : Odd (Nat.card (mbarKer M)) := odd_card_mbarKer M
  have hy0 : ∀ v ∈ V, (y₀ : X) * v * (y₀ : X)⁻¹ ∈ V ⊔ mbarKer M := by
    intro v hv
    let v' : ↥M := ⟨v, hVM hv⟩
    have hxv : mbarMk M v' ∈ (V.subgroupOf M).map (mbarMk M) :=
      Subgroup.mem_map.2 ⟨v', Subgroup.mem_subgroupOf.2 hv, rfl⟩
    have hconj := hy (mbarMk M v') hxv
    rw [← hy₀'] at hconj
    have hconj' : mbarMk M (y₀ * v' * y₀⁻¹) ∈ (V.subgroupOf M).map (mbarMk M) := by
      simpa only [map_mul, map_inv] using hconj
    obtain ⟨v₂, hv₂mem, hv₂eq⟩ := Subgroup.mem_map.1 hconj'
    have hv₂V : (v₂ : X) ∈ V := Subgroup.mem_subgroupOf.1 hv₂mem
    let k : ↥M := v₂⁻¹ * (y₀ * v' * y₀⁻¹)
    have hk1 : mbarMk M k = 1 := by
      simp only [k, map_mul, map_inv, hv₂eq]
      exact inv_mul_cancel _
    have hkk : ((k : ↥M) : X) ∈ mbarKer M := (mem_mbarKer_iff M k).2 hk1
    have hmul : (v₂ : X) * (k : X) = (y₀ : X) * v * (y₀ : X)⁻¹ := by
      have h1 : v₂ * k = (y₀ * v' * y₀⁻¹ : ↥M) := by
        simp only [k]
        group
      calc (v₂ : X) * (k : X) = ((v₂ * k : ↥M) : X) := rfl
        _ = ((y₀ * v' * y₀⁻¹ : ↥M) : X) := by rw [h1]
        _ = (y₀ : X) * v * (y₀ : X)⁻¹ := rfl
    rw [← hmul]
    exact Subgroup.mul_mem_sup hv₂V hkk
  obtain ⟨o, ho, hnorm⟩ := exists_mul_mem_normalizer hVpg hodd hy0
  obtain ⟨o', ho', rfl⟩ := Subgroup.mem_map.1 ho
  have ho1 : mbarMk M o' = 1 := (QuotientGroup.eq_one_iff o').2 ho'
  let n' : ↥M := o'⁻¹ * y₀
  have hn : (n' : X) ∈ normalizer (V : Set X) := by
    show (o' : X)⁻¹ * (y₀ : X) ∈ normalizer (V : Set X)
    simpa using hnorm
  have hπn' : mbarMk M n' = y := by
    show mbarMk M (o'⁻¹ * y₀) = y
    rw [map_mul, map_inv, ho1, inv_one, one_mul, hy₀']
  obtain ⟨j, hj⟩ := hperm (n' : X) hn i
  refine ⟨j, ?_⟩
  intro w hw
  obtain ⟨w₁, hw₁mem, rfl⟩ := Subgroup.mem_map.1 hw
  have hw₁W : ((w₁ : ↥M) : X) ∈ W i := Subgroup.mem_subgroupOf.1 hw₁mem
  refine Subgroup.mem_map.2 ⟨n' * w₁ * n'⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    show ((n' * w₁ * n'⁻¹ : ↥M) : X) ∈ W j
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hj ((w₁ : ↥M) : X) hw₁W
  · simp only [map_mul, map_inv, hπn']

end CFSG.OddStandard.SmallF3.Omega
