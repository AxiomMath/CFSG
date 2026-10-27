module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step37Syl

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.Sporadic.SuzOddCore

namespace Sec3

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G}

theorem exists_mem_sec3B_of_comm
    (hS : Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z y) {τ : G}
    (hτB : τ ∈ normalizer (sec3B A₁ x : Set G)) (hτx : τ * x * τ⁻¹ = x⁻¹) {w : G}
    (hw : w * x = x * w) : ∃ b ∈ sec3B A₁ x, b⁻¹ * w ∈ centralizer (sec3B A₁ x : Set G) := by
  obtain ⟨e₀⟩ := hS.B_suz
  obtain ⟨ψ, hψ, hψk⟩ := exists_suzT_hom hS.B_perf (e₀.trans suzEquivM)
  have hxZ : x ∈ centerIn (sec3B A₁ x) := by
    rw [hS.B_center]
    exact mem_zpowers x
  have hxB : x ∈ sec3B A₁ x := (mem_inf.mp hxZ).1
  have hx3 : orderOf x = 3 := hS.setting.order_x
  have hinner : ∀ n : normalizer (sec3B A₁ x : Set G),
      ((ψ n : ↥suzT) : Equiv.Perm (Fin 1782)) ∈ suzM →
        ∃ b ∈ sec3B A₁ x, b⁻¹ * (n : G) ∈ centralizer (sec3B A₁ x : Set G) := by
    intro n hn
    obtain ⟨q, hq⟩ := (e₀.trans suzEquivM).surjective ⟨_, hn⟩
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨b, b.2, ?_⟩
    have h1 : ψ ⟨b, le_normalizer b.2⟩ = ψ n := by
      apply Subtype.ext
      rw [hψ b b.2]
      exact congrArg Subtype.val hq
    have h2 : ψ ((⟨b, le_normalizer b.2⟩ : normalizer (sec3B A₁ x : Set G))⁻¹ * n) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    exact (hψk _).mp h2
  have hcomm : ∀ {n : G}, (∃ b ∈ sec3B A₁ x, b⁻¹ * n ∈ centralizer (sec3B A₁ x : Set G)) →
      n * x = x * n := by
    rintro n ⟨b, hb, hbn⟩
    have h1 : x * (b⁻¹ * n) = (b⁻¹ * n) * x := mem_centralizer_iff.mp hbn x hxB
    have h2 : b * x = x * b := mem_centralizer_iff.mp (mem_inf.mp hxZ).2 b hb
    calc n * x = b * ((b⁻¹ * n) * x) := by group
      _ = b * (x * (b⁻¹ * n)) := by rw [h1]
      _ = (b * x) * (b⁻¹ * n) := by group
      _ = (x * b) * (b⁻¹ * n) := by rw [h2]
      _ = x * n := by group
  have hxx : ∀ {n : G}, n * x = x * n → n * x * n⁻¹ = x⁻¹ → False := by
    intro n h1 h2
    have h3 : x = x⁻¹ := by rw [← h2, h1, mul_inv_cancel_right]
    have h4 : x ^ 2 = 1 := by
      calc x ^ 2 = x * x⁻¹ := by rw [pow_two, ← h3]
        _ = 1 := mul_inv_cancel x
    have h5 := orderOf_dvd_of_pow_eq_one h4
    rw [hx3] at h5
    exact absurd h5 (by norm_num)
  have hwB : w ∈ normalizer (sec3B A₁ x : Set G) :=
    centralizer_le_normalizer_sec3B A₁ x (mem_centralizer_singleton_iff.mpr hw)
  by_cases hwM : ((ψ ⟨w, hwB⟩ : ↥suzT) : Equiv.Perm (Fin 1782)) ∈ suzM
  · exact hinner _ hwM
  exfalso
  have hτM : ((ψ ⟨τ, hτB⟩ : ↥suzT) : Equiv.Perm (Fin 1782)) ∉ suzM := fun h =>
    hxx (hcomm (hinner _ h)) hτx
  have hidx := suzM_index_T
  have hwτ : ((ψ (⟨w, hwB⟩ * ⟨τ, hτB⟩) : ↥suzT) : Equiv.Perm (Fin 1782)) ∈ suzM := by
    rw [map_mul]
    have h := (mul_mem_iff_of_index_two hidx (a := ψ ⟨w, hwB⟩) (b := ψ ⟨τ, hτB⟩)).mpr
      (by rw [mem_subgroupOf, mem_subgroupOf]; exact iff_of_false hwM hτM)
    exact mem_subgroupOf.mp h
  have h1 := hcomm (hinner _ hwτ)
  refine hxx h1 ?_
  show w * τ * x * (w * τ)⁻¹ = x⁻¹
  calc w * τ * x * (w * τ)⁻¹ = w * (τ * x * τ⁻¹) * w⁻¹ := by group
    _ = w * x⁻¹ * w⁻¹ := by rw [hτx]
    _ = x⁻¹ := by
      rw [show w * x⁻¹ = x⁻¹ * w by
        calc w * x⁻¹ = x⁻¹ * (x * w) * x⁻¹ := by group
          _ = x⁻¹ * (w * x) * x⁻¹ := by rw [hw]
          _ = x⁻¹ * w := by group]
      group

theorem exists_mem_B₀_of_mem_centralizer
    (hS : Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z y) {k : G}
    (hk : k ∈ sec3B A₁ x ⊓ centralizer ({z} : Set G)) :
    ∃ b₀ ∈ B₀, ∃ i : ℤ, k = b₀ * x ^ i := by
  obtain ⟨e₀⟩ := hS.B_suz
  obtain ⟨-, -, π, hπs, hπk, -⟩ := exists_hom_invE hS e₀
  have hcomm : (commutator ↥(sec3B A₁ x ⊓ centralizer ({z} : Set G))).map π = ⊤ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hπs, ← _root_.commutator_def, SuzB0.invE_one_perfect]
  have hmem : π ⟨k, hk⟩ ∈ (commutator ↥(sec3B A₁ x ⊓ centralizer ({z} : Set G))).map π := by
    rw [hcomm]
    exact mem_top _
  obtain ⟨k', hk', hkk'⟩ := hmem
  have hker : π (k'⁻¹ * ⟨k, hk⟩) = 1 := by rw [map_mul, map_inv, hkk', inv_mul_cancel]
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp ((hπk _).mp hker)
  refine ⟨k', ?_, i, ?_⟩
  · rw [hS.B₀_eq, ← Subgroup.map_subtype_commutator]
    exact ⟨k', hk', rfl⟩
  · have h1 : ((k' : G))⁻¹ * k = x ^ i := by
      rw [hi]
      rfl
    calc k = (k' : G) * ((k' : G)⁻¹ * k) := by group
      _ = (k' : G) * x ^ i := by rw [h1]

end Sec3

end CFSG.ComponentClassification.AS81
