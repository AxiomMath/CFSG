module

import CFSG.ClassicalInvolution.Asc77.AscT8W8Eng
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscT8S26UAction
public import CFSG.ClassicalInvolution.Asc77.AscT8Y1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace T8W

section Lift

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem mem_zpowers_involution {y : G} (hy2 : y * y = 1) {u : G} (hu : u ∈ Subgroup.zpowers y) :
    u = 1 ∨ u = y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  have hsq : y ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hy2
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, hsq, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, hsq, one_zpow, one_mul]

theorem exists_fixed_lift (hΩ : HypOmegaMod p f Ω) {a y : G} (hy : y ∈ T8.cenZ a)
    (hy2 : y * y = 1) (u : T8.LayerQuot Ω a)
    (hu : s26Act (T8.layerJoin Ω a) ⟨y, mem_normalizer_iff_conjSub_eq.mpr
      (T8.layerJoin_conjSub_eq hΩ hy)⟩ u = u) :
    ∃ w : ↥(T8.layerJoin Ω a), y * (w : G) * y⁻¹ = w ∧
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(T8.layerJoin Ω a)) w :
        T8.LayerQuot Ω a) = u := by
  classical
  have hyY : y ∈ Subgroup.normalizer ((T8.layerJoin Ω a : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (T8.layerJoin_conjSub_eq hΩ hy)
  obtain ⟨w₀, rfl⟩ := QuotientGroup.mk_surjective u
  have hyk : y * (w₀ : G) * y⁻¹ ∈ T8.layerJoin Ω a :=
    (Subgroup.mem_normalizer_iff.mp hyY (w₀ : G)).mp w₀.2
  have e := s26Act_mk (T8.layerJoin Ω a) ⟨y, hyY⟩ w₀ ⟨y * (w₀ : G) * y⁻¹, hyk⟩ rfl
  have h1 : ((⟨y * (w₀ : G) * y⁻¹, hyk⟩ : ↥(T8.layerJoin Ω a)) :
      T8.LayerQuot Ω a) = (w₀ : T8.LayerQuot Ω a) := e.symm.trans hu
  have h2 : (⟨y * (w₀ : G) * y⁻¹, hyk⟩ : ↥(T8.layerJoin Ω a))⁻¹ * w₀ ∈
      classicalInvolutionOddCore ↥(T8.layerJoin Ω a) := QuotientGroup.eq.mp h1
  set N : Subgroup G := oddCoreOf (T8.layerJoin Ω a) with hN
  have hx : ∀ b ∈ Subgroup.zpowers y, (w₀ : G)⁻¹ * (b * (w₀ : G) * b⁻¹) ∈ N := by
    intro b hb
    rcases mem_zpowers_involution hy2 hb with hb1 | hb1
    · rw [hb1]
      simp
    · rw [hb1]
      have h3 : (y * (w₀ : G) * y⁻¹)⁻¹ * (w₀ : G) ∈ N := by
        refine mem_oddCoreOf_iff.mpr ⟨(T8.layerJoin Ω a).mul_mem
          ((T8.layerJoin Ω a).inv_mem hyk) w₀.2, ?_⟩
        convert h2 using 1
      have := N.inv_mem h3
      simpa [mul_assoc] using this
  have hAN : ∀ b ∈ Subgroup.zpowers y, ∀ n ∈ N, b * n * b⁻¹ ∈ N := by
    intro b hb n hn
    have hbc : b ∈ T8.cenZ a := (Subgroup.zpowers_le.mpr hy) hb
    have := T8.mem_normalizer_oddCoreOf_layerJoin hΩ hbc
    exact (Subgroup.mem_normalizer_iff.mp this n).mp hn
  have hA2 : IsPGroup 2 ↥(Subgroup.zpowers y) := by
    obtain ⟨m, hm⟩ := T8.exists_orderOf_eq_two_pow hy2
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  obtain ⟨n, hnN, hfix⟩ := Balance.Bootstrap.exists_fixed_mem_coset_of_isPGroup hA2
    (odd_natCard_oddCoreOf _) hAN hx
  have hnY : n ∈ T8.layerJoin Ω a := (mem_oddCoreOf_iff.mp hnN).1
  refine ⟨⟨(w₀ : G) * n, (T8.layerJoin Ω a).mul_mem w₀.2 hnY⟩, ?_, ?_⟩
  · exact hfix y (Subgroup.mem_zpowers y)
  · apply QuotientGroup.eq.mpr
    have hn' := (mem_oddCoreOf_iff.mp hnN).2
    have hE : (⟨(w₀ : G) * n, (T8.layerJoin Ω a).mul_mem w₀.2 hnY⟩ :
        ↥(T8.layerJoin Ω a))⁻¹ * w₀ = (⟨n, hnY⟩ : ↥(T8.layerJoin Ω a))⁻¹ := by
      apply Subtype.ext
      simp
    rw [hE]
    exact (classicalInvolutionOddCore ↥(T8.layerJoin Ω a)).inv_mem hn'

@[expose] def layerImage (Ω : Set (Subgroup G)) (a : G) (H : Subgroup G) :
    Subgroup (T8.LayerQuot Ω a) :=
  (H.subgroupOf (T8.layerJoin Ω a)).map
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(T8.layerJoin Ω a)))

theorem mem_layerImage_of_fixed (hΩ : HypOmegaMod p f Ω) {a y : G} {H : Subgroup G}
    (hy : y ∈ T8.cenZ a) (hy2 : y * y = 1) (hCy : Subgroup.centralizer ({y} : Set G) ≤ H)
    (u : T8.LayerQuot Ω a)
    (hu : s26Act (T8.layerJoin Ω a) ⟨y, mem_normalizer_iff_conjSub_eq.mpr
      (T8.layerJoin_conjSub_eq hΩ hy)⟩ u = u) : u ∈ layerImage Ω a H := by
  exact mem_layerImage_of_fixedE hCy u (exists_fixed_lift hΩ hy hy2 u hu)

theorem layerJoin_le_of_closure {a : G} {H : Subgroup G}
    (hO : oddCoreOf (T8.layerJoin Ω a) ≤ H) (S : Set (T8.LayerQuot Ω a))
    (hS : S ⊆ (layerImage Ω a H : Set (T8.LayerQuot Ω a)))
    (hgen : Subgroup.closure S = ⊤) : T8.layerJoin Ω a ≤ H := by
  exact layerJoin_le_of_closureE hO S hS hgen

end Lift

end T8W

end CFSG.ClassicalInvolution.Asc77
