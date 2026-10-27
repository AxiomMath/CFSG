module

import CFSG.Goldschmidt.Steps.GoldTypeBender
import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingBender
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
public import CFSG.Goldschmidt.Steps.G3aBorel

public section

namespace CFSG.Goldschmidt

open CFSG.Open
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter
  sylowCenter_le)
open CFSG.ComponentClassification.AschbacherStrongEmbedding
  (commuting_involutions_eq_of_cyclic_or_quaternion)

namespace G32Q

theorem fusionStronglyEmbedded_subgroupOf {Y : Type*} [Group Y] [Finite Y] {B M : Subgroup Y}
    (hB : fusionStronglyEmbedded B) (hMB : ¬ M ≤ B) {u : Y} (huM : u ∈ M) (huB : u ∈ B)
    (hu : orderOf u = 2) : fusionStronglyEmbedded (B.subgroupOf M) := by
  refine ⟨fun htop => hMB (Subgroup.subgroupOf_eq_top.mp htop), ?_, fun g hg => ?_⟩
  · have hmem : (⟨u, huM⟩ : M) ∈ B.subgroupOf M := huB
    have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
    rw [Subgroup.orderOf_mk, hu] at hdvd
    exact even_iff_two_dvd.mpr hdvd
  · have hgB : (g : Y) ∉ B := hg
    refine (hB.2.2 (g : Y) hgB).of_dvd_nat ?_
    rw [← Subgroup.card_map_of_injective M.subtype_injective]
    apply Subgroup.card_dvd_of_le
    rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
    refine ⟨hy1, ?_⟩
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy2
    exact Subgroup.mem_map.mpr ⟨(z : Y), hz, by simp⟩

theorem card_eq_of_dvd
    {Q : Type*} [Group Q] (hQ : fusionIsBenderGroup Q)
    (hdvd : Nat.card Q ∣ 29120) : Nat.card Q = 29120 := by
  have hle : Nat.card Q ≤ 29120 := Nat.le_of_dvd (by norm_num) hdvd
  rcases hQ with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · exfalso
    rw [Nat.card_congr e.toEquiv, CFSG.Walter.psl2_even_card (by omega)] at hdvd
    have h4 : (2 ^ f) ^ 2 = 4 ^ f := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have h3 : 3 ∣ (2 ^ f) ^ 2 - 1 := by
      have hmod : 4 ^ f % 3 = 1 := by
        rw [Nat.pow_mod]
        norm_num
      have hpos : 1 ≤ 4 ^ f := Nat.one_le_pow _ _ (by norm_num)
      rw [h4]
      omega
    have := (h3.mul_left (2 ^ f)).trans hdvd
    norm_num at this
  · exfalso
    have hc := CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psu3_mul_gcd
      (p := f) (by omega)
    rw [← Nat.card_congr e.toEquiv] at hc
    have hg : Nat.gcd 3 (2 ^ f + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    rcases (show f = 2 ∨ 3 ≤ f by omega) with rfl | hf3
    · norm_num at hc
      omega
    · have h8 : 8 ≤ 2 ^ f := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
      have h1 : 512 ≤ (2 ^ f) ^ 3 := by
        calc 512 = 8 ^ 3 := by norm_num
          _ ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left h8 3
      have h2 : 63 ≤ (2 ^ f) ^ 2 - 1 := by
        have : 64 ≤ (2 ^ f) ^ 2 := by
          calc 64 = 8 ^ 2 := by norm_num
            _ ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left h8 2
        omega
      have h3 : 513 ≤ (2 ^ f) ^ 3 + 1 := by omega
      have hbig : 512 * (63 * 513) ≤ (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
      have hsmall : Nat.card Q * Nat.gcd 3 (2 ^ f + 1) ≤ 29120 * 3 := Nat.mul_le_mul hle hg
      omega
  · rcases (show a = 1 ∨ 2 ≤ a by omega) with rfl | ha2
    · rw [Nat.card_congr e.toEquiv, CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz]
      norm_num
    · exfalso
      rw [Nat.card_congr e.toEquiv,
        CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz] at hle
      have h32 : 32 ≤ 2 ^ (2 * a + 1) := by
        calc 32 = 2 ^ 5 := by norm_num
          _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h1 : 1024 ≤ (2 ^ (2 * a + 1)) ^ 2 := by
        calc 1024 = 32 ^ 2 := by norm_num
          _ ≤ (2 ^ (2 * a + 1)) ^ 2 := Nat.pow_le_pow_left h32 2
      have hbig : 1024 * 1025 * 31 ≤ (2 ^ (2 * a + 1)) ^ 2 * ((2 ^ (2 * a + 1)) ^ 2 + 1) *
          (2 ^ (2 * a + 1) - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 (by omega)) (by omega)
      omega

variable {X : Type} [Group X] [Finite X] {T : Sylow 2 X} {D : Subgroup X}

theorem le_normalizer_of_sylowCenter_le
    (h : G3a.BorelSetup T D) (hX : Nat.card X = 29120)
    {M : Subgroup X} (hM : M ≠ ⊤) (hZM : sylowCenter (T : Subgroup X) ≤ M) :
    M ≤ Subgroup.normalizer ((T : Subgroup X) : Set X) := by
  by_contra hMB
  obtain ⟨z₁, hz₁, z₂, hz₂, hz₁1, hz₂1, hz₁₂⟩ :=
    GoldType.exists_ne_one_of_two_lt (S := sylowCenter (T : Subgroup X)) (by
      have := h.four
      omega)
  have hord : ∀ z ∈ sylowCenter (T : Subgroup X), z ≠ 1 → orderOf z = 2 := fun z hz hz1 =>
    orderOf_eq_prime (h.sq z hz) hz1
  have hSE := fusionStronglyEmbedded_subgroupOf h.se hMB (hZM hz₁)
    (Subgroup.le_normalizer (sylowCenter_le _ hz₁)) (hord z₁ hz₁ hz₁1)
  rcases CFSG.Open.bender_strongly_embedded_normal_series M _ hSE with
    hcq | ⟨M₀, N₀, hM₀, hN₀, hMN, -, -, -, hBN⟩
  ·
    apply hz₁₂
    have hc : Commute (⟨z₁, hZM hz₁⟩ : M) ⟨z₂, hZM hz₂⟩ :=
      Subtype.ext ((mem_sylowCenter.mp hz₂).2 z₁ (sylowCenter_le _ hz₁))
    have := commuting_involutions_eq_of_cyclic_or_quaternion hcq
      (by rw [Subgroup.orderOf_mk]; exact hord z₁ hz₁ hz₁1)
      (by rw [Subgroup.orderOf_mk]; exact hord z₂ hz₂ hz₂1) hc
    exact congrArg Subtype.val this
  ·
    have hdvd : Nat.card (↥N₀ ⧸ M₀.subgroupOf N₀) ∣ Nat.card X :=
      (Subgroup.card_quotient_dvd_card _).trans ((Subgroup.card_subgroup_dvd_card N₀).trans
        (Subgroup.card_subgroup_dvd_card M))
    have hQ := card_eq_of_dvd hBN (hX ▸ hdvd)
    have hle1 : Nat.card (↥N₀ ⧸ M₀.subgroupOf N₀) ≤ Nat.card N₀ :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    have hle2 : Nat.card N₀ ≤ Nat.card M :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card N₀)
    have hle3 : Nat.card M ≤ Nat.card X :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card M)
    exact hM ((Subgroup.card_eq_iff_eq_top M).mp (by omega))

end G32Q

end CFSG.Goldschmidt
