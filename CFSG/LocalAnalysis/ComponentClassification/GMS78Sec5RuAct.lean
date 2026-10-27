module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuMask
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuSylow

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII
open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ

namespace RuQCode

theorem glList_length : glList.length = 168 := by
  decide +kernel

theorem glList_nodup : glList.Nodup := by
  decide +kernel

theorem fix_image_check : (invList.all fun r => let A := adMat r
    all256.all fun m => maskApply A m != m ||
      all256.any fun n => maskApply A n ^^^ n == m) = true := by
  decide +kernel

theorem exists_image_eq {r : Lin8} (hr : r ∈ invList) {m : Nat} (hm : m < 256)
    (hfix : maskApply (adMat r) m = m) : ∃ n < 256, maskApply (adMat r) n ^^^ n = m := by
  have h := fix_image_check
  simp only [List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, List.any_eq_true,
    beq_iff_eq, RuSimCode.mem_all256] at h
  rcases h r hr m hm with h | ⟨n, hn, h⟩
  · exact absurd hfix h
  · exact ⟨n, hn, h⟩

theorem fix_image_commute_check : (invList.all fun r₁ => let A₁ := adMat r₁
    let F := all256.filter fun m => maskApply A₁ m == m
    invList.all fun r₂ => r₁ == r₂ || linComp r₁ r₂ != linComp r₂ r₁ ||
    (let A₂ := adMat r₂
     F.all fun m => maskApply A₂ m != m ||
       F.any fun n => maskApply A₂ n ^^^ n == m)) = true := by
  decide +kernel

theorem exists_image_eq_of_commute {r₁ r₂ : Lin8} (h₁ : r₁ ∈ invList) (h₂ : r₂ ∈ invList)
    (hne : r₁ ≠ r₂) (hc : linComp r₁ r₂ = linComp r₂ r₁) {m : Nat} (hm : m < 256)
    (hm₁ : maskApply (adMat r₁) m = m) (hm₂ : maskApply (adMat r₂) m = m) :
    ∃ n < 256, maskApply (adMat r₁) n = n ∧ maskApply (adMat r₂) n ^^^ n = m := by
  have h := fix_image_commute_check
  simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    List.any_eq_true, List.mem_filter, RuSimCode.mem_all256] at h
  rcases h r₁ h₁ r₂ h₂ with (h | h) | h
  · exact absurd h hne
  · exact absurd hc h
  · rcases h m ⟨hm, hm₁⟩ with h | ⟨n, ⟨hn, hn₁⟩, h⟩
    · exact absurd hm₂ h
    · exact ⟨n, hn, hn₁, h⟩

end RuQCode

namespace Sec3.SzR

variable {G : Type} [Group G] [Finite G] {L T R R₂ : Subgroup G} {y d : G}

namespace MaskCoords

variable {μ : G → ℕ} {ν : G → Fin 8} (hM : MaskCoords L T R μ ν)
include hM

theorem exists_code_eq
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168) {r : Lin8} (hr : r ∈ glList) :
    ∃ g ∈ normalizer (R : Set G), (∀ b ∈ gmsA L T, ν (g * b * g⁻¹) = linApply r (ν b)) ∧
      ∀ x ∈ R, μ (g * x * g⁻¹) = maskApply (adMat r) (μ x) := by
  classical
  choose! rOf hrGL hrA hrR using hM.act
  by_contra hno
  have hne : ∀ g ∈ normalizer (R : Set G), rOf g ≠ r := by
    intro g hg h
    exact hno ⟨g, hg, by rw [← h]; exact hrA g hg, by rw [← h]; exact hrR g hg⟩
  have hmem : ∀ g ∈ normalizer (R : Set G), rOf g ∈ glList.erase r := fun g hg =>
    (List.mem_erase_of_ne (hne g hg)).mpr (hrGL g hg)
  have hinj : ∀ a ∈ normalizer (R : Set G), ∀ b ∈ normalizer (R : Set G), rOf a = rOf b →
      a⁻¹ * b ∈ R := by
    intro a ha b hb h
    rw [← hNC]
    refine mem_inf.mpr ⟨mul_mem (inv_mem ha) hb, mem_centralizer_iff.mpr fun c hc => ?_⟩
    have hac : a * c * a⁻¹ ∈ gmsA L T := hM.normA a ha c hc
    have hbc : b * c * b⁻¹ ∈ gmsA L T := hM.normA b hb c hc
    have h1 := hM.eq_of_ν_eq hac hbc (by rw [hrA a ha c hc, hrA b hb c hc, h])
    calc c * (a⁻¹ * b) = a⁻¹ * (a * c * a⁻¹) * b := by group
      _ = a⁻¹ * (b * c * b⁻¹) * b := by rw [h1]
      _ = a⁻¹ * b * c := by group
  have h1 := card_le_length_mul_card le_normalizer rOf (glList.erase r) hmem hinj
  rw [List.length_erase_of_mem hr, RuQCode.glList_length] at h1
  have h2 := (R.subgroupOf (normalizer (R : Set G))).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe le_normalizer).toEquiv] at h2
  have h3 : (R.subgroupOf (normalizer (R : Set G))).index = 168 := hidx
  rw [h3] at h2
  have hpos : 0 < Nat.card R := Nat.card_pos
  omega

end MaskCoords

end Sec3.SzR

end CFSG.ComponentClassification.GMS78
