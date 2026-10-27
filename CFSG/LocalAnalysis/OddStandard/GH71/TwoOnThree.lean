module

public import CFSG.LocalAnalysis.SignalizerFunctor.Coprime
public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG

variable {G : Type} [Group G]

theorem centralizes_of_five [Finite G] {F F₀ : Subgroup G} {y : G} {k : ℕ}
    (hy : orderOf y = 5 ^ k) (hyF : y ∈ normalizer (F : Set G)) (hF3 : IsPGroup 3 ↥F)
    (hF₀F : F₀ ≤ F) (hyF₀ : F₀ ≤ centralizer ({y} : Set G)) (hidx : F₀.relIndex F ≤ 9) :
    F ≤ centralizer ({y} : Set G) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set A := zpowers y with hA
  have hA5 : IsPGroup 5 ↥A := IsPGroup.of_card (by rw [Nat.card_zpowers, hy])
  have hAF : A ≤ normalizer (F : Set G) := zpowers_le.mpr hyF
  let _action := SignalizerFunctor.Helpers.conjugationAction A F hAF
  have hmod := hA5.card_modEq_card_fixedPoints (α := ↥F)
  set C := F ⊓ centralizer (A : Set G) with hC
  have hfix' : Nat.card (FixedPoints.subgroup A F) = Nat.card C := by
    have hmap := SignalizerFunctor.Helpers.conjugation_fixed_subgroup_map A F hAF
    rw [hC, ← hmap, Subgroup.card_map_of_injective F.subtype_injective]
  have hfix : Nat.card (MulAction.fixedPoints A ↥F) = Nat.card C := hfix'
  rw [hfix] at hmod
  have hcenA : centralizer (A : Set G) = centralizer ({y} : Set G) := by
    rw [hA, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hCF : C ≤ F := inf_le_left
  have hF₀C : F₀ ≤ C := le_inf hF₀F (hcenA ▸ hyF₀)
  set i := C.relIndex F with hi
  have hcardF : i * Nat.card C = Nat.card F := by
    have := relIndex_mul_card C F
    rwa [inf_of_le_left hCF] at this
  have hidiv : i ∣ F₀.relIndex F := Dvd.intro_left _ (relIndex_mul_relIndex F₀ C F hF₀C hCF)
  obtain ⟨a, ha⟩ := hF3.exists_card_eq
  have hiF : i ∣ 3 ^ a := ha ▸ Dvd.intro _ hcardF
  obtain ⟨j, hj, hij⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hiF
  have hFpos : 0 < F₀.relIndex F :=
    Nat.pos_of_dvd_of_pos (relIndex_dvd_card F₀ F) Nat.card_pos
  have hi9 : i ≤ 9 := (Nat.le_of_dvd hFpos hidiv).trans hidx
  obtain ⟨b, hb⟩ := (hF3.to_le hCF).exists_card_eq
  have hcop : Nat.Coprime 5 (Nat.card C) := by
    rw [hb]; exact Nat.Coprime.pow_right b (by norm_num)
  have hipos : 1 ≤ i := by rw [hij]; exact Nat.one_le_pow _ _ (by norm_num)
  have hle : Nat.card C ≤ i * Nat.card C := Nat.le_mul_of_pos_left _ hipos
  rw [← hcardF] at hmod
  have hdvd : 5 ∣ i * Nat.card C - Nat.card C := (Nat.modEq_iff_dvd' hle).mp hmod.symm
  have hdvd' : 5 ∣ (i - 1) * Nat.card C := by
    rwa [Nat.sub_mul, one_mul]
  have h5 : 5 ∣ i - 1 := hcop.dvd_of_dvd_mul_right hdvd'
  have hi1 : i = 1 := by
    have hj2 : j ≤ 2 := by
      by_contra hj2
      have : 3 ^ 3 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← hij] at this
      omega
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · simpa using hij
    · exfalso; rw [hij] at h5; norm_num at h5
    · exfalso; rw [hij] at h5; norm_num at h5
  have hFC : F ≤ C := relIndex_eq_one.mp hi1
  intro f hf
  have := (hFC hf).2
  rwa [hcenA] at this

theorem le_of_isPGroup_two_of_odd_index [Finite G] {C O T : Subgroup G}
    (hT : IsPGroup 2 ↥T) (hTC : T ≤ normalizer (C : Set G)) (hOC : O ≤ normalizer (C : Set G))
    (hTO : T ≤ C ⊔ O) (hO : Odd (Nat.card O)) : T ≤ C := by
  have h1 := RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hTC
  have h2 := RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hOC
  set a := C.relIndex (C ⊔ T)
  set b := C.relIndex (C ⊔ O)
  have ha : a * Nat.card C = Nat.card (C ⊔ T : Subgroup G) := by
    have := relIndex_mul_card C (C ⊔ T)
    rwa [inf_of_le_left le_sup_left] at this
  have hb : b * Nat.card C = Nat.card (C ⊔ O : Subgroup G) := by
    have := relIndex_mul_card C (C ⊔ O)
    rwa [inf_of_le_left le_sup_left] at this
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have haT : a ∣ Nat.card T := by
    refine ⟨Nat.card (C ⊓ T : Subgroup G), ?_⟩
    have : a * Nat.card C * Nat.card (C ⊓ T : Subgroup G) = Nat.card C * Nat.card T := by
      rw [ha]; exact h1
    nlinarith [this]
  have hbO : b ∣ Nat.card O := by
    refine ⟨Nat.card (C ⊓ O : Subgroup G), ?_⟩
    have : b * Nat.card C * Nat.card (C ⊓ O : Subgroup G) = Nat.card C * Nat.card O := by
      rw [hb]; exact h2
    nlinarith [this]
  have hab : a ∣ b :=
    Dvd.intro _ (relIndex_mul_relIndex C (C ⊔ T) (C ⊔ O) le_sup_left (sup_le le_sup_left hTO))
  have hbodd : Odd b := Odd.of_dvd_nat hO hbO
  have haodd : Odd a := Odd.of_dvd_nat hbodd hab
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  rw [hn] at haT
  obtain ⟨k, hk, hak⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp haT
  have ha1 : a = 1 := by
    rcases k with _ | k
    · simpa using hak
    · exfalso
      rw [hak] at haodd
      exact (Nat.not_even_iff_odd.mpr haodd) (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  exact le_sup_right.trans (relIndex_eq_one.mp ha1)

end CFSG.OddStandard.GH71
