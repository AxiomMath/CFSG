module

public import CFSG.Foundations.Basic
public import CFSG.Open.LocalVocabulary

import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComm
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.SupCommute
import CFSG.GroupTheory.DisjointSupCard
import CFSG.GroupTheory.LocalCores.ComponentRank
import CFSG.RankThree.PartTwo.Sec14.Ronan148JFix
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open Subgroup

variable {X : Type} [Group X] [Finite X]

private theorem component_le_centralizer_of_ne {C D : Subgroup X} (hC : CFSG.IsComponent C)
    (hD : CFSG.IsComponent D) (hCD : C ≠ D) :
    C ≤ Subgroup.centralizer (D : Set X) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    ((CFSG.LocalCores.distinct_components_commute hC hD).resolve_left hCD)

private theorem exists_isElemAbelian_card_sq_of_central {p : ℕ} (hp : p.Prime)
    {C : Subgroup X} {x : X} (z : ↥C) (hxC : x ∈ C) (hxord : orderOf x = p)
    (hzord : orderOf z = p) (hzcen : z ∈ Subgroup.center ↥C)
    (hxnc : ∃ c ∈ C, x * c ≠ c * x) :
    ∃ B : Subgroup X, B ≤ C ∧ IsElemAbelian p B ∧ Nat.card B = p ^ 2 := by
  have hzXord : orderOf (z : X) = p := by rw [Subgroup.orderOf_coe, hzord]
  have hxXord : orderOf x = p := hxord
  have hzpow : (z : X) ^ p = 1 := by simpa [hzXord] using pow_orderOf_eq_one (z : X)
  have hzcent : Subgroup.zpowers (z : X) ≤ Subgroup.centralizer (C : Set X) := by
    refine Subgroup.zpowers_le.mpr ?_
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzcen ⟨l, hl⟩)
  obtain ⟨hBab, hBcard⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.isElemAbelian_sup_zpowers hp
      (CFSG.Open.isElemAbelian_zpowers hzpow)
      (by rw [Nat.card_zpowers, hzXord, pow_one]) hzcent hxC hxXord hxnc
  refine ⟨Subgroup.zpowers (z : X) ⊔ Subgroup.zpowers x,
    sup_le (Subgroup.zpowers_le.mpr z.2) (Subgroup.zpowers_le.mpr hxC), hBab, ?_⟩
  simpa using hBcard

private theorem four_le_pRank_of_central {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L J J' : Subgroup X} (hL : CFSG.IsComponent L) (hJ : CFSG.IsComponent J)
    (hJ' : CFSG.IsComponent J') (hLJ : L ≠ J) (hLJ' : L ≠ J') (hJJ' : J ≠ J')
    (hdL : p ∣ Nat.card L) (hdJ : p ∣ Nat.card J) (hdJ' : p ∣ Nat.card J')
    (hz : ∃ z : ↥L, orderOf z = p ∧ z ∈ Subgroup.center ↥L) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  obtain ⟨x, hxL, hxord, hxnc⟩ :=
    CFSG.LocalCores.exists_noncentral_of_isComponent hp hp2 hL hdL
  obtain ⟨z, hzord, hzcen⟩ := hz
  obtain ⟨B, hBL, hBab, hBcard⟩ :=
    exists_isElemAbelian_card_sq_of_central hp z hxL hxord hzord hzcen hxnc
  have h4 := CFSG.LocalAnalysis.RankThreeUC.AGL81C.add_two_le_pRank_of_three_components
    hp hL hJ hJ' hLJ hLJ' hJJ' hBL hBab hBcard
    (CFSG.LocalCores.exists_noncentral_of_isComponent hp hp2 hJ hdJ)
    (CFSG.LocalCores.exists_noncentral_of_isComponent hp hp2 hJ' hdJ')
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank p (⊤ : Subgroup X)] at h4
  omega

private theorem exists_noncentral_orderOf_eq_prime_centralizing {p : ℕ} (hp : p.Prime)
    {F C : Subgroup X} (hF : IsPGroup p F)
    (hFC : F ≤ Subgroup.normalizer (C : Set X)) (hdC : p ∣ Nat.card C)
    (hZ : ¬ ∃ z : ↥C, orderOf z = p ∧ z ∈ Subgroup.center ↥C) :
    ∃ y ∈ C, orderOf y = p ∧ y ∈ Subgroup.centralizer (F : Set X) ∧
      ∃ c ∈ C, y * c ≠ c * y := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hyC, hy1, hyp, hycent⟩ :=
    CFSG.RankThree.PartTwo.Sec14.Ronan148J.exists_pow_eq_one_mem_centralizer hF hFC hdC
  have hyord : orderOf y = p := orderOf_eq_prime hyp hy1
  refine ⟨y, hyC, hyord, hycent, ?_⟩
  by_contra h
  push Not at h
  exact hZ ⟨⟨y, hyC⟩, by simpa using hyord,
    Subgroup.mem_center_iff.mpr fun c => Subtype.ext (h c c.2).symm⟩

private theorem exists_isElemAbelian_card_sq_of_two_components {p : ℕ} (hp : p.Prime)
    {C₁ C₂ C₃ F : Subgroup X} (h₁ : CFSG.IsComponent C₁) (h₂ : CFSG.IsComponent C₂)
    (h₃ : CFSG.IsComponent C₃) (h₁₂ : C₁ ≠ C₂) (h₁₃ : C₁ ≠ C₃) (h₂₃ : C₂ ≠ C₃)
    {y₂ y₃ : X} (hy₂C : y₂ ∈ C₂) (hy₂ord : orderOf y₂ = p)
    (hy₂nc : ∃ c ∈ C₂, y₂ * c ≠ c * y₂)
    (hy₂cent : y₂ ∈ Subgroup.centralizer (F : Set X))
    (hy₃C : y₃ ∈ C₃) (hy₃ord : orderOf y₃ = p)
    (hy₃cent : y₃ ∈ Subgroup.centralizer (F : Set X)) :
    ∃ A : Subgroup X, IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧
      A ≤ Subgroup.centralizer (C₁ : Set X) ∧ A ≤ Subgroup.centralizer (F : Set X) ∧
      y₂ ∈ A ∧ y₃ ∈ A := by
  have hC₂₁ := component_le_centralizer_of_ne h₂ h₁ h₁₂.symm
  have hC₃₁ := component_le_centralizer_of_ne h₃ h₁ h₁₃.symm
  have hC₃₂ := component_le_centralizer_of_ne h₃ h₂ h₂₃.symm
  have hy₃pow : y₃ ^ p = 1 := by rw [← hy₃ord]; exact pow_orderOf_eq_one y₃
  obtain ⟨hAab, hAcard⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.isElemAbelian_sup_zpowers hp
      (CFSG.Open.isElemAbelian_zpowers hy₃pow)
      (by rw [Nat.card_zpowers, hy₃ord, pow_one])
      (Subgroup.zpowers_le.mpr (hC₃₂ hy₃C)) hy₂C hy₂ord hy₂nc
  refine ⟨Subgroup.zpowers y₃ ⊔ Subgroup.zpowers y₂, hAab, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hAcard
  · exact sup_le (Subgroup.zpowers_le.mpr (hC₃₁ hy₃C)) (Subgroup.zpowers_le.mpr (hC₂₁ hy₂C))
  · exact sup_le (Subgroup.zpowers_le.mpr hy₃cent) (Subgroup.zpowers_le.mpr hy₂cent)
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y₂)
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y₃)

private theorem exists_isElemAbelian_card_three_of_le_centralizer {p : ℕ} (hp : p.Prime)
    {C₁ F A : Subgroup X} {y₁ : X} (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2)
    (hAC : A ≤ Subgroup.centralizer (C₁ : Set X))
    (hAF : A ≤ Subgroup.centralizer (F : Set X))
    (hy₁C : y₁ ∈ C₁) (hy₁ord : orderOf y₁ = p)
    (hy₁nc : ∃ c ∈ C₁, y₁ * c ≠ c * y₁)
    (hy₁cent : y₁ ∈ Subgroup.centralizer (F : Set X)) :
    ∃ Y : Subgroup X, IsElemAbelian p Y ∧ Nat.card Y = p ^ 3 ∧ A ≤ Y ∧ y₁ ∈ Y ∧
      Y ≤ Subgroup.centralizer (F : Set X) := by
  obtain ⟨hYab, hYcard⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.isElemAbelian_sup_zpowers hp hA hAc hAC
      hy₁C hy₁ord hy₁nc
  refine ⟨A ⊔ Subgroup.zpowers y₁, hYab, ?_, le_sup_left,
    Subgroup.mem_sup_right (Subgroup.mem_zpowers y₁), ?_⟩
  · simpa using hYcard
  · exact sup_le hAF (Subgroup.zpowers_le.mpr hy₁cent)

private theorem false_of_le_isElemAbelian_card_three {p : ℕ} (hp : p.Prime)
    {C₁ F A Y : Subgroup X} (hFc : Nat.card F = p ^ 2)
    (hAc : Nat.card A = p ^ 2) (hYcard : Nat.card Y = p ^ 3)
    (hFY : F ≤ Y) (hAY : A ≤ Y) (hAC : A ≤ Subgroup.centralizer (C₁ : Set X))
    (hF₁ : ∀ f ∈ F, f ≠ 1 → ¬ C₁ ≤ Subgroup.centralizer ({f} : Set X)) : False := by
  have hdisj : F ⊓ A ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card ↥F * Nat.card ↥A ≤ Nat.card ↥Y := by
      calc Nat.card ↥F * Nat.card ↥A ≤ Nat.card ↥(F ⊔ A) :=
            CFSG.GroupTheory.card_mul_card_le_card_sup_of_disjoint (disjoint_iff.mpr hbot)
        _ ≤ Nat.card ↥Y := Subgroup.card_le_of_le (sup_le hFY hAY)
    have hp4 : p ^ 4 ≤ p ^ 3 := by
      calc p ^ 4 = p ^ 2 * p ^ 2 := by rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add]
        _ = Nat.card ↥F * Nat.card ↥A := by rw [hFc, hAc]
        _ ≤ Nat.card ↥Y := hcard
        _ = p ^ 3 := hYcard
    have : 4 ≤ 3 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hp4
    omega
  obtain ⟨f, hfFA, hf1⟩ :=
    (Subgroup.nontrivial_iff_exists_ne_one (F ⊓ A)).mp
      ((Subgroup.nontrivial_iff_ne_bot (F ⊓ A)).mpr hdisj)
  exact (hF₁ f hfFA.1 hf1) fun c hc =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hAC hfFA.2) c hc)

private theorem four_le_pRank_of_not_le_isElemAbelian_card_three {p : ℕ} (hp : p.Prime)
    {F Y : Subgroup X} (hF : IsElemAbelian p F) (hY : IsElemAbelian p Y)
    (hYcard : Nat.card Y = p ^ 3) (hFY : ¬ F ≤ Y)
    (hYcentF : Y ≤ Subgroup.centralizer (F : Set X)) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨f, hfF, hfY⟩ := Set.not_subset.mp hFY
  have hf1 : f ≠ 1 := by rintro rfl; exact hfY (Y.one_mem)
  have hford : orderOf f = p := orderOf_eq_prime (hF.2 f hfF) hf1
  have hfpow : f ^ p = 1 := by rw [← hford]; exact pow_orderOf_eq_one f
  have hA₀ab : IsElemAbelian p (Subgroup.zpowers f) := isElemAbelian_zpowers hfpow
  have hdisj : Subgroup.zpowers f ⊓ Y = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    have hxpow : x ^ p = 1 := hY.2 x hx.2
    have hxord : orderOf x = p := orderOf_eq_prime hxpow hx1
    have hxA : Subgroup.zpowers x ≤ Subgroup.zpowers f := Subgroup.zpowers_le.mpr hx.1
    have hcard : Nat.card ↥(Subgroup.zpowers f) ≤ Nat.card ↥(Subgroup.zpowers x) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hxord, hford]
    have hEq : Subgroup.zpowers x = Subgroup.zpowers f :=
      Subgroup.eq_of_le_of_card_ge hxA hcard
    have hle : Subgroup.zpowers f ≤ Y := hEq ▸ Subgroup.zpowers_le.mpr hx.2
    exact hfY (hle (Subgroup.mem_zpowers f))
  have hcomm : ∀ a ∈ Subgroup.zpowers f, ∀ b ∈ Y, a * b = b * a := by
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp (hYcentF hb) a (Subgroup.zpowers_le.mpr hfF ha)
  have hKab : IsElemAbelian p (Subgroup.zpowers f ⊔ Y) :=
    IsElemAbelian.sup_of_commute hA₀ab hY hcomm
  have hKcard : Nat.card ↥(Subgroup.zpowers f ⊔ Y) = p ^ 4 := by
    rw [CFSG.card_sup_eq_mul_of_commute _ _ hcomm hdisj,
      show Nat.card ↥(Subgroup.zpowers f) = p by rw [Nat.card_zpowers, hford], hYcard]
    ring
  exact CFSG.SectionRank.le_pRank hp.one_lt le_top hKab hKcard

private theorem four_le_pRank_of_three_components_no_central {p : ℕ} (hp : p.Prime)
    {C₁ C₂ C₃ F : Subgroup X}
    (h₁ : CFSG.IsComponent C₁) (h₂ : CFSG.IsComponent C₂) (h₃ : CFSG.IsComponent C₃)
    (h₁₂ : C₁ ≠ C₂) (h₁₃ : C₁ ≠ C₃) (h₂₃ : C₂ ≠ C₃)
    (hd₁ : p ∣ Nat.card C₁) (hd₂ : p ∣ Nat.card C₂) (hd₃ : p ∣ Nat.card C₃)
    (hF : CFSG.Open.IsElemAbelian p F) (hFc : Nat.card F = p ^ 2)
    (hN₁ : F ≤ Subgroup.normalizer (C₁ : Set X))
    (hN₂ : F ≤ Subgroup.normalizer (C₂ : Set X))
    (hN₃ : F ≤ Subgroup.normalizer (C₃ : Set X))
    (hF₁ : ∀ f ∈ F, f ≠ 1 → ¬ C₁ ≤ Subgroup.centralizer ({f} : Set X))
    (hZ₁ : ¬ ∃ z : ↥C₁, orderOf z = p ∧ z ∈ Subgroup.center ↥C₁)
    (hZ₂ : ¬ ∃ z : ↥C₂, orderOf z = p ∧ z ∈ Subgroup.center ↥C₂)
    (hZ₃ : ¬ ∃ z : ↥C₃, orderOf z = p ∧ z ∈ Subgroup.center ↥C₃) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y₁, hy₁C, hy₁ord, hy₁cent, hy₁nc⟩ :=
    exists_noncentral_orderOf_eq_prime_centralizing hp hF.isPGroup hN₁ hd₁ hZ₁
  obtain ⟨y₂, hy₂C, hy₂ord, hy₂cent, hy₂nc⟩ :=
    exists_noncentral_orderOf_eq_prime_centralizing hp hF.isPGroup hN₂ hd₂ hZ₂
  obtain ⟨y₃, hy₃C, hy₃ord, hy₃cent, _⟩ :=
    exists_noncentral_orderOf_eq_prime_centralizing hp hF.isPGroup hN₃ hd₃ hZ₃
  obtain ⟨A, hAab, hAcard, hAcentC, hAcentF, hy₂A, hy₃A⟩ :=
    exists_isElemAbelian_card_sq_of_two_components hp h₁ h₂ h₃ h₁₂ h₁₃ h₂₃
      hy₂C hy₂ord hy₂nc hy₂cent hy₃C hy₃ord hy₃cent
  obtain ⟨Y, hYab, hYcard, hAY, hy₁Y, hYcentF⟩ :=
    exists_isElemAbelian_card_three_of_le_centralizer hp hAab hAcard hAcentC hAcentF
      hy₁C hy₁ord hy₁nc hy₁cent
  by_cases hFY : F ≤ Y
  · exact (false_of_le_isElemAbelian_card_three hp hFc hAcard hYcard hFY hAY hAcentC hF₁).elim
  · exact four_le_pRank_of_not_le_isElemAbelian_card_three hp hF hYab hYcard hFY hYcentF

theorem four_le_pRank_of_three_components {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {C₁ C₂ C₃ F : Subgroup X}
    (h₁ : CFSG.IsComponent C₁) (h₂ : CFSG.IsComponent C₂) (h₃ : CFSG.IsComponent C₃)
    (h₁₂ : C₁ ≠ C₂) (h₁₃ : C₁ ≠ C₃) (h₂₃ : C₂ ≠ C₃)
    (hd₁ : p ∣ Nat.card C₁) (hd₂ : p ∣ Nat.card C₂) (hd₃ : p ∣ Nat.card C₃)
    (hF : CFSG.Open.IsElemAbelian p F) (hFc : Nat.card F = p ^ 2)
    (hN₁ : F ≤ Subgroup.normalizer (C₁ : Set X)) (hN₂ : F ≤ Subgroup.normalizer (C₂ : Set X))
    (hN₃ : F ≤ Subgroup.normalizer (C₃ : Set X))
    (hF₁ : ∀ f ∈ F, f ≠ 1 → ¬ C₁ ≤ Subgroup.centralizer ({f} : Set X)) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  by_cases hZ₁ : ∃ z : ↥C₁, orderOf z = p ∧ z ∈ Subgroup.center ↥C₁
  · exact four_le_pRank_of_central hp hp2 h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hd₁ hd₂ hd₃ hZ₁
  · by_cases hZ₂ : ∃ z : ↥C₂, orderOf z = p ∧ z ∈ Subgroup.center ↥C₂
    · exact four_le_pRank_of_central hp hp2 h₂ h₁ h₃ h₁₂.symm h₂₃ h₁₃ hd₂ hd₁ hd₃ hZ₂
    · by_cases hZ₃ : ∃ z : ↥C₃, orderOf z = p ∧ z ∈ Subgroup.center ↥C₃
      · exact four_le_pRank_of_central hp hp2 h₃ h₁ h₂ h₁₃.symm h₂₃.symm h₁₂ hd₃ hd₁ hd₂ hZ₃
      · exact four_le_pRank_of_three_components_no_central hp h₁ h₂ h₃ h₁₂ h₁₃ h₂₃
          hd₁ hd₂ hd₃ hF hFc hN₁ hN₂ hN₃ hF₁ hZ₁ hZ₂ hZ₃

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
