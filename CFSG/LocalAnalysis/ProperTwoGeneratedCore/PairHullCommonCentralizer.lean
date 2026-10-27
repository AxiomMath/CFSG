module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherEscapingRankTwo
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator

public section

namespace CFSG.ProperTwoGeneratedCore.PairHullCommonCentralizer

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.Assembly
open CFSG.BenderSuzuki.PFAppendixIII CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator

variable {G : Type} [Group G]

theorem mem_localHull_of_isConj {z w t : G} (h : IsConj z t) (hcomm : Commute t w) :
    t ∈ localInvolutionPointHull z w := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  refine mem_localInvolutionPointHull ⟨c⁻¹, ?_⟩ hcomm
  simp only [rightConjugateElem, inv_inv]

theorem conj_mem_localHull_of_commute {z w x c : G} (hc : Commute c w)
    (hx : x ∈ localInvolutionPointHull z w) :
    c⁻¹ * x * c ∈ localInvolutionPointHull z w := by
  have h := conj_mem_localInvolutionPointHull (z := z) c hx
  have hw : c⁻¹ * w * c = w := by
    rw [mul_assoc, ← hc.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  rwa [hw] at h

theorem commutator_centralizer_le_localHull {z w t : G} (I : Subgroup G)
    (ht : t ∈ localInvolutionPointHull z w) :
    ⁅I ⊓ Subgroup.centralizer {w}, Subgroup.zpowers t⁆ ≤ localInvolutionPointHull z w := by
  rw [Subgroup.commutator_le]
  intro c hc k hk
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  have hcw : Commute c w :=
    (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2)
  have htn : t ^ n ∈ localInvolutionPointHull z w := Subgroup.zpow_mem _ ht n
  have hconj : c * t ^ n * c⁻¹ ∈ localInvolutionPointHull z w := by
    have := conj_mem_localHull_of_commute (z := z) (c := c⁻¹) hcw.inv_left htn
    simpa only [inv_inv] using this
  exact Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ htn)

theorem centralizer_inf_centralizer_eq_bot [Finite G] (hZ : Subgroup.center G = ⊥)
    {z t u : G} (hz : orderOf z = 2) (hzt : IsConj z t) (hu : orderOf u = 2) (hut : u ≠ t)
    (huz : Commute u z) (hutc : Commute u t)
    (I : Subgroup G) (hIodd : Odd (Nat.card I))
    (huI : u ∈ Subgroup.normalizer (I : Set G)) (htI : t ∈ Subgroup.normalizer (I : Set G))
    (hgen : Subgroup.zpowers z ⊔ Subgroup.zpowers t ⊔ ⁅I, Subgroup.zpowers t⁆ = ⊤)
    {g : G} (hgL : g ∈ localInvolutionPointHull z u) (hgt : g⁻¹ * z * g = t) :
    Subgroup.centralizer (localInvolutionPointHull z u : Set G) ⊓
      Subgroup.centralizer (localInvolutionPointHull z (u * z) : Set G) = ⊥ := by
  set A := Subgroup.centralizer (localInvolutionPointHull z u : Set G) ⊓
      Subgroup.centralizer (localInvolutionPointHull z (u * z) : Set G) with hA
  have ht : orderOf t = 2 := by
    obtain ⟨c, hc⟩ := hzt
    exact hc.orderOf_eq.symm.trans hz
  have hzLu : z ∈ localInvolutionPointHull z u := distinguished_mem_localInvolutionPointHull huz
  have htLu : t ∈ localInvolutionPointHull z u := mem_localHull_of_isConj hzt hutc.symm
  have hgu : Commute g u :=
    Subgroup.mem_centralizer_singleton_iff.mp (localInvolutionPointHull_le_centralizer z u hgL)
  have hconjv : g⁻¹ * (u * z) * g = u * t := by
    rw [← hgt]
    have : g⁻¹ * u * g = u := by rw [mul_assoc, ← hgu.eq, ← mul_assoc, inv_mul_cancel, one_mul]
    calc g⁻¹ * (u * z) * g = (g⁻¹ * u * g) * (g⁻¹ * z * g) := by group
      _ = u * (g⁻¹ * z * g) := by rw [this]
  have hAut : ∀ a ∈ A, ∀ y ∈ localInvolutionPointHull z (u * t), Commute a y := by
    intro a haA y hy
    have hy' : g * y * g⁻¹ ∈ localInvolutionPointHull z (u * z) := by
      have h := conj_mem_localInvolutionPointHull (z := z) g⁻¹ hy
      have hw : g⁻¹⁻¹ * (u * t) * g⁻¹ = u * z := by
        rw [inv_inv, ← hconjv]; group
      rw [hw] at h
      simpa only [inv_inv] using h
    have hag : Commute a g :=
      ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp haA).1 g hgL)).symm
    have hay' : Commute a (g * y * g⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp haA).2 _ hy').symm
    have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
    rw [this]
    exact (hag.inv_right.mul_right hay').mul_right hag
  have htLut : t ∈ localInvolutionPointHull z (u * t) := by
    refine mem_localHull_of_isConj hzt ?_
    exact (hutc.symm.mul_right (Commute.refl t)).symm.symm
  have hIt : ⁅I, Subgroup.zpowers t⁆ ≤ Subgroup.centralizer (A : Set G) := by
    have hgen2 := odd_four_group_ambient_commutator_generation I u t hu ht hut hutc huI htI
      hIodd
    rw [hgen2]
    apply sup_le
    · intro x hx
      have hxL := commutator_centralizer_le_localHull (z := z) I htLu hx
      rw [Subgroup.mem_centralizer_iff]
      intro a haA
      exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp haA).1 x hxL)).symm
    · intro x hx
      have hxL := commutator_centralizer_le_localHull (z := z) I htLut hx
      rw [Subgroup.mem_centralizer_iff]
      intro a haA
      exact (hAut a haA x hxL).eq
  have htop : (⊤ : Subgroup G) ≤ Subgroup.centralizer (A : Set G) := by
    rw [← hgen]
    refine sup_le (sup_le ?_ ?_) hIt
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro a haA
      exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp haA).1 z hzLu)).symm
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro a haA
      exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp haA).1 t htLu)).symm
  rw [eq_bot_iff, ← hZ]
  intro a haA
  rw [Subgroup.mem_center_iff]
  intro x
  exact (Subgroup.mem_centralizer_iff.mp (htop (Subgroup.mem_top x)) a haA).symm

theorem eq_one_of_centralizes_both [Finite G] (hZ : Subgroup.center G = ⊥)
    {z t u : G} (hz : orderOf z = 2) (hzt : IsConj z t) (hu : orderOf u = 2) (hut : u ≠ t)
    (huz : Commute u z) (hutc : Commute u t)
    (I : Subgroup G) (hIodd : Odd (Nat.card I))
    (huI : u ∈ Subgroup.normalizer (I : Set G)) (htI : t ∈ Subgroup.normalizer (I : Set G))
    (hgen : Subgroup.zpowers z ⊔ Subgroup.zpowers t ⊔ ⁅I, Subgroup.zpowers t⁆ = ⊤)
    {g : G} (hgL : g ∈ localInvolutionPointHull z u) (hgt : g⁻¹ * z * g = t)
    {x : G} (hxv : x ∈ Subgroup.centralizer (localInvolutionPointHull z (u * z) : Set G))
    (hxu : ∀ l ∈ localInvolutionPointHull z u, x * l * x⁻¹ = l) : x = 1 := by
  have h := centralizer_inf_centralizer_eq_bot hZ hz hzt hu hut huz hutc I hIodd huI htI hgen
    hgL hgt
  have hx : x ∈ Subgroup.centralizer (localInvolutionPointHull z u : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have := hxu l hl
    calc l * x = (x * l * x⁻¹) * x := by rw [this]
      _ = x * l := by group
  have : x ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_inf.mpr ⟨hx, hxv⟩
  exact Subgroup.mem_bot.mp this

end CFSG.ProperTwoGeneratedCore.PairHullCommonCentralizer
