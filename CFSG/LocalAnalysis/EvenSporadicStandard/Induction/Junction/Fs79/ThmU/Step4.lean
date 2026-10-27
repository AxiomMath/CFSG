module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.Sylow

public section

namespace CFSG.EvenSporadicStandard.Induction.ThmU

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
  CFSG.ComponentClassification.AschbacherToolkit
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def StarHyp (G : Type) [Group G] [Finite G] : Prop :=
  ∀ J : Subgroup G, MaximalF J → UniversalF J → 2 ≤ CFSG.Open.pRank 2 J →
    ∀ g : G, (∀ a ∈ J, ∀ b ∈ cj g J, a * b = b * a) → cj g J = J

theorem not_universalF_of_swapConfig [Finite G] (hstar : StarHyp G) {A K : Subgroup G}
    {t a : G} (hS : SwapConfig A t a K) (hK : MaximalF K) (hrank : 2 ≤ CFSG.Open.pRank 2 K) :
    ¬ UniversalF K := by
  intro hu
  exact hS.ne (hstar K hK hu hrank t hS.diagComm)

theorem exists_swap_rank_three [Finite G] {B M : Subgroup G} {x y : G} (hS : SwapConfig B x y M)
    (hMrank : 2 ≤ CFSG.Open.pRank 2 M) (hy : y ∉ cj x M) :
    ∃ w₁ w₂ : G, w₁ ∈ cj x M ∧ w₂ ∈ cj x M ∧ orderOf w₁ = 2 ∧ orderOf w₂ = 2 ∧
      w₁ * w₂ = w₂ * w₁ ∧ w₁ ≠ w₂ ∧
      ∃ P : Subgroup G, y ∈ P ∧ w₁ ∈ P ∧ w₂ ∈ P ∧ Nat.card P = 8 ∧
        (∀ p ∈ P, ∀ q ∈ P, p * q = q * p) ∧ (∀ p ∈ P, p * p = 1) ∧
        (∀ p ∈ P, ∀ m ∈ M, p * m = m * p) ∧
        3 ≤ CFSG.Open.pRank 2 (centralizer (M : Set G)) := by
  obtain ⟨v₁, v₂, hv₁, hv₂, ho₁, ho₂, hc, hne⟩ := exists_fourGroup_of_two_le_pRank hMrank
  have hw₁c : x * v₁ * x⁻¹ ∈ cj x M := conj_mem_cj hv₁
  have hw₂c : x * v₂ * x⁻¹ ∈ cj x M := conj_mem_cj hv₂
  have ho₁' : orderOf (x * v₁ * x⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ho₁]
  have ho₂' : orderOf (x * v₂ * x⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ho₂]
  have hw₁₂ : (x * v₁ * x⁻¹) * (x * v₂ * x⁻¹) = (x * v₂ * x⁻¹) * (x * v₁ * x⁻¹) := by
    rw [show (x * v₁ * x⁻¹) * (x * v₂ * x⁻¹) = x * (v₁ * v₂) * x⁻¹ by group,
      show (x * v₂ * x⁻¹) * (x * v₁ * x⁻¹) = x * (v₂ * v₁) * x⁻¹ by group, hc]
  have hwne : x * v₁ * x⁻¹ ≠ x * v₂ * x⁻¹ := by
    intro h
    exact hne ((MulAut.conj x).injective (by simpa [MulAut.conj_apply] using h))
  have hyw₁ : y * (x * v₁ * x⁻¹) = (x * v₁ * x⁻¹) * y :=
    (Subgroup.mem_centralizer_singleton_iff.1 (hS.isCompIn_cj.1 hw₁c)).symm
  have hyw₂ : y * (x * v₂ * x⁻¹) = (x * v₂ * x⁻¹) * y :=
    (Subgroup.mem_centralizer_singleton_iff.1 (hS.isCompIn_cj.1 hw₂c)).symm
  have hyw₁ne : y ≠ x * v₁ * x⁻¹ := fun h => hy (h.symm ▸ hw₁c)
  have hyw₂ne : y ≠ x * v₂ * x⁻¹ := fun h => hy (h.symm ▸ hw₂c)
  have hywne : y ≠ (x * v₁ * x⁻¹) * (x * v₂ * x⁻¹) :=
    fun h => hy (h.symm ▸ (cj x M).mul_mem hw₁c hw₂c)
  obtain ⟨P, hyP, hw₁P, hw₂P, hPcard, hPcomm, hPsq, hPle⟩ :=
    exists_elemAbelian_eight hS.y_ord ho₁' ho₂' hw₁₂ hwne hyw₁ hyw₂ hyw₁ne hyw₂ne hywne
  have hyM : y ∈ centralizer (M : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun m hm =>
      Subgroup.mem_centralizer_singleton_iff.1 (hS.isCompIn.1 hm)
  have hw₁M : x * v₁ * x⁻¹ ∈ centralizer (M : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun m hm => hS.diagComm m hm _ hw₁c
  have hw₂M : x * v₂ * x⁻¹ ∈ centralizer (M : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun m hm => hS.diagComm m hm _ hw₂c
  have hPcentM : ∀ p ∈ P, ∀ m ∈ M, p * m = m * p :=
    fun p hp m hm =>
      (Subgroup.mem_centralizer_iff.1 (hPle (centralizer (M : Set G)) hyM hw₁M hw₂M hp) m hm).symm
  have hrank : 3 ≤ CFSG.Open.pRank 2 (centralizer (M : Set G)) :=
    three_le_pRank_of_involutions hS.y_ord ho₁' ho₂' hw₁₂ hwne hyw₁ hyw₂ hyw₁ne hyw₂ne hywne
      hyM hw₁M hw₂M
  exact ⟨x * v₁ * x⁻¹, x * v₂ * x⁻¹, hw₁c, hw₂c, ho₁', ho₂', hw₁₂, hwne,
    P, hyP, hw₁P, hw₂P, hPcard, hPcomm, hPsq, hPcentM, hrank⟩

theorem step_four [Finite G] (hLB : LayerBalanceAt G) (hglaub : GlaubermanSimplePerfect)
    (hstar : StarHyp G) {K : Subgroup G} (hK : MaximalF K) (hrank : 2 ≤ CFSG.Open.pRank 2 K)
    {a b : G} (ha : GoodInv K a) (hb : BadInv K b) (hab : a * b = b * a) {P : Subgroup G}
    (haP : a ∈ P) (hbP : b ∈ P) (hcard : Nat.card P = 8)
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hsq : ∀ x ∈ P, x * x = 1)
    (hPK : ∀ p ∈ P, ∀ k ∈ K, p * k = k * p) : False := by
  obtain ⟨M, hS, hM, ⟨e⟩⟩ := exists_swapConfig hLB hglaub hK ha hb hab
  have hMrank : 2 ≤ CFSG.Open.pRank 2 M := by
    rw [← pRank_eq_of_mulEquiv e]
    exact hrank
  have hPb : P ≤ centralizer ({b} : Set G) := by
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm p hp b hbP
  obtain ⟨hR, hRbad⟩ :=
    swap_package hLB hglaub hK ha hS hM hPb hPK (fun p hp => hcomm p hp a haP) haP
  obtain ⟨r₁, r₂, hr₁, hr₂, ho₁, ho₂, ho₃, h12⟩ :=
    exists_fourGroup_of_relIndex_two hcard hcomm hsq inf_le_left hR
  have hr₃ : r₁ * r₂ ∈ P ⊓ normalizer (M : Set G) := Subgroup.mul_mem _ hr₁ hr₂
  have hg₁ : GoodInv M r₁ := ⟨ho₁, (hRbad r₁ hr₁ ho₁).2.1⟩
  have hg₂ : GoodInv M r₂ := ⟨ho₂, (hRbad r₂ hr₂ ho₂).2.1⟩
  have hg₃ : GoodInv M (r₁ * r₂) := ⟨ho₃, (hRbad (r₁ * r₂) hr₃ ho₃).2.1⟩
  have hMu : UniversalF M := by
    by_cases hbM : b ∈ M
    · refine universalF_of_good_mem_center hLB hglaub hM ⟨hb.1, hS.isCompIn⟩ hbM ?_
      intro m hm
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hS.isCompIn.1 hm)).symm
    · have hbn : b ∉ cj a M := by
        intro h
        apply hbM
        have h2 : a * b * a = b := by
          rw [hab, mul_assoc, hS.x_mul_self, mul_one]
        rw [mem_cj_of_mul_self hS.x_mul_self, h2] at h
        exact h
      obtain ⟨w₁, w₂, _, _, _, _, _, _, Q, _, _, _, _, _, _, _, hQrank⟩ :=
        exists_swap_rank_three hS hMrank hbn
      exact universalF_of_fourGroup hLB hglaub hM hg₁ hg₂ hg₃ h12 hQrank
  exact not_universalF_of_swapConfig hstar hS hM hMrank hMu

end CFSG.EvenSporadicStandard.Induction.ThmU
