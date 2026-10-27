module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTwoComp
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.GH74.GLS.Basic
public import CFSG.Open.GriessSchurMultipliersMilestoneDefs
public import CFSG.GroupTheory.NonabelianSimpleOrderSixty
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma45c
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup Assembly.LowTwoRank
open scoped MatrixGroups

@[expose] def IsSolvableTwoComponentIn {G : Type*} [Group G] (L A : Subgroup G) : Prop :=
  L ≤ A ∧ (L.subgroupOf A).IsSubnormal ∧
    (pPrimeCore 2 ↥L).map L.subtype = (pPrimeCore 2 ↥A).map A.subtype ∧
    (Nonempty (↥L ⧸ pPrimeCore 2 ↥L ≃* PSL(2, ZMod 3)) ∨
      Nonempty (↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, ZMod 3)))

@[expose] def IsSimpleChevalleyOver (p : ℕ) (Y : Type) [Group Y] : Prop :=
  ∃ (τ : StatedLieTag) (n f : ℕ), Blueprint.LieModel Y τ n p f

@[expose] def IsChevalleyOver (p : ℕ) (Y : Type) [Group Y] : Prop :=
  (IsQuasisimple Y ∧ IsSimpleChevalleyOver p (Y ⧸ center Y)) ∨
    (p = 3 ∧ (Nonempty (Y ≃* SL(2, ZMod 3)) ∨ Nonempty (Y ≃* PSL(2, ZMod 3))))

@[expose] def IsMTypeSchur (p : ℕ) (H : Type) [Group H] : Prop :=
  (IsTwoQuasisimple H ∧ IsSimpleChevalleyOver p (H ⧸ Open.fusionZStar H) ∧
      Even (Nat.card ↥(Open.fusionZStar H)) ∧
      ∀ n r : ℕ, 0 < n → 0 < r →
        (Blueprint.LieModel (H ⧸ Open.fusionZStar H) .PSL (2 * n) p r ∨
          Blueprint.LieModel (H ⧸ Open.fusionZStar H) .PSU (2 * n) p r) →
        ordProj[2] (Nat.card ↥(Open.fusionZStar H)) =
          ordProj[2] (Nat.card (Open.griessHopfMultiplier (H ⧸ Open.fusionZStar H)))) ∨
    (p = 3 ∧ Nonempty (H ⧸ pPrimeCore 2 H ≃* SL(2, ZMod 3)))

@[expose] def Harris82Theorem1Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 G) →
    ∀ z : G, orderOf z = 2 → ∀ L : Subgroup G,
      (IsTwoComponentIn L (centralizer {z}) ∨ IsSolvableTwoComponentIn L (centralizer {z})) →
      z ∈ L → ∀ p : ℕ, p.Prime → p ≠ 2 → IsMTypeSchur p ↥L →
        IsChevalleyOver p (↥(GH74.GLS.oPrimeResidual 2 G) ⧸
            pPrimeCore 2 ↥(GH74.GLS.oPrimeResidual 2 G)) ∨
          Nonempty (G ⧸ pPrimeCore 2 G ≃* ↥Blueprint.NativeSporadic.M11)

theorem card_specialLinearGroup_two_zmod_three : Nat.card SL(2, ZMod 3) = 24 := by
  rw [Matrix.card_SL_field (𝔽 := ZMod 3) 2, ZMod.card, Fin.prod_univ_two]
  norm_num

section Simple

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem pPrimeCore_eq_bot_of_simple {z : G} (hz : orderOf z = 2) : pPrimeCore 2 G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 G) with h | h
  · exact h
  · exfalso
    have hdvd := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 G) (h ▸ mem_top z)
    rw [hz] at hdvd
    exact absurd hdvd (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card)

omit [Finite G] in
theorem oPrimeResidual_eq_top_of_simple {z : G} (hz : orderOf z = 2) :
    GH74.GLS.oPrimeResidual 2 G = ⊤ := by
  have hn : (GH74.GLS.oPrimeResidual 2 G).Normal := by
    refine ⟨fun n hn g => ?_⟩
    unfold GH74.GLS.oPrimeResidual at hn ⊢
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk⟩ := hx
      exact subset_closure ⟨k, by rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩
    | one => simp
    | mul x y _ _ hx hy =>
      rw [show g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) by group]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
      exact inv_mem hx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GH74.GLS.oPrimeResidual 2 G) with h | h
  · exfalso
    have hz2 : z ^ 2 = 1 := by
      have := pow_orderOf_eq_one z
      rwa [hz] at this
    have hz' : z ∈ GH74.GLS.oPrimeResidual 2 G := subset_closure ⟨1, by rw [pow_one]; exact hz2⟩
    rw [h, mem_bot] at hz'
    rw [hz', orderOf_one] at hz
    exact absurd hz (by norm_num)
  · exact h

@[expose] def oPrimeResidualEquivOfSimple {z : G} (hz : orderOf z = 2) :
    G ≃* ↥(GH74.GLS.oPrimeResidual 2 G) :=
  Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr (oPrimeResidual_eq_top_of_simple hz).symm)

theorem isTwoQuasisimple_oPrimeResidual_of_simple (hnonab : ∃ a b : G, a * b ≠ b * a) {z : G}
    (hz : orderOf z = 2) : IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 G) := by
  have hq := (LocalCores.isQuasisimple_of_isSimpleGroup hnonab).1
  refine isTwoQuasisimple_of_mulEquiv (oPrimeResidualEquivOfSimple hz) ⟨hq.1, ?_⟩
  exact LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq (pPrimeCore_eq_bot_of_simple hz).symm)) hq

theorem lieModel_or_m11_of_theorem1 (hnonab : ∃ a b : G, a * b ≠ b * a) {z : G}
    (hz : orderOf z = 2) {p : ℕ}
    (h : IsChevalleyOver p (↥(GH74.GLS.oPrimeResidual 2 G) ⧸
        pPrimeCore 2 ↥(GH74.GLS.oPrimeResidual 2 G)) ∨
      Nonempty (G ⧸ pPrimeCore 2 G ≃* ↥Blueprint.NativeSporadic.M11)) :
    (∃ (τ : StatedLieTag) (n k : ℕ), Blueprint.LieModel G τ n p k) ∨
      Nonempty (G ≃* ↥Blueprint.NativeSporadic.M11) := by
  set N := GH74.GLS.oPrimeResidual 2 G with hN
  have e₀ : G ≃* ↥N := oPrimeResidualEquivOfSimple hz
  have hO : pPrimeCore 2 ↥N = ⊥ := by
    rw [← pPrimeCore_map_iso 2 e₀, pPrimeCore_eq_bot_of_simple hz, Subgroup.map_bot]
  have e₁ : ↥N ⧸ pPrimeCore 2 ↥N ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans (QuotientGroup.quotientBot.trans e₀.symm)
  rcases h with (⟨-, τ, n, k, hm⟩ | ⟨-, hY⟩) | hM11
  · left
    have : IsSimpleGroup (↥N ⧸ pPrimeCore 2 ↥N) := e₁.isSimpleGroup
    have hnonab' : ∃ a b : ↥N ⧸ pPrimeCore 2 ↥N, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnonab
      exact ⟨e₁.symm a, e₁.symm b, fun hc => hab (by simpa using congrArg e₁ hc)⟩
    have hZ := (LocalCores.isQuasisimple_of_isSimpleGroup hnonab').2
    exact ⟨τ, n, k, GSThmB.OddQuot.lieModel_of_equiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e₁)) hm⟩
  · exfalso
    have h60 := GroupTheory.nonabelian_simple_order_at_least_sixty (G := G) inferInstance
      (by obtain ⟨a, b, hab⟩ := hnonab; exact ⟨a, b, hab⟩)
    have hcard : Nat.card G ≤ 24 := by
      rw [← Nat.card_congr e₁.toEquiv]
      rcases hY with hP | hP
      · obtain ⟨e⟩ := hP
        rw [Nat.card_congr e.toEquiv, card_specialLinearGroup_two_zmod_three]
      · obtain ⟨e⟩ := hP
        rw [Nat.card_congr e.toEquiv, ← card_specialLinearGroup_two_zmod_three]
        exact Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective)
    omega
  · right
    obtain ⟨e⟩ := hM11
    exact ⟨(QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq (pPrimeCore_eq_bot_of_simple hz).symm)).trans e⟩

theorem lieModel_or_m11_of_theorem1_intrinsic (hT1 : Harris82Theorem1Input)
    (hnonab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : orderOf z = 2) {L : Subgroup G}
    (hL : IsTwoComponentIn L (centralizer {z})) (hzL : z ∈ L) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hM : IsMTypeSchur p ↥L) :
    (∃ (τ : StatedLieTag) (n k : ℕ), Blueprint.LieModel G τ n p k) ∨
      Nonempty (G ≃* ↥Blueprint.NativeSporadic.M11) :=
  lieModel_or_m11_of_theorem1 hnonab hz
    (hT1 G (isTwoQuasisimple_oPrimeResidual_of_simple hnonab hz) z hz L (.inl hL) hzL p hp hp2 hM)

theorem not_isMTypeSchur_of_theorem1 (hT1 : Harris82Theorem1Input)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hcat : ¬ Blueprint.Catalog G) {z : G}
    (hz : orderOf z = 2) {L : Subgroup G} (hL : IsTwoComponentIn L (centralizer {z}))
    (hzL : z ∈ L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ IsMTypeSchur p ↥L := by
  intro hM
  rcases lieModel_or_m11_of_theorem1_intrinsic hT1 hnonab hz hL hzL hp hp2 hM with
    ⟨τ, n, k, hm⟩ | hM11
  · exact hcat (Blueprint.lieModel_catalog G τ n p k hm)
  · obtain ⟨e⟩ := hM11
    exact hcat (.inr (.inr (.inr (.inr ⟨.M11, ⟨e⟩⟩))))

end Simple

end CFSG.ComponentClassification.HarrisLit
