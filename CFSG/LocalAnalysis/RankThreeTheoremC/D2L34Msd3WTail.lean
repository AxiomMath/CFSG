module

public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
public import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3TailQuot
import CFSG.LocalAnalysis.RankThreeTheoremC.HasPrimeConstraintBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem exists_normal_order_three_le_of_tail3 {M C W D : Subgroup G}
    (hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥M)
    (hCn : (C.subgroupOf M).Normal)
    (hCsmall : ∀ E : Subgroup G, E ≤ C → IsPGroup 3 E → Nat.card E ≤ 9)
    (hWM : W ≤ M) (hWp : IsPGroup 3 W) (hWidx : ¬ 3 ∣ (W.subgroupOf M).index)
    (hDW : D ≤ W) (hDC : D ≤ C) (hD9 : Nat.card D = 9)
    (hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hD3 : ∀ d ∈ D, d ^ 3 = 1)
    (hR : ∀ a ∈ W ⊓ Subgroup.centralizer (D : Set G), ∀ b ∈ W ⊓ Subgroup.centralizer (D : Set G),
      a * b = b * a)
    (hA : ∃ A : Subgroup G, A ≤ W ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a ^ 3 = 1) ∧
      Nat.card A = 27)
    (hmax : ∀ A : Subgroup G, A ≤ W → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ a ∈ A, a ^ 3 = 1) → Nat.card A ≤ 27)
    {s : G} (hsM : s ∈ M) (hsD : ∀ d ∈ D, s * d * s⁻¹ ∈ D)
    (hs2 : ∀ d ∈ D, s ^ 2 * d * (s ^ 2)⁻¹ = d⁻¹) :
    ∃ P₀ : Subgroup G, P₀ ≤ W ∧ Nat.card P₀ = 3 ∧
      ((P₀ ⊔ GLBPrimeCore 3 M).subgroupOf M).Normal := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDM : D ≤ M := hDW.trans hWM
  have hY := hasPrimeConstraint_of_isPConstrained hcon
  have hW'p : IsPGroup 3 (W.subgroupOf M) :=
    hWp.of_equiv (Subgroup.subgroupOfEquivOfLe hWM).symm
  have hCsmall' : ∀ E : Subgroup ↥M, E ≤ C.subgroupOf M → IsPGroup 3 E → Nat.card E ≤ 9 := by
    intro E hEC hEp
    have h1 : E.map M.subtype ≤ C := by
      rintro _ ⟨e, he, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hEC he)
    have h2 := hCsmall _ h1 (hEp.map M.subtype)
    rwa [Subgroup.card_map_of_injective M.subtype_injective] at h2
  have hDW' : D.subgroupOf M ≤ W.subgroupOf M := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hDW (Subgroup.mem_subgroupOf.1 hx))
  have hDC' : D.subgroupOf M ≤ C.subgroupOf M := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hDC (Subgroup.mem_subgroupOf.1 hx))
  have hD9' : Nat.card (D.subgroupOf M) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDM).toEquiv, hD9]
  have hDab' : ∀ a ∈ D.subgroupOf M, ∀ b ∈ D.subgroupOf M, a * b = b * a := fun a ha b hb =>
    Subtype.ext (hDab _ (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hb))
  have hD3' : ∀ d ∈ D.subgroupOf M, d ^ 3 = 1 := fun d hd =>
    Subtype.ext (by simpa using hD3 _ (Subgroup.mem_subgroupOf.1 hd))
  have hR' : ∀ a ∈ W.subgroupOf M ⊓ Subgroup.centralizer ((D.subgroupOf M : Subgroup ↥M) :
      Set ↥M), ∀ b ∈ W.subgroupOf M ⊓ Subgroup.centralizer ((D.subgroupOf M : Subgroup ↥M) :
      Set ↥M), a * b = b * a := by
    have hcent : ∀ a ∈ W.subgroupOf M ⊓ Subgroup.centralizer ((D.subgroupOf M : Subgroup ↥M) :
        Set ↥M), (a : G) ∈ W ⊓ Subgroup.centralizer (D : Set G) := by
      intro a ha
      refine ⟨Subgroup.mem_subgroupOf.1 ha.1, Subgroup.mem_centralizer_iff.2 fun d hd => ?_⟩
      have := Subgroup.mem_centralizer_iff.1 ha.2 ⟨d, hDM hd⟩ (Subgroup.mem_subgroupOf.2 hd)
      exact congrArg Subtype.val this
    intro a ha b hb
    exact Subtype.ext (hR _ (hcent a ha) _ (hcent b hb))
  obtain ⟨A, hAW, hAab, hA3, hA27⟩ := hA
  have hA' : ∃ A' : Subgroup ↥M, A' ≤ W.subgroupOf M ∧ (∀ a ∈ A', ∀ b ∈ A', a * b = b * a) ∧
      (∀ a ∈ A', a ^ 3 = 1) ∧ Nat.card A' = 27 := by
    refine ⟨A.subgroupOf M, fun x hx => Subgroup.mem_subgroupOf.2
      (hAW (Subgroup.mem_subgroupOf.1 hx)), fun a ha b hb =>
      Subtype.ext (hAab _ (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hb)),
      fun a ha => Subtype.ext (by simpa using hA3 _ (Subgroup.mem_subgroupOf.1 ha)), ?_⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hAW.trans hWM)).toEquiv, hA27]
  have hmax' : ∀ A' : Subgroup ↥M, A' ≤ W.subgroupOf M → (∀ a ∈ A', ∀ b ∈ A', a * b = b * a) →
      (∀ a ∈ A', a ^ 3 = 1) → Nat.card A' ≤ 27 := by
    intro A' hA'W hA'ab hA'3
    have h1 : A'.map M.subtype ≤ W := by
      rintro _ ⟨a, ha, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hA'W ha)
    have h2 := hmax _ h1 (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (hA'ab a ha b hb)) (by
      rintro _ ⟨a, ha, rfl⟩
      simpa using congrArg Subtype.val (hA'3 a ha))
    rwa [Subgroup.card_map_of_injective M.subtype_injective] at h2
  have hsD' : ∀ d ∈ D.subgroupOf M, (⟨s, hsM⟩ : ↥M) * d * (⟨s, hsM⟩ : ↥M)⁻¹ ∈ D.subgroupOf M :=
    fun d hd => Subgroup.mem_subgroupOf.2 (by
      simpa using hsD _ (Subgroup.mem_subgroupOf.1 hd))
  have hs2' : ∀ d ∈ D.subgroupOf M,
      (⟨s, hsM⟩ : ↥M) ^ 2 * d * ((⟨s, hsM⟩ : ↥M) ^ 2)⁻¹ = d⁻¹ := fun d hd =>
    Subtype.ext (by simpa using hs2 _ (Subgroup.mem_subgroupOf.1 hd))
  obtain ⟨P₀', hP₀'W, hP₀'3, hP₀'n⟩ := exists_normal_order_three_of_tail_in_group (Y := ↥M) hY
    hCn hCsmall' hW'p hWidx hDW' hDC' hD9' hDab' hD3' hR' hA' hmax' hsD' hs2'
  set P₀ : Subgroup G := P₀'.map M.subtype with hP₀
  have hP₀M : P₀ ≤ M := Subgroup.map_subtype_le _
  have hP₀sub : P₀.subgroupOf M = P₀' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective P₀'
  refine ⟨P₀, (Subgroup.map_le_iff_le_comap).2 hP₀'W,
    by rw [hP₀, Subgroup.card_map_of_injective M.subtype_injective, hP₀'3], ?_⟩
  rw [Subgroup.subgroupOf_sup hP₀M (glbPrimeCore_le 3 M), glbPrimeCore_subgroupOf 3 M, hP₀sub]
  exact hP₀'n

end CFSG.LocalAnalysis.RankThreeTheoremC
