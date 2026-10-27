module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviSetup
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDefs
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviFields
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviModel
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLinear
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard

theorem leviChoice_linear_of {G : Type} [Group G] [Finite G] {A : Subgroup G} {k m : ℕ}
    (hn : 4 ≤ 2 + k) (hm : 1 ≤ m) (hnm : (2 + k, m) ≠ (4, 1)) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ m) (e : rankTwoQuot A ≃* StatedProj (StatedSL (2 + k) K))
    (hZ : Odd (Nat.card (center ↥A))) (hm2 : 2 ≤ m) {p : G}
    {θ : ↥A →* projectiveSL (2 + k) K} (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ)
    (hα : ∀ y ∈ {y : G | (∃ j : ℕ, y ^ 2 ^ j = 1) ∧ ∃ M N : GL (Fin (2 + k)) K,
        Represents e p M ∧ orderOf M = 2 ∧ Represents e y N ∧ ∃ a : K,
          (N : Matrix (Fin (2 + k)) (Fin (2 + k)) K) - 1 = a • ((M : Matrix _ _ K) - 1)},
        y ∈ liftSub θ (barL K k) ∧ ∃ j : ℕ, y ^ 2 ^ j = 1)
    {Y : Subgroup G} (hWY : leviW θ ≤ Y)
    (hYc : Y ≤ liftSub θ (centralizer (barL K k : Set (projectiveSL (2 + k) K))))
    (hnoInv : NoInvolutoryCentralizing A (Y ⊔ leviL θ))
    (hdiag : (ClassicalModel.linear (2 + k) m hn hm hnm K hK e).IsLinearFiveFour →
      ∃ y ∈ A ⊓ centralizer (Y : Set G), (∃ j : ℕ, y ^ 3 ^ j = 1) ∧
        ¬ ∃ l ∈ leviL θ, ∀ x ∈ leviL θ,
          y * x * y⁻¹ * (l * x * l⁻¹)⁻¹ ∈ (center ↥(leviL θ)).map (leviL θ).subtype)
    (houter : (ClassicalModel.linear (2 + k) m hn hm hnm K hK e).IsLTwoFour →
      ∀ σ : MulAut ↥A, σ * σ = 1 → (∀ y : ↥A, (y : G) ∈ Y → σ y = y) →
        ∃ l ∈ leviL θ, ∀ z : ↥A, (z : G) ∈ leviL θ → ((σ z : ↥A) : G) = l * z * l⁻¹)
    (hsym : (ClassicalModel.linear (2 + k) m hn hm hnm K hK e).IsLTwoFour →
      ∃ (D' : Subgroup G) (s x : G), Y = D' ⊔ leviW θ ∧ s ∈ A ∧
        AschbacherTightEmbedding.rightConjugate (leviW θ) s = leviL θ ∧
        AschbacherTightEmbedding.rightConjugate (leviL θ) s = leviW θ ∧
        AschbacherTightEmbedding.rightConjugate D' s = D' ∧
        x ∈ leviL θ ∧ orderOf x = 5 ∧
        AS76b.layerCentralizer A (D' ⊔ zpowers x) = leviW θ ∧
        NoInvolutoryCentralizing A (D' ⊔ zpowers x ⊔ leviW θ)) :
    LeviChoice (ClassicalModel.linear (2 + k) m hn hm hnm K hK e) p (leviW θ) Y := by
  have hk : 2 ≤ k := by omega
  have : CharP K 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have h4 : ∃ s : Finset K, s.card = 4 := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
      (by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2)
    exact ⟨s, hs⟩
  have hYθ : ∀ x ∈ Y, ∃ hx : x ∈ A, ∀ l ∈ barL K k, θ ⟨x, hx⟩ * l = l * θ ⟨x, hx⟩ := by
    intro x hx
    obtain ⟨hxA, hxθ⟩ := mem_liftSub.mp (hYc hx)
    exact ⟨hxA, fun l hl => (mem_centralizer_iff.mp hxθ l hl).symm⟩
  have hYA : Y ≤ A := fun x hx => (hYθ x hx).1
  have hLY : leviL θ ≤ A ⊓ centralizer (Y : Set G) := by
    refine le_inf levLift_le ?_
    rw [le_centralizer_iff]
    intro y hy
    obtain ⟨hyA, hyθ⟩ := hYθ y hy
    have := levLift_le_centralizer hker hyA (S := barL K k) hyθ
    intro l hl
    exact (mem_centralizer_singleton_iff.mp (this hl))
  have hlayer := layerCentralizer_eq_leviL hker hθ h4 hk hWY hLY
  have hαL : alphaGroup e p ≤ leviL θ := closure_le_leviL hker hθ h4 hk hZ hα
  refine
    { W_le := hWY
      Y_le := le_inf hYA (le_centralizer_closure hker hZ hα hYθ)
      W_type := ⟨K, inferInstance, inferInstance, hK,
        nonempty_leviW_equiv hker hθ hZ hm2 hK (by omega)⟩
      alpha_le := ?_
      quasisimple := ?_
      oddCenter := ?_
      levi := ?_
      noInv := ?_
      diag := ?_
      outerFree := ?_
      sym := ?_ }
  · show alphaGroup e p ≤ _
    rw [hlayer]
    exact hαL
  · rw [hlayer]
    exact open_isQuasisimple_leviL hker hθ h4 hk
  · rw [hlayer]
    exact odd_card_center_leviL hker hθ hk hZ hm hK h4
  · show StatedClassicalModel _ .PSL (2 + k - 2) 2 m
    rw [hlayer, Nat.add_sub_cancel_left]
    exact statedClassicalModel_leviL hker hθ hk hm2 hK h4
  · rw [hlayer]
    exact hnoInv
  · rw [hlayer]
    exact hdiag
  · rw [hlayer]
    exact houter
  · rw [hlayer]
    exact hsym

end CFSG.ComponentClassification.RankTwoClassical
