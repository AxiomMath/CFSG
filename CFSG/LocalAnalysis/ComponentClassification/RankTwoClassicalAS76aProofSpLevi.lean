module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpSetup
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDefs
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviModel
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLinear
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBruhat
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

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups commutatorElement

section Levi

variable {K : Type} [Field K] {m : ℕ} {G : Type} [Group G] {A : Subgroup G}
  {θ : ↥A →* StatedProj (StatedSp (m + 1) K)}

variable (θ) in
@[expose] noncomputable def spLeviW : Subgroup G := levLift θ (spBarW K m)

variable (θ) in
@[expose] noncomputable def spLeviL : Subgroup G := levLift θ (spBarL K m)

variable [CharP K 2] (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ)
  (h4 : ∃ s : Finset K, s.card = 4)
include hker hθ h4

theorem layerCentralizer_eq_spLeviL (hm : 1 ≤ m) {Y : Subgroup G} (hWY : spLeviW θ ≤ Y)
    (hLY : spLeviL θ ≤ A ⊓ centralizer (Y : Set G)) :
    AS76b.layerCentralizer A Y = spLeviL θ := by
  have himg : ∀ m' ∈ A ⊓ centralizer (Y : Set G), ∀ hm' : m' ∈ A,
      θ ⟨m', hm'⟩ ∈ spBarL K m := by
    intro m' hmM hm'
    refine mem_spBarL_of_commute fun w hw => ?_
    obtain ⟨w', hw', rfl⟩ := exists_mem_levLift hθ (commutator_spBarW h4) hw
    have hc : m' * w' = w' * m' :=
      (mem_centralizer_iff.mp (mem_inf.mp hmM).2 w' (hWY hw')).symm
    rw [← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext hc)
  exact layerCentralizer_eq_levLift hker hθ (commutator_spBarL h4) (isQuasisimple_spBarL hm h4)
    hLY (fun m' hmM hm' => le_normalizer (himg m' hmM hm'))
    (fun a ha b hb haA hbA => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem (himg a ha haA) (himg b hb hbA))
        (inv_mem (himg a ha haA))) (inv_mem (himg b hb hbA)))

@[expose] noncomputable def spLeviLQuotEquiv :
    rankTwoQuot (spLeviL θ) ≃* StatedSp m K ⧸ center (StatedSp m K) :=
  (levLiftQuotEquiv hker hθ (commutator_spBarL h4)).trans
    (QuotientGroup.congr (center (spBarL K m)) (center (StatedSp m K))
      (spBarLEquiv K m).symm (Subgroup.map_center_eq _))

theorem statedClassicalModel_spLeviL [Finite K] {f : ℕ} (hm : 2 ≤ m) (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) : StatedClassicalModel (rankTwoQuot (spLeviL θ)) .PSp m 2 f := by
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine ⟨⟨Nat.prime_two, by omega, hm, fun h => ?_⟩, K, inferInstance, inferInstance, hK,
    ⟨(spLeviLQuotEquiv hker hθ h4).trans
      (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv m K)⟩⟩
  simp only [Prod.mk.injEq] at h
  omega

theorem statedClassicalModel_spLeviL_one [Finite K] {f : ℕ} (hm : m = 1) (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) : StatedClassicalModel (rankTwoQuot (spLeviL θ)) .PSL 2 2 f := by
  subst hm
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, fun h => ?_, fun h => ?_⟩, K, inferInstance,
    inferInstance, hK, ⟨((spLeviLQuotEquiv hker hθ h4).trans
      (QuotientGroup.congr (center (StatedSp 1 K)) (center SL(2, K)) (longBlockEquivOne K).symm
        (Subgroup.map_center_eq _))).trans (projectiveSpecialLinearGroupEquivStatedProj 2 K)⟩⟩
  · simp only [Prod.mk.injEq] at h
    omega
  · simp only [Prod.mk.injEq] at h
    omega

theorem open_isQuasisimple_spLeviL (hm : 1 ≤ m) : CFSG.Open.IsQuasisimple ↥(spLeviL θ) := by
  obtain ⟨hp, hs, -⟩ := isQuasisimple_levLift hker hθ (commutator_spBarL h4)
    (isQuasisimple_spBarL hm h4)
  exact ⟨hp.commutator_eq_top, hs⟩

omit h4 in
theorem odd_card_center_spLeviL [Finite G] (hZ : Odd (Nat.card (center ↥A))) (hm : 1 ≤ m)
    (h4 : ∃ s : Finset K, s.card = 4) : Odd (Nat.card (center ↥(spLeviL θ))) :=
  odd_card_center_levLift hker hθ (commutator_spBarL h4) hZ
    (by rw [card_center_spBarL hm]; exact odd_one)

end Levi

section Choice

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem leviChoice_symplectic_of {m f : ℕ} (hn : 2 ≤ m + 1) (hf : 1 ≤ f)
    (hnm : (m + 1, 2 ^ f) ≠ (2, 2)) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (e : rankTwoQuot A ≃* StatedProj (StatedSp (m + 1) K))
    (hZ : Odd (Nat.card (center ↥A))) (hf2 : 2 ≤ f) {p : G}
    {θ : ↥A →* StatedProj (StatedSp (m + 1) K)} (hker : θ.ker = center ↥A)
    (hθ : Function.Surjective θ)
    (hα : ∀ y ∈ {y : G | (∃ j : ℕ, y ^ 2 ^ j = 1) ∧ ∃ M N : GL (Fin (m + 1) ⊕ Fin (m + 1)) K,
        Represents e p M ∧ orderOf M = 2 ∧ Represents e y N ∧ ∃ a : K,
          (N : Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) K) - 1 =
            a • ((M : Matrix _ _ K) - 1)},
        y ∈ liftSub θ (spBarL K m) ∧ ∃ j : ℕ, y ^ 2 ^ j = 1)
    {Y : Subgroup G} (hWY : spLeviW θ ≤ Y)
    (hYc : Y ≤ liftSub θ (centralizer (spBarL K m : Set (StatedProj (StatedSp (m + 1) K)))))
    (hnoInv : NoInvolutoryCentralizing A (Y ⊔ spLeviL θ))
    (houter : (ClassicalModel.symplectic (m + 1) f hn hf hnm K hK e).IsLTwoFour →
      ∀ σ : MulAut ↥A, σ * σ = 1 → (∀ y : ↥A, (y : G) ∈ Y → σ y = y) →
        ∃ l ∈ spLeviL θ, ∀ z : ↥A, (z : G) ∈ spLeviL θ → ((σ z : ↥A) : G) = l * z * l⁻¹)
    (hsym : (ClassicalModel.symplectic (m + 1) f hn hf hnm K hK e).IsLTwoFour →
      ∃ (D' : Subgroup G) (s x : G), Y = D' ⊔ spLeviW θ ∧ s ∈ A ∧
        AschbacherTightEmbedding.rightConjugate (spLeviW θ) s = spLeviL θ ∧
        AschbacherTightEmbedding.rightConjugate (spLeviL θ) s = spLeviW θ ∧
        AschbacherTightEmbedding.rightConjugate D' s = D' ∧
        x ∈ spLeviL θ ∧ orderOf x = 5 ∧
        AS76b.layerCentralizer A (D' ⊔ zpowers x) = spLeviW θ ∧
        NoInvolutoryCentralizing A (D' ⊔ zpowers x ⊔ spLeviW θ)) :
    LeviChoice (ClassicalModel.symplectic (m + 1) f hn hf hnm K hK e) p (spLeviW θ) Y := by
  have hm : 1 ≤ m := by omega
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
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2)
    exact ⟨s, hs⟩
  have hYθ : ∀ x ∈ Y, ∃ hx : x ∈ A, ∀ l ∈ spBarL K m, θ ⟨x, hx⟩ * l = l * θ ⟨x, hx⟩ := by
    intro x hx
    obtain ⟨hxA, hxθ⟩ := mem_liftSub.mp (hYc hx)
    exact ⟨hxA, fun l hl => (mem_centralizer_iff.mp hxθ l hl).symm⟩
  have hYA : Y ≤ A := fun x hx => (hYθ x hx).1
  have hLY : spLeviL θ ≤ A ⊓ centralizer (Y : Set G) := by
    refine le_inf levLift_le ?_
    rw [le_centralizer_iff]
    intro y hy
    obtain ⟨hyA, hyθ⟩ := hYθ y hy
    have := levLift_le_centralizer hker hyA (S := spBarL K m) hyθ
    intro l hl
    exact mem_centralizer_singleton_iff.mp (this hl)
  have hlayer := layerCentralizer_eq_spLeviL hker hθ h4 hm hWY hLY
  have hαL : alphaGroup e p ≤ spLeviL θ :=
    closure_le_levLift hker hθ (commutator_spBarL h4) hZ hα
  refine
    { W_le := hWY
      Y_le := le_inf hYA (le_centralizer_closure_levLift hker hZ hα hYθ)
      W_type := ⟨K, inferInstance, inferInstance, hK,
        nonempty_levLift_equiv_SL2 hker hθ hZ hf2 hK (commutator_spBarW h4) (spBarWEquiv K m)⟩
      alpha_le := ?_
      quasisimple := ?_
      oddCenter := ?_
      levi := ?_
      noInv := ?_
      diag := fun h => h.elim
      outerFree := ?_
      sym := ?_ }
  · show alphaGroup e p ≤ _
    rw [hlayer]
    exact hαL
  · rw [hlayer]
    exact open_isQuasisimple_spLeviL hker hθ h4 hm
  · rw [hlayer]
    exact odd_card_center_spLeviL hker hθ hZ hm h4
  · show (3 ≤ m + 1 ∧ StatedClassicalModel (rankTwoQuot _) .PSp (m + 1 - 1) 2 f) ∨
      (m + 1 = 2 ∧ StatedClassicalModel (rankTwoQuot _) .PSL 2 2 f)
    rw [hlayer, Nat.add_sub_cancel]
    rcases (show m = 1 ∨ 2 ≤ m by omega) with h1 | h2
    · exact Or.inr ⟨by omega, statedClassicalModel_spLeviL_one hker hθ h4 h1 hf2 hK⟩
    · exact Or.inl ⟨by omega, statedClassicalModel_spLeviL hker hθ h4 h2 hf2 hK⟩
  · rw [hlayer]
    exact hnoInv
  · rw [hlayer]
    exact houter
  · rw [hlayer]
    exact hsym

end Choice

end CFSG.ComponentClassification.RankTwoClassical
