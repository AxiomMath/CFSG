module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUSetup
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDefs
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviModel
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUTypes
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

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups commutatorElement

section Levi

variable {K : Type} [Field K] {k f : ℕ} {G : Type} [Group G] {A : Subgroup G}
  {θ : ↥A →* StatedProj (StatedSU (2 + k) (2 ^ f) K)}

variable (θ) in
@[expose] noncomputable def uLeviW : Subgroup G := levLift θ (uBarW K k f)

variable (θ) in
@[expose] noncomputable def uLeviL : Subgroup G := levLift θ (uBarL K k f)

variable [Finite K] [CharP K 2] (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ)
  (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f)
include hker hθ hK hf

theorem layerCentralizer_eq_uLeviL (hk : 2 ≤ k) {Y : Subgroup G} (hWY : uLeviW θ ≤ Y)
    (hLY : uLeviL θ ≤ A ⊓ centralizer (Y : Set G)) :
    AS76b.layerCentralizer A Y = uLeviL θ := by
  have h := unitaryFieldData_of_card hK (by omega)
  obtain ⟨ζ, hζ, hζ1⟩ := exists_norm_one_ne_one hK
  have hcommW : ∀ m ∈ A ⊓ centralizer (Y : Set G), ∀ hm : m ∈ A, ∀ w ∈ uBarW K k f,
      θ ⟨m, hm⟩ * w = w * θ ⟨m, hm⟩ := by
    intro m hmM hm w hw
    obtain ⟨w', hw', rfl⟩ := exists_mem_levLift hθ (commutator_uBarW hK hf) hw
    have hc : m * w' = w' * m :=
      (mem_centralizer_iff.mp (mem_inf.mp hmM).2 w' (hWY hw')).symm
    rw [← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext hc)
  refine layerCentralizer_eq_levLift hker hθ (commutator_uBarL hK hf hk)
    (isQuasisimple_uBarL hK hf hk) hLY ?_ ?_
  · intro m hmM hm
    obtain ⟨g, hg, _, _, hgD⟩ :=
      exists_blk_of_commute_uBarW (by omega) hζ hζ1 (hcommW m hmM hm)
    rw [← hg]
    exact uProj_mem_normalizer_uBarL h hgD
  · intro a ha b hb haA hbA
    obtain ⟨g, hg, c, D, hgD⟩ := exists_blk_of_commute_uBarW (by omega) hζ hζ1 (hcommW a ha haA)
    obtain ⟨g', hg', c', D', hgD'⟩ :=
      exists_blk_of_commute_uBarW (by omega) hζ hζ1 (hcommW b hb hbA)
    rw [← hg, ← hg', ← map_commutatorElement]
    obtain ⟨S, hS⟩ := commutatorElement_mem_range_uL h hgD hgD'
      (by rw [smul_one_mul_smul_one, smul_one_mul_smul_one, mul_comm])
    exact ⟨S, by simp only [MonoidHom.comp_apply]; rw [hS]⟩

@[expose] noncomputable def uLeviLQuotEquiv (hk : 2 ≤ k) :
    rankTwoQuot (uLeviL θ) ≃* StatedSU k (2 ^ f) K ⧸ center (StatedSU k (2 ^ f) K) :=
  (levLiftQuotEquiv hker hθ (commutator_uBarL hK hf hk)).trans
    (QuotientGroup.congr (center (uBarL K k f)) (center (StatedSU k (2 ^ f) K))
      (uBarLEquiv K k f).symm (Subgroup.map_center_eq _))

theorem statedClassicalModel_uLeviL (hk : 3 ≤ k) :
    StatedClassicalModel (rankTwoQuot (uLeviL θ)) .PSU k 2 f :=
  ⟨⟨Nat.prime_two, by omega, hk, ne_three_two_of_two_le hf⟩, K, inferInstance, inferInstance, hK,
    ⟨(uLeviLQuotEquiv hker hθ hK hf (by omega)).trans (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK hk
        (ne_three_two_of_two_le hf)).2)⟩⟩

theorem statedClassicalModel_uLeviL_two (hk : k = 2) :
    StatedClassicalModel (rankTwoQuot (uLeviL θ)) .PSL 2 2 f := by
  subst hk
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨e₂⟩ := nonempty_SL2_equiv_statedSU_two hK
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, fun h => ?_, fun h => ?_⟩,
    CFSG.LieType.Steinberg.fixedSubfield K 2 f, inferInstance, inferInstance,
    CFSG.LieType.Steinberg.card_fixedSubfield hK,
    ⟨((uLeviLQuotEquiv hker hθ hK hf le_rfl).trans
      (QuotientGroup.congr (center (StatedSU 2 (2 ^ f) K)) (center SL(2, _)) e₂.symm
        (Subgroup.map_center_eq _))).trans (projectiveSpecialLinearGroupEquivStatedProj 2 _)⟩⟩
  · simp only [Prod.mk.injEq] at h
    omega
  · simp only [Prod.mk.injEq] at h
    omega

theorem open_isQuasisimple_uLeviL (hk : 2 ≤ k) : CFSG.Open.IsQuasisimple ↥(uLeviL θ) := by
  obtain ⟨hp, hs, -⟩ := isQuasisimple_levLift hker hθ (commutator_uBarL hK hf hk)
    (isQuasisimple_uBarL hK hf hk)
  exact ⟨hp.commutator_eq_top, hs⟩

theorem odd_card_center_uLeviL [Finite G] (hZ : Odd (Nat.card (center ↥A))) (hk : 2 ≤ k) :
    Odd (Nat.card (center ↥(uLeviL θ))) :=
  odd_card_center_levLift hker hθ (commutator_uBarL hK hf hk) hZ (odd_card_center_uBarL hK hf hk)

end Levi

section Choice

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem leviChoice_unitary_of {k f : ℕ} (hn : 4 ≤ 2 + k) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2)
    (e : rankTwoQuot A ≃* StatedProj (StatedSU (2 + k) (2 ^ f) K))
    (hZ : Odd (Nat.card (center ↥A))) (hf2 : 2 ≤ f) {p : G}
    {θ : ↥A →* StatedProj (StatedSU (2 + k) (2 ^ f) K)} (hker : θ.ker = center ↥A)
    (hθ : Function.Surjective θ)
    (hα : ∀ y ∈ {y : G | (∃ j : ℕ, y ^ 2 ^ j = 1) ∧ ∃ M N : GL (Fin (2 + k)) K,
        Represents e p M ∧ orderOf M = 2 ∧ Represents e y N ∧ ∃ a : K,
          (N : Matrix (Fin (2 + k)) (Fin (2 + k)) K) - 1 = a • ((M : Matrix _ _ K) - 1)},
        y ∈ liftSub θ (uBarL K k f) ∧ ∃ j : ℕ, y ^ 2 ^ j = 1)
    {Y : Subgroup G} (hWY : uLeviW θ ≤ Y)
    (hYc : Y ≤ liftSub θ (centralizer (uBarL K k f : Set (StatedProj
      (StatedSU (2 + k) (2 ^ f) K)))))
    (hnoInv : NoInvolutoryCentralizing A (Y ⊔ uLeviL θ))
    (houter : (ClassicalModel.unitary (2 + k) f hn hf K hK e).IsLTwoFour →
      ∀ σ : MulAut ↥A, σ * σ = 1 → (∀ y : ↥A, (y : G) ∈ Y → σ y = y) →
        ∃ l ∈ uLeviL θ, ∀ z : ↥A, (z : G) ∈ uLeviL θ → ((σ z : ↥A) : G) = l * z * l⁻¹)
    (hsym : (ClassicalModel.unitary (2 + k) f hn hf K hK e).IsLTwoFour →
      ∃ (D' : Subgroup G) (s x : G), Y = D' ⊔ uLeviW θ ∧ s ∈ A ∧
        AschbacherTightEmbedding.rightConjugate (uLeviW θ) s = uLeviL θ ∧
        AschbacherTightEmbedding.rightConjugate (uLeviL θ) s = uLeviW θ ∧
        AschbacherTightEmbedding.rightConjugate D' s = D' ∧
        x ∈ uLeviL θ ∧ orderOf x = 5 ∧
        AS76b.layerCentralizer A (D' ⊔ zpowers x) = uLeviW θ ∧
        NoInvolutoryCentralizing A (D' ⊔ zpowers x ⊔ uLeviW θ)) :
    LeviChoice (ClassicalModel.unitary (2 + k) f hn hf K hK e) p (uLeviW θ) Y := by
  have hk : 2 ≤ k := by omega
  have : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hK
  have hYθ : ∀ x ∈ Y, ∃ hx : x ∈ A, ∀ l ∈ uBarL K k f, θ ⟨x, hx⟩ * l = l * θ ⟨x, hx⟩ := by
    intro x hx
    obtain ⟨hxA, hxθ⟩ := mem_liftSub.mp (hYc hx)
    exact ⟨hxA, fun l hl => (mem_centralizer_iff.mp hxθ l hl).symm⟩
  have hYA : Y ≤ A := fun x hx => (hYθ x hx).1
  have hLY : uLeviL θ ≤ A ⊓ centralizer (Y : Set G) := by
    refine le_inf levLift_le ?_
    rw [le_centralizer_iff]
    intro y hy
    obtain ⟨hyA, hyθ⟩ := hYθ y hy
    have := levLift_le_centralizer hker hyA (S := uBarL K k f) hyθ
    intro l hl
    exact mem_centralizer_singleton_iff.mp (this hl)
  have hlayer := layerCentralizer_eq_uLeviL hker hθ hK hf2 hk hWY hLY
  have hαL : alphaGroup e p ≤ uLeviL θ :=
    closure_le_levLift hker hθ (commutator_uBarL hK hf2 hk) hZ hα
  obtain ⟨e₂⟩ := nonempty_SL2_equiv_statedSU_two hK
  refine
    { W_le := hWY
      Y_le := le_inf hYA (le_centralizer_closure_levLift hker hZ hα hYθ)
      W_type := ⟨CFSG.LieType.Steinberg.fixedSubfield K 2 f, inferInstance, inferInstance,
        CFSG.LieType.Steinberg.card_fixedSubfield hK,
        nonempty_levLift_equiv_SL2 hker hθ hZ hf2 (CFSG.LieType.Steinberg.card_fixedSubfield hK)
          (commutator_uBarW hK hf2) (e₂.trans (uBarWEquiv K k f (by omega)))⟩
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
    exact open_isQuasisimple_uLeviL hker hθ hK hf2 hk
  · rw [hlayer]
    exact odd_card_center_uLeviL hker hθ hK hf2 hZ hk
  · show (5 ≤ 2 + k ∧ StatedClassicalModel (rankTwoQuot _) .PSU (2 + k - 2) 2 f) ∨
      (2 + k = 4 ∧ StatedClassicalModel (rankTwoQuot _) .PSL 2 2 f)
    rw [hlayer, Nat.add_sub_cancel_left]
    rcases (show k = 2 ∨ 3 ≤ k by omega) with h2 | h3
    · exact Or.inr ⟨by omega, statedClassicalModel_uLeviL_two hker hθ hK hf2 h2⟩
    · exact Or.inl ⟨by omega, statedClassicalModel_uLeviL hker hθ hK hf2 h3⟩
  · rw [hlayer]
    exact hnoInv
  · rw [hlayer]
    exact houter
  · rw [hlayer]
    exact hsym

end Choice

end CFSG.ComponentClassification.RankTwoClassical
