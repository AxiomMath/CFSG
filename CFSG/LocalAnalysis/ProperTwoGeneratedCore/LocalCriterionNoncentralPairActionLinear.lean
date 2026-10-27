module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNoncentralPairActionSetup
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFieldFixedRoot
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairStatements
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PerfectOddCoverLinear

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII CFSG.GorensteinWalter
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open CFSG.ProperTwoGeneratedCore.HighRankPair
open scoped MatrixGroups

universe u

theorem sl2_eq_upperUnipotent_of_sq {F : Type*} [Field F] [CharP F 2] (g : SL(2, F))
    (h10 : g.val 1 0 = 0) (hg : g * g = 1) : g = sl2UpperUnipotent (g.val 0 1) := by
  have hdet : g.val 0 0 * g.val 1 1 = 1 := by
    have h := g.property
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at h
    exact h
  have h00 : g.val 0 0 * g.val 0 0 = 1 := by
    have h := congrFun (congrFun (congrArg
      (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) hg) 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, h10] using h
  have hp : g.val 0 0 = 1 := by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have : (g.val 0 0 + 1) * (g.val 0 0 + 1) = 0 := by
      linear_combination h00 + (g.val 0 0 + 1) * h2
    exact CharTwo.add_eq_zero.mp (mul_self_eq_zero.mp this)
  have hs : g.val 1 1 = 1 := by rwa [hp, one_mul] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2UpperUnipotent, hp, hs, h10]

theorem sl2_lower_eq_zero_of_conj {F : Type*} [Field F] (A : SL(2, F)) (r : F)
    (h : A * sl2UpperUnipotent 1 * A⁻¹ = sl2UpperUnipotent r) : A.val 1 0 = 0 := by
  have h' : A * sl2UpperUnipotent 1 = sl2UpperUnipotent r * A := by
    rw [← h, inv_mul_cancel_right]
  have e := congrFun (congrFun (congrArg
    (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) h') 1) 1
  simp only [Matrix.SpecialLinearGroup.coe_mul] at e
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two] at e
  simp [sl2UpperUnipotent] at e
  linear_combination e

theorem map_sl2UpperUnipotent {F : Type*} [Field F] (σ : RingAut F) (c : F) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (sl2UpperUnipotent c) = sl2UpperUnipotent (σ c) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;> simp [sl2UpperUnipotent]

variable {G : Type u} [Group G]

theorem linear_square_field_action
    [Finite G] {L U : Subgroup G} [Group.IsPerfect L]
    (hcen : CFSG.oddCore L ≤ Subgroup.center L) (helem : IsElementaryAbelian 2 U) (hUL : U ≤ L)
    {f : ℕ} (hf : 2 ≤ f) (hUcard : Nat.card U = 2 ^ f)
    (E : L ⧸ CFSG.oddCore L ≃* PSL2BinaryMatrixGroup f)
    (hUB : ∀ x (hx : x ∈ U), E (QuotientGroup.mk ⟨x, hUL hx⟩) •
      psl2ProjectiveInfinity (BinaryGaloisField f) = psl2ProjectiveInfinity (BinaryGaloisField f))
    {v : G} (hv : v ∈ Subgroup.normalizer (L : Set G)) (hv2 : v * v = 1)
    (hvU : ∀ x ∈ U, v * x * v⁻¹ ∈ U) (hmove : ∃ x ∈ U, ¬ Commute v x) :
    ∃ a : ℕ, 1 ≤ a ∧ f = 2 * a ∧ FieldInvolutionOn L v a ∧ SubfieldCentralizer L v a ∧
      Nat.card (((U : Set G) \ {1}) ∩ (Subgroup.centralizer ({v} : Set G) : Set G) : Set G) =
        2 ^ a - 1 := by
  classical
  let k := BinaryGaloisField f
  have hk : Nat.card k = 2 ^ f := GaloisField.card 2 f (by omega)
  let η : L →* PSL2MatrixGroup k := E.toMonoidHom.comp (QuotientGroup.mk' (CFSG.oddCore L))
  have hη : Function.Surjective η := E.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = CFSG.oddCore L := by
    ext x
    simp [η]
  obtain ⟨-, e, he⟩ := CFSG.ShultStronglyClosedTI.PerfectOddCover.perfect_odd_cover_linear f hf hk
    η hη (hker ▸ hcen) (hker ▸ CFSG.ComponentClassification.OddCore.odd_card L)
  let φ₀ : L ≃* SL(2, k) := e.trans sl2EquivPSL2.symm
  have hφ₀ : ∀ l : L, psl2QuotientMap k (φ₀ l) = E (QuotientGroup.mk l) := by
    intro l
    change sl2EquivPSL2 (sl2EquivPSL2.symm (e l)) = _
    rw [MulEquiv.apply_symm_apply, he]
    rfl
  let cv := normalizerConj L hv
  let γ : MulAut SL(2, k) := φ₀.symm.trans (cv.trans φ₀)
  have hγ : ∀ l : L, γ (φ₀ l) = φ₀ (cv l) := fun l => by simp [γ]
  have hvv : v⁻¹ = v := inv_eq_of_mul_eq_one_left hv2
  have hcv2 : ∀ l, cv (cv l) = l := fun l => by
    ext
    simp [cv, mul_assoc, hvv, ← mul_assoc v v, hv2]
  have hγγ : ∀ g, γ (γ g) = g := fun g => by
    obtain ⟨l, rfl⟩ := φ₀.surjective g
    rw [hγ, hγ, hcv2]
  obtain ⟨a, ha⟩ := (gammaToMulAut_bijective (F := k)).2 γ
  have ha2 : a * a = 1 := by
    apply (gammaToMulAut_bijective (F := k)).1
    rw [map_mul, map_one, ha]
    ext g : 1
    exact hγγ g
  have hUφ : ∀ x (hx : x ∈ U),
      φ₀ ⟨x, hUL hx⟩ = sl2UpperUnipotent ((φ₀ ⟨x, hUL hx⟩).val 0 1) := by
    intro x hx
    apply sl2_eq_upperUnipotent_of_sq
    · have h := hUB x hx
      rw [← hφ₀, psl2QuotientMap_smul] at h
      exact (sl2_mem_stabilizer_infinity_iff _).mp h
    · have hx2 : (⟨x, hUL hx⟩ : L) * ⟨x, hUL hx⟩ = 1 := Subtype.ext (by
        simpa [sq] using CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) x hx)
      rw [← map_mul, hx2, map_one]
  let r : U → k := fun x => (φ₀ ⟨x, hUL x.2⟩).val 0 1
  have hr : ∀ x : U, φ₀ ⟨x, hUL x.2⟩ = sl2UpperUnipotent (r x) := fun x => hUφ x x.2
  have hr_inj : Function.Injective r := by
    intro x y hxy
    have h : φ₀ ⟨x, hUL x.2⟩ = φ₀ ⟨y, hUL y.2⟩ := by rw [hr, hr, hxy]
    exact Subtype.ext (congrArg (fun l : L => (l : G)) (φ₀.injective h))
  have hr_bij : Function.Bijective r :=
    (Nat.bijective_iff_injective_and_card r).mpr ⟨hr_inj, by rw [hUcard, hk]⟩
  obtain ⟨x₁, hx₁⟩ := hr_bij.2 1
  have hγ1 : a.left * sl2UpperUnipotent 1 * a.left⁻¹ =
      sl2UpperUnipotent (r ⟨v * x₁ * v⁻¹, hvU _ x₁.2⟩) := by
    have hσ1 : Matrix.SpecialLinearGroup.map a.right.toRingHom (sl2UpperUnipotent 1) =
        sl2UpperUnipotent 1 := by rw [map_sl2UpperUnipotent, map_one]
    rw [← hσ1, ← gammaToMulAut_apply, ha, ← hx₁, ← hr, hγ]
    exact hr ⟨v * x₁ * v⁻¹, hvU _ x₁.2⟩
  have hborel : a.left ∈ sl2Borel k :=
    (sl2_mem_stabilizer_infinity_iff a.left).mpr (sl2_lower_eq_zero_of_conj a.left _ hγ1)
  have hγU : ∀ c : k, γ (sl2UpperUnipotent c) =
      sl2UpperUnipotent (a.left.val 0 0 ^ 2 * a.right c) := by
    intro c
    rw [← ha, gammaToMulAut_apply, map_sl2UpperUnipotent, sl2Borel_conj_upperUnipotent hborel]
  have hσ2 : a.right ^ 2 = 1 := by
    have h := congrArg SemidirectProduct.right ha2
    rwa [SemidirectProduct.mul_right, SemidirectProduct.one_right, ← sq] at h
  have hU01 : ∀ c d : k, sl2UpperUnipotent c = sl2UpperUnipotent d → c = d := fun c d h => by
    simpa [sl2UpperUnipotent] using
      congrFun (congrFun (congrArg (fun g : SL(2, k) => (g : Matrix (Fin 2) (Fin 2) k)) h) 0) 1
  have hnorm : a.left.val 0 0 ^ 2 * a.right (a.left.val 0 0 ^ 2) = 1 := by
    have h := hγγ (sl2UpperUnipotent 1)
    rw [hγU, hγU, map_one, mul_one] at h
    exact hU01 _ _ h
  have hcomm_iff : ∀ x : U, Commute v x ↔ a.left.val 0 0 ^ 2 * a.right (r x) = r x := by
    intro x
    constructor
    · intro hc
      have hcl : cv ⟨x, hUL x.2⟩ = ⟨x, hUL x.2⟩ := Subtype.ext (by
        change v * x * v⁻¹ = x
        rw [hc.eq, mul_inv_cancel_right])
      have h := hγ ⟨x, hUL x.2⟩
      rw [hcl, hr, hγU] at h
      exact hU01 _ _ h
    · intro hfix
      have h : φ₀ (cv ⟨x, hUL x.2⟩) = φ₀ ⟨x, hUL x.2⟩ := by rw [← hγ, hr, hγU, hfix]
      have h' := congrArg Subtype.val (φ₀.injective h)
      change v * x * v⁻¹ = x at h'
      exact mul_inv_eq_iff_eq_mul.mp h'
  have hσ1 : a.right ≠ 1 := by
    intro hσ
    obtain ⟨x, hx, hxv⟩ := hmove
    apply hxv
    have hc0 : a.left.val 0 0 ^ 2 = 1 := by
      have hn : a.left.val 0 0 ^ 2 * a.left.val 0 0 ^ 2 = 1 := by
        rw [hσ] at hnorm
        exact hnorm
      have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
      have : (a.left.val 0 0 ^ 2 + 1) * (a.left.val 0 0 ^ 2 + 1) = 0 := by
        linear_combination hn + (a.left.val 0 0 ^ 2 + 1) * h2
      exact CharTwo.add_eq_zero.mp (mul_self_eq_zero.mp this)
    exact (hcomm_iff ⟨x, hx⟩).mpr (by rw [hc0, one_mul, hσ]; rfl)
  have houter : a ∉ linearKernel k := by
    rw [mem_linearKernel_iff]
    exact hσ1
  have hord : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha2) (by
    rintro rfl
    exact houter (linearKernel k).one_mem)
  obtain ⟨s, hs1, hfs, hfrob, hfixcard, x, hax, -⟩ :=
    original_outer_involution_field_conjugacy_and_centralizer (by omega : 1 ≤ f) hk a hord houter
  let φ : L ≃* SL(2, k) := φ₀.trans (MulAut.conj x⁻¹)
  have hgam : ∀ g, gammaToMulAut k a g = x * sl2FieldAction a.right (x⁻¹ * g * x) * x⁻¹ := by
    intro g
    conv_lhs => rw [hax]
    rw [map_mul, map_mul, map_inv, gammaToMulAut_inl, gammaToMulAut_inr]
    simp [MulAut.mul_apply, MulAut.conj_apply]
  have hφcv : ∀ l : L, φ (cv l) = sl2FieldAction a.right (φ l) := by
    intro l
    simp only [φ, MulEquiv.trans_apply]
    rw [← hγ, ← ha, hgam]
    simp [mul_assoc]
  have hFI : FieldInvolutionOn L v s := by
    refine ⟨k, inferInstance, by rw [hk, hfs], φ, fun l y hy i j => ?_⟩
    have hyl : y = cv l := Subtype.ext hy
    rw [hyl, hφcv, sl2FieldAction_apply, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, Matrix.map_apply]
    exact hfrob _
  have hrange : ∀ g : SL(2, k),
      g ∈ (Matrix.SpecialLinearGroup.map (fixedField a.right).subtype).range ↔
        sl2FieldAction a.right g = g := by
    intro g
    constructor
    · rintro ⟨B, rfl⟩
      ext i j
      simp only [sl2FieldAction_apply, Matrix.SpecialLinearGroup.map_apply_coe,
        RingHom.mapMatrix_apply, Matrix.map_apply]
      exact (mem_fixedField_iff a.right _).mp (B i j).2
    · intro hg
      have hentry (i j : Fin 2) : a.right (g i j) = g i j :=
        congrFun (congrFun (congrArg (fun g : SL(2, k) => (g : Matrix (Fin 2) (Fin 2) k)) hg) i) j
      let B : Matrix (Fin 2) (Fin 2) (fixedField a.right) :=
        fun i j => ⟨g i j, (mem_fixedField_iff a.right _).mpr (hentry i j)⟩
      have hBdet : B.det = 1 := by
        apply (fixedField a.right).subtype.injective
        rw [map_one, RingHom.map_det]
        exact g.2
      exact ⟨⟨B, hBdet⟩, by ext i j; rfl⟩
  have hfix_iff : ∀ l : L, (l : G) ∈ Subgroup.centralizer ({v} : Set G) ↔
      φ l ∈ (Matrix.SpecialLinearGroup.map (fixedField a.right).subtype).range := by
    intro l
    rw [hrange, ← hφcv, φ.injective.eq_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      apply Subtype.ext
      change v * l * v⁻¹ = l
      rw [← h, mul_inv_cancel_right]
    · intro h
      have h' := congrArg Subtype.val h
      change v * l * v⁻¹ = l at h'
      exact (mul_inv_eq_iff_eq_mul.mp h').symm
  have hSC : SubfieldCentralizer L v s := by
    refine ⟨fixedField a.right, inferInstance, hfixcard, ⟨?_⟩⟩
    have hmap : ((L ⊓ Subgroup.centralizer ({v} : Set G)).subgroupOf L).map φ.toMonoidHom =
        (Matrix.SpecialLinearGroup.map (fixedField a.right).subtype).range := by
      ext g
      constructor
      · rintro ⟨l, hl, rfl⟩
        exact (hfix_iff l).mp (Subgroup.mem_subgroupOf.mp hl).2
      · intro hg
        obtain ⟨l, rfl⟩ := φ.surjective g
        exact ⟨l, Subgroup.mem_subgroupOf.mpr ⟨l.2, (hfix_iff l).mpr hg⟩, rfl⟩
    exact (Subgroup.subgroupOfEquivOfLe inf_le_left).symm.trans
      ((Subgroup.equivMapOfInjective _ φ.toMonoidHom φ.injective).trans
        ((MulEquiv.subgroupCongr hmap).trans
          (MonoidHom.ofInjective (sl2_map_injective (fixedField a.right).subtype)).symm))
  obtain ⟨s', -, -, hfs', -, -, -, -, -, -, -, hcount⟩ :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator.original_scalar_involution_full_fixed_root_card
      (by omega : 1 ≤ f) hk a.right hσ2 hσ1 _ hnorm
  refine ⟨s, hs1, hfs, hFI, hSC, ?_⟩
  rw [show s = s' by omega, ← hcount]
  have hr1 : ∀ x : U, r x = 0 → (x : G) = 1 := by
    intro x hx
    have h : φ₀ ⟨x, hUL x.2⟩ = φ₀ 1 := by rw [hr, hx, sl2UpperUnipotent_zero, map_one]
    exact congrArg (fun l : L => (l : G)) (φ₀.injective h)
  apply Nat.card_congr
  refine Equiv.ofBijective (fun x => ⟨r ⟨x.1, x.2.1.1⟩,
    (hcomm_iff ⟨x.1, x.2.1.1⟩).mp
      (Subgroup.mem_centralizer_singleton_iff.mp x.2.2).symm,
    fun h0 => x.2.1.2 (hr1 _ h0)⟩) ⟨?_, ?_⟩
  · intro x y hxy
    have h := hr_inj (congrArg Subtype.val hxy)
    exact Subtype.ext (congrArg (fun w : U => (w : G)) h)
  · rintro ⟨c, hc, hc0⟩
    obtain ⟨x, rfl⟩ := hr_bij.2 c
    refine ⟨⟨x, ⟨x.2, fun h1 => hc0 ?_⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr ((hcomm_iff x).mpr hc).eq.symm⟩, rfl⟩
    have h : φ₀ ⟨x, hUL x.2⟩ = 1 := by
      rw [← map_one φ₀]
      congr 1
      exact Subtype.ext h1
    rw [hr, ← sl2UpperUnipotent_zero] at h
    exact hU01 _ _ h

end CFSG.ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction
