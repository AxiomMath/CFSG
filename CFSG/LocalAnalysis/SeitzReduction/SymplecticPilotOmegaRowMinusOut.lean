module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaGlobal
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaModel
public import CFSG.RankThree.PartOne.AUTSL.OmegaOut

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup QuadraticMap Matrix
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.PartOne.AUTSL (frobPair frobPair_right frobPair_pow_f
  frobPair_pow_f_eq_inclusion tailZero tailOne tailZero_ne_tailOne tailOne_ne_tailZero
  tailZero_ne_inl tailOne_ne_inl tailZero_ne_inr tailOne_ne_inr coordQuadMinus_apply'
  form_single_tailZero ne_zero_of_irreducible_tail reflMat reflMat_mulVec reflMat_mem_isometries
  mem_or_mul_reflMat_mem exists_frob_pow conjAct_inclusion_val)

theorem frobeniusEquiv_pow_ne_one {K : Type} [Field K] [Finite K] [CharP K 2] {f m : ℕ}
    (hK : Nat.card K = 2 ^ f) (hm0 : 0 < m) (hmf : m < f) : (frobeniusEquiv K 2) ^ m ≠ 1 := by
  classical
  intro h
  have := Fintype.ofFinite K
  have hx : ∀ x : K, x ^ 2 ^ m = x := fun x => by
    have h1 : ((frobeniusEquiv K 2) ^ m) x = x := congrArg (fun σ : K ≃+* K => σ x) h
    rw [CFSG.RankThree.PartOne.AUTSL.frobeniusEquiv_pow_apply] at h1
    exact h1
  have hp : 1 < 2 ^ m := Nat.one_lt_two_pow hm0.ne'
  apply FiniteField.X_pow_card_sub_X_ne_zero K hp
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Finset.univ
    (fun x _ => ?_) ?_
  · simp [hx x]
  · rw [FiniteField.X_pow_card_sub_X_natDegree_eq K hp, Finset.card_univ,
      ← Nat.card_eq_fintype_card, hK]
    exact Nat.pow_lt_pow_right (by norm_num) hmf

section FrobSymmetry

variable {K : Type} [Field K] (N : ℕ) (hN : 1 ≤ N) (b c : K)

theorem frobPair_pow_right [Finite K] [CharP K 2] (hb : b ≠ 0) (j : ℕ) :
    ((frobPair N hN b c hb) ^ j).val.right = (frobeniusEquiv K 2) ^ j := by
  change ((frobPair N hN b c hb).val ^ j).right = _
  exact map_pow SemidirectProduct.rightHom _ j

theorem coordQuadMinus_of_tail (v : Fin (2 * N) → K)
    (h1 : ∀ i, v (minusIndexEquiv N hN (.inl i)) = 0) :
    coordinateQuadMinus N K hN b c v = v (tailZero N hN) ^ 2 +
      b * v (tailZero N hN) * v (tailOne N hN) + c * v (tailOne N hN) ^ 2 := by
  rw [coordQuadMinus_apply']
  simp [h1]

theorem polar_single_tailZero [CharP K 2] (v : Fin (2 * N) → K) :
    polar (coordinateQuadMinus N K hN b c) (Pi.single (tailZero N hN) 1) v =
      b * v (tailOne N hN) := by
  have h1 : ∀ i : Fin (N - 1), (Pi.single (tailZero N hN) (1 : K) : Fin (2 * N) → K)
      (minusIndexEquiv N hN (.inl i)) = 0 := fun i =>
    Pi.single_eq_of_ne (tailZero_ne_inl N hN i) _
  have h2 : ∀ i : Fin (N - 1), (Pi.single (tailZero N hN) (1 : K) : Fin (2 * N) → K)
      (minusIndexEquiv N hN (.inr (.inl i))) = 0 := fun i =>
    Pi.single_eq_of_ne (tailZero_ne_inr N hN i) _
  have h3 : (Pi.single (tailZero N hN) (1 : K) : Fin (2 * N) → K) (tailOne N hN) = 0 :=
    Pi.single_eq_of_ne (tailOne_ne_tailZero N hN) _
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [QuadraticMap.polar, coordQuadMinus_apply', coordQuadMinus_apply', coordQuadMinus_apply']
  simp only [Pi.add_apply, h1, h2, h3, Pi.single_eq_same, zero_add, zero_mul,
    Finset.sum_const_zero]
  linear_combination (v (tailZero N hN)) * h22

theorem frobPair_pow_f_eq_symmetry [Finite K] [CharP K 2] (hb : b ≠ 0) {f : ℕ}
    (hf : Nat.card K = 2 ^ f) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hnd : (coordinateQuadMinus N K hN b c).polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * N) → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, coordinateQuadMinus N K hN b c x = 0) :
    (frobPair N hN b c hb) ^ f = matrixIsometryInclusion (coordinateQuadMinus N K hN b c)
      (symmetryIsometry (coordinateQuadMinus N K hN b c) (Pi.single (tailZero N hN) 1)) := by
  obtain ⟨p, hp0, -, hform⟩ := frobPair_pow_f N hN b c hb hf hirr
  obtain ⟨A, hA, -, hTA⟩ := frobPair_pow_f_eq_inclusion N hN b c hb hf hirr hnd hT
  have hAv : ∀ (v : Fin (2 * N) → K) (k : Fin (2 * N)), (A.val *ᵥ v) k =
      v k + if k = tailZero N hN then p * v (tailOne N hN) else 0 := by
    intro v k
    have h := hform v k
    rw [hTA] at h
    exact h
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hpb : p = b := by
    have h1 := (mem_matrixIsometries_iff _ A).1 hA (Pi.single (tailOne N hN) 1)
    change coordinateQuadMinus N K hN b c (A.val *ᵥ _) = _ at h1
    have hz : ∀ i : Fin (N - 1),
        (Pi.single (tailOne N hN) (1 : K) : Fin (2 * N) → K) (minusIndexEquiv N hN (.inl i)) = 0 :=
      fun i => Pi.single_eq_of_ne (tailOne_ne_inl N hN i) _
    have hz' : ∀ i : Fin (N - 1),
        (A.val *ᵥ (Pi.single (tailOne N hN) (1 : K))) (minusIndexEquiv N hN (.inl i)) = 0 := by
      intro i
      rw [hAv, hz, ite_eq_right (tailZero_ne_inl N hN i), add_zero]
    rw [coordQuadMinus_of_tail N hN b c _ hz', coordQuadMinus_of_tail N hN b c _ hz, hAv, hAv,
      ite_eq_left rfl, ite_eq_right (tailOne_ne_tailZero N hN), Pi.single_eq_same,
      Pi.single_eq_of_ne (tailZero_ne_tailOne N hN)] at h1
    have h2 : p * (p + b) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hp0
    · linear_combination h - b * h22
  have hw : coordinateQuadMinus N K hN b c (Pi.single (tailZero N hN) 1) = 1 :=
    form_single_tailZero N hN b c
  have hAeq : A = symmetryGL (coordinateQuadMinus N K hN b c) (Pi.single (tailZero N hN) 1) := by
    apply matrixLinearIso.injective
    refine LinearEquiv.ext fun v => ?_
    change A.val *ᵥ v = ((symmetryGL (coordinateQuadMinus N K hN b c)
      (Pi.single (tailZero N hN) 1) : GL (Fin (2 * N)) K) :
        Matrix (Fin (2 * N)) (Fin (2 * N)) K) *ᵥ v
    rw [symmetryGL_mulVec_of_charTwo hw, polar_single_tailZero]
    funext k
    rw [hAv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hpb]
    by_cases hk : k = tailZero N hN
    · subst hk
      rw [ite_eq_left rfl, Pi.single_eq_same, mul_one]
    · rw [ite_eq_right hk, Pi.single_eq_of_ne hk, mul_zero]
  rw [hTA]
  congr 1
  exact Subtype.ext hAeq

end FrobSymmetry

theorem reflMat_eq_symmetryGL {K : Type} [Field K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {w : Fin d → K} (hw : Q w = 1) (hw0 : Q w ≠ 0) :
    reflMat Q w hw0 = symmetryGL Q w := by
  apply matrixLinearIso.injective
  refine LinearEquiv.ext fun x => ?_
  change (reflMat Q w hw0).val *ᵥ x =
    ((symmetryGL Q w : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ x
  rw [reflMat_mulVec, symmetryGL_mulVec_of_charTwo hw, hw, div_one, sub_eq_add_neg, ← neg_smul,
    CharTwo.neg_eq]

theorem mul_conj_eq_conj_apply_mul {G : Type*} [Group G] (φ : MulAut G) (y : G) :
    φ * MulAut.conj y = MulAut.conj (φ y) * φ := by
  ext z
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem omegaMinusOutInput_holds : OmegaMinusOutInput := by
  intro K _ _ _ N hN4 b c hirr
  have hN : 1 ≤ N := by omega
  suffices H : ∃ v : Fin (2 * N) → K, coordinateQuadMinus N K hN b c v = 1 ∧
      ∃ C : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadMinus N K hN b c))),
        IsCyclic C ∧
        (∀ β ∈ C, β ∈ (MulAut.conj : matrixProjectiveDerived (coordinateQuadMinus N K hN b c)
          →* MulAut _).range → β = 1) ∧
        (∀ α, ∃ g, ∃ β ∈ C, α = MulAut.conj g * β) ∧
        symmetryAut (coordinateQuadMinus N K hN b c) v ∈ C from H
  have hb : b ≠ 0 := ne_zero_of_irreducible_tail b c hirr
  have := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadMinus N K b c hN4 hirr
  have hE := commutator_coordinateQuadMinus N K b c hN4 hirr
  have hAP := coordinate_minus_point_action_properties N K b c hN4 hirr
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K N hN4
    b c hirr
  have hTf := frobPair_pow_f_eq_symmetry N hN b c hb hK hirr hnd hT
  have hφf : (frobeniusEquiv K 2) ^ (f : ℕ) = 1 := by
    obtain ⟨-, -, hright, -⟩ := frobPair_pow_f N hN b c hb hK hirr
    rw [← frobPair_pow_right N hN b c hb]
    exact hright
  set Q := coordinateQuadMinus N K hN b c with hQdef
  set w : Fin (2 * N) → K := Pi.single (tailZero N hN) 1 with hwdef
  have hw : Q w = 1 := form_single_tailZero N hN b c
  have hw0 : Q w ≠ 0 := by rw [hw]; exact one_ne_zero
  set T := frobPair N hN b c hb with hTdef
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = matrixProjectiveConjugationHom Q T := ⟨_, rfl⟩
  have hτf : τ ^ (f : ℕ) = symmetryAut Q w := by rw [hτ, ← map_pow, hTf]
  have hτ2f : τ ^ (2 * (f : ℕ)) = 1 := by rw [pow_mul', hτf, symmetryAut_sq]
  have hfield : ∀ (m : ℕ) (x : matrixProjectiveDerived Q), τ ^ m = MulAut.conj x →
      (frobeniusEquiv K 2) ^ m = 1 := by
    intro m x hx
    obtain ⟨γ, rfl⟩ := matrixProjectiveProjection_surjective Q x
    rw [← kappa_derived_eq_conj, hτ, ← map_pow] at hx
    have h1 : matrixProjectiveConjugationHom Q (T ^ m * (matrixDerivedInclusion Q γ)⁻¹) = 1 := by
      rw [map_mul, map_inv, hx]
      exact mul_inv_cancel _
    have h2 := ((CFSG.RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff Q
      hnd hT hAP _).1 h1).1
    have h3 : (T ^ m * (matrixDerivedInclusion Q γ)⁻¹).val.right = (frobeniusEquiv K 2) ^ m := by
      change fieldProjection Q (T ^ m * (matrixDerivedInclusion Q γ)⁻¹) = _
      rw [map_mul, map_inv, map_pow]
      change (T.val.right) ^ m * ((matrixDerivedInclusion Q γ).val.right)⁻¹ = _
      rw [frobPair_right, matrixDerivedInclusion_val, SemidirectProduct.right_inl, inv_one,
        mul_one]
    rw [← h3]
    exact h2
  have hinner : ∀ m : ℕ, m < 2 * (f : ℕ) → ∀ x : matrixProjectiveDerived Q,
      τ ^ m = MulAut.conj x → τ ^ m = 1 := by
    intro m hm x hx
    have hφ := hfield m x hx
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact pow_zero τ
    rcases lt_trichotomy m (f : ℕ) with hlt | rfl | hgt
    · exact absurd hφ (frobeniusEquiv_pow_ne_one hK hm0 hlt)
    · exfalso
      apply F4Pilot.symmetryAut_not_mem_inner_of_regular hnd hT hE hw
      rw [← hτf, hx]
      exact ⟨x, rfl⟩
    · exfalso
      have h1 : (frobeniusEquiv K 2) ^ m =
          (frobeniusEquiv K 2) ^ (f : ℕ) * (frobeniusEquiv K 2) ^ (m - f) := by
        rw [← pow_add]
        congr 1
        omega
      rw [h1, hφf, one_mul] at hφ
      exact frobeniusEquiv_pow_ne_one hK (by omega) (by omega) hφ
  have hisom : ∀ B : matrixIsometries Q, ∃ (y : matrixProjectiveDerived Q) (k : ℕ),
      matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q B) = MulAut.conj y * τ ^ k := by
    intro B
    rcases mem_or_mul_reflMat_mem hnd hT B.2 w hw0 with hBΩ | hBΩ
    · refine ⟨matrixProjectiveProjection Q ⟨B.val, hBΩ⟩, 0, ?_⟩
      rw [pow_zero, mul_one, ← kappa_derived_eq_conj]
      rfl
    · have hsr : reflMat Q w hw0 = symmetryGL Q w := reflMat_eq_symmetryGL hw hw0
      have hR := reflMat_mem_isometries (Q := Q) w hw0
      refine ⟨matrixProjectiveProjection Q ⟨B.val * reflMat Q w hw0, hBΩ⟩, (f : ℕ), ?_⟩
      have hιB : matrixIsometryInclusion Q B =
          matrixIsometryInclusion Q ⟨B.val * reflMat Q w hw0, mul_mem B.2 hR⟩ *
            matrixIsometryInclusion Q (symmetryIsometry Q w) := by
        rw [← map_mul]
        congr 1
        apply Subtype.ext
        change B.val = B.val * reflMat Q w hw0 * symmetryGL Q w
        rw [← hsr, mul_assoc, CFSG.RankThree.PartOne.AUTSL.reflMat_mul_self, mul_one]
      rw [hιB, map_mul, hτf, ← kappa_derived_eq_conj]
      rfl
  refine ⟨w, hw, zpowers τ, inferInstance, ?_, ?_,
    mem_zpowers_iff.2 ⟨((f : ℕ) : ℤ), by rw [zpow_natCast, hτf]⟩⟩
  ·
    rintro β hβ ⟨x, hx⟩
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hβ
    have h0 : (0 : ℤ) < ((2 * (f : ℕ) : ℕ) : ℤ) := by
      have : 0 < (f : ℕ) := f.pos
      omega
    obtain ⟨m, hm, hjm⟩ : ∃ m : ℕ, m < 2 * (f : ℕ) ∧ τ ^ j = τ ^ m := by
      refine ⟨(j % ((2 * (f : ℕ) : ℕ) : ℤ)).toNat, ?_, ?_⟩
      · have h1 := Int.emod_lt_of_pos j h0
        have h2 := Int.emod_nonneg j h0.ne'
        omega
      · rw [zpow_eq_zpow_emod' j hτ2f, ← zpow_natCast,
          Int.toNat_of_nonneg (Int.emod_nonneg j h0.ne')]
    rw [hjm] at hx ⊢
    exact hinner m hm x hx.symm
  ·
    intro α
    have hα : α ∈ matrixProjectiveImage Q := by
      rw [htop]
      exact mem_top α
    obtain ⟨g, hg⟩ := (mem_matrixProjectiveImage_iff Q α).1 hα
    obtain ⟨i, hi⟩ := exists_frob_pow g.val.right
    have hℓr : (T ^ i)⁻¹ * g ∈ linearSimilarityPairs Q := by
      rw [mem_linearSimilarityPairs_iff]
      change fieldProjection Q ((T ^ i)⁻¹ * g) = 1
      rw [map_mul, map_inv, map_pow]
      change ((T.val.right) ^ i)⁻¹ * g.val.right = 1
      rw [frobPair_right, hi, inv_mul_cancel]
    obtain ⟨B, hB⟩ := CFSG.RankThree.PartOne.OutStructure.exists_isometry_of_linear Q ⟨w, hw0⟩
      ⟨(T ^ i)⁻¹ * g, hℓr⟩
    have hℓB : matrixProjectiveConjugationHom Q ((T ^ i)⁻¹ * g) =
        matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q B) := by
      refine MulEquiv.ext fun x => ?_
      obtain ⟨C, rfl⟩ := matrixProjectiveProjection_surjective Q x
      change matrixProjectiveConjugation Q ((T ^ i)⁻¹ * g) (matrixProjectiveProjection Q C) =
        matrixProjectiveConjugation Q (matrixIsometryInclusion Q B) (matrixProjectiveProjection Q C)
      rw [matrixProjectiveConjugation_mk, matrixProjectiveConjugation_mk]
      congr 1
      exact Subtype.ext ((hB C).trans (conjAct_inclusion_val B C).symm)
    obtain ⟨y, k, hyk⟩ := hisom B
    refine ⟨(τ ^ i) y, τ ^ (i + k), mem_zpowers_iff.2 ⟨((i + k : ℕ) : ℤ), zpow_natCast _ _⟩, ?_⟩
    have hgT : g = T ^ i * ((T ^ i)⁻¹ * g) := (mul_inv_cancel_left (T ^ i) g).symm
    rw [← hg]
    change matrixProjectiveConjugationHom Q g = _
    rw [hgT, map_mul, hℓB, hyk, map_pow, ← hτ, ← mul_assoc, mul_conj_eq_conj_apply_mul, pow_add,
      mul_assoc]

section Rows

theorem false_of_spOmegaMinusRow_of_kind' (hk : SpOmegaKindInput .omegaMinus)
    (hu : SpOmegaRowUniqueInput .omegaMinus) : SpOmegaMinusRowInput :=
  false_of_spOmegaMinusRow_of_kind hk hu omegaMinusOutInput_holds

end Rows

end CFSG.SeitzReduction.SymplecticPilot
