module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusFamRes
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusCover
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusData

public section

namespace CFSG.AGLEmbedding

open Matrix QuadraticMap CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin
open scoped Pointwise MatrixGroups

namespace LeviBlock

variable {r : ℕ} {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def plusFamHom [Finite K] [CharP K 2] (hr : 3 ≤ r) {D : Finset ℕ}
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r - 2) (hD' : ∀ d ∈ D, d ≤ r) {t : ℕ} (ht : t = 0 ∨ t ∈ D)
    (htm : t + 2 = r) : Fin 2 → (↥(plusFlagStab K r D) →* GL (Fin 2) K) :=
  ![SpecialLinearGroup.toGL.comp ((plusFamTwoHom K).comp ((plusResAut hD' ht htm).codRestrict _
      fun g => (plusResAut_mem_plusFamTwoStab hr hD hD' ht htm g).1)),
    SpecialLinearGroup.toGL.comp ((plusFamTwoHom K).comp
      (((MulAut.conj (swapPair K (1 : Fin 2))).toMonoidHom.comp (plusResAut hD' ht htm)).codRestrict
        _ fun g => (plusResAut_mem_plusFamTwoStab hr hD hD' ht htm g).2))]

variable [Finite K] [CharP K 2] (hr : 3 ≤ r) {D : Finset ℕ} (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r - 2)
  (hD' : ∀ d ∈ D, d ≤ r) {t : ℕ} (ht : t = 0 ∨ t ∈ D) (htm : t + 2 = r)
include hr hD

theorem plusFamHom_zero (g : ↥(plusFlagStab K r D)) :
    plusFamHom K hr hD hD' ht htm 0 g = SpecialLinearGroup.toGL (plusFamTwoHom K
      ⟨plusResAut hD' ht htm g, (plusResAut_mem_plusFamTwoStab hr hD hD' ht htm g).1⟩) :=
  rfl

theorem plusFamHom_one (g : ↥(plusFlagStab K r D)) :
    plusFamHom K hr hD hD' ht htm 1 g = SpecialLinearGroup.toGL (plusFamTwoHom K
      ⟨MulAut.conj (swapPair K (1 : Fin 2)) (plusResAut hD' ht htm g),
        (plusResAut_mem_plusFamTwoStab hr hD hD' ht htm g).2⟩) :=
  rfl

omit [Finite K] [CharP K 2] hr hD in
theorem swapPair_one_inv : (swapPair K (1 : Fin 2))⁻¹ = swapPair K 1 :=
  inv_eq_of_mul_eq_one_right (swapPair_mul_self 1)

theorem plusResAut_eq_one_of_plusFamHom {g : ↥(plusFlagStab K r D)}
    (h0 : plusFamHom K hr hD hD' ht htm 0 g = 1) (h1 : plusFamHom K hr hD hD' ht htm 1 g = 1) :
    plusResAut hD' ht htm g = 1 := by
  rw [plusFamHom_zero] at h0
  rw [plusFamHom_one] at h1
  have e0 := SpecialLinearGroup.toGL_injective (h0.trans (map_one _).symm)
  have e1 := SpecialLinearGroup.toGL_injective (h1.trans (map_one _).symm)
  refine eq_one_of_plusFam (plusResAut_mem_orthogonalGroup hD' ht htm g) (fun p hp => ?_)
    (fun p hp => ?_)
  · have h := plusFamTwoHom_spec ⟨_, (plusResAut_mem_plusFamTwoStab hr hD hD' ht htm g).2⟩ hp
    have hone : ((1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ p = p := by simp
    rw [e1, hone] at h
    change (MulAut.conj (swapPair K (1 : Fin 2)) (plusResAut hD' ht htm g)) • plusFamTwo p =
      plusFamTwo p at h
    rw [MulAut.conj_apply, swapPair_one_inv, mul_smul, mul_smul, swapPair_smul_plusFamTwo] at h
    have h' := congrArg (swapPair K (1 : Fin 2) • ·) h
    simp only [smul_smul, ← mul_assoc, swapPair_mul_self, one_mul, swapPair_smul_plusFamTwo]
      at h'
    exact h'
  · have h := plusFamTwoHom_spec ⟨_, (plusResAut_mem_plusFamTwoStab hr hD hD' ht htm g).1⟩ hp
    rw [e0] at h
    simpa using h

theorem plusFamHom_eq_one {g : ↥(plusFlagStab K r D)} (hg : plusResAut hD' ht htm g = 1)
    (j : Fin 2) : plusFamHom K hr hD hD' ht htm j g = 1 := by
  have key : ∀ (h : ↥(plusFamTwoStab K)),
      (h : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) = 1 →
      SpecialLinearGroup.toGL (plusFamTwoHom K h) = 1 := fun h h1 => by
    rw [plusFamTwoHom_eq h (A := 1) fun p _ => by rw [h1]; simp, map_one]
  fin_cases j
  · exact key _ hg
  · exact key _ (by change MulAut.conj _ (plusResAut hD' ht htm g) = 1; rw [hg, map_one])

omit hD in
theorem plusResExt_iotaTwo_mem (hDt : ∀ d ∈ D, d ≤ t) (A : SL(2, K)) :
    plusResExt K htm (plusIotaTwo K A) ∈ plusFlagStab K r D := by
  have hcut : ∀ B : SL(2, K), PlusCut (plusResExt K htm (plusIotaTwo K B)) r := fun B =>
    plusCut_plusResExt htm _ (Or.inr (Or.inr ⟨2, by omega,
      plusCut_of_smul_flag le_rfl (MulAction.mem_stabilizer_iff.1 (plusIotaTwo_mem_stabilizer B))⟩))
  have hX : plusResExt K htm (plusIotaTwo K A) • flag r K r = flag r K r :=
    smul_flag_of_plusCut le_rfl (hcut A) (by rw [← map_inv, ← map_inv]; exact hcut A⁻¹)
  refine plusResExt_mem_plusFlagStab_of_mem htm hDt (maxStab_le_orthElementaryGroup hr ?_)
  exact mem_maxStab.2 ⟨plusResExt_mem_orthogonalGroup htm (plusIotaTwo_mem_orthogonalGroup A), hX⟩

omit hD in
theorem plusResExt_iotaOne_mem (hDt : ∀ d ∈ D, d ≤ t) (A : SL(2, K)) :
    plusResExt K htm (plusIotaOne K A) ∈ plusFlagStab K r D := by
  refine plusResExt_mem_plusFlagStab_of_mem htm hDt ?_
  have hσ : plusResExt K htm (swapPair K (1 : Fin 2)) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) :=
    plusResExt_mem_orthogonalGroup htm (swapIso K 1).2
  have hE := conj_mem_orthElementaryGroup hσ
    (mem_plusFlagStab.1 (plusResExt_iotaTwo_mem hr htm hDt A)).1
  rw [← map_inv, swapPair_one_inv, ← map_mul, ← map_mul, ← plusIotaOne_apply] at hE
  exact hE

theorem plusFamHom_iotaTwo {A : SL(2, K)} (hq : plusResExt K htm (plusIotaTwo K A) ∈
    plusFlagStab K r D) :
    plusFamHom K hr hD hD' ht htm 0 ⟨_, hq⟩ = SpecialLinearGroup.toGL A ∧
      plusFamHom K hr hD hD' ht htm 1 ⟨_, hq⟩ = 1 := by
  have hR := plusResAut_plusResExt hD' ht htm hq
  refine ⟨?_, ?_⟩
  · rw [plusFamHom_zero]
    congr 1
    refine plusFamTwoHom_eq _ fun p hp => ?_
    change plusResAut hD' ht htm ⟨_, hq⟩ • _ = _
    rw [hR]
    exact plusIotaTwo_smul_plusFamTwo A hp
  · rw [plusFamHom_one, plusFamTwoHom_eq _ (A := 1) fun p hp => ?_, map_one]
    change MulAut.conj (swapPair K (1 : Fin 2)) (plusResAut hD' ht htm ⟨_, hq⟩) • _ = _
    rw [hR, MulAut.conj_apply, swapPair_one_inv, ← plusIotaOne_apply,
      plusIotaOne_smul_plusFamTwo]
    simp

theorem plusFamHom_iotaOne {A : SL(2, K)} (hq : plusResExt K htm (plusIotaOne K A) ∈
    plusFlagStab K r D) :
    plusFamHom K hr hD hD' ht htm 0 ⟨_, hq⟩ = 1 ∧
      plusFamHom K hr hD hD' ht htm 1 ⟨_, hq⟩ = SpecialLinearGroup.toGL A := by
  have hR := plusResAut_plusResExt hD' ht htm hq
  refine ⟨?_, ?_⟩
  · rw [plusFamHom_zero, plusFamTwoHom_eq _ (A := 1) fun p hp => ?_, map_one]
    change plusResAut hD' ht htm ⟨_, hq⟩ • _ = _
    rw [hR, plusIotaOne_smul_plusFamTwo]
    simp
  · rw [plusFamHom_one]
    congr 1
    refine plusFamTwoHom_eq _ fun p hp => ?_
    change MulAut.conj (swapPair K (1 : Fin 2)) (plusResAut hD' ht htm ⟨_, hq⟩) • _ = _
    rw [hR, MulAut.conj_apply, swapPair_one_inv, plusIotaOne_apply]
    simp only [← mul_assoc, swapPair_mul_self, one_mul]
    rw [mul_assoc, swapPair_mul_self, mul_one]
    exact plusIotaTwo_smul_plusFamTwo A hp

end LeviBlock

open LeviBlock

variable {r : ℕ} {K : Type} [Field K]

theorem hasLeviBlocks_plusFlagStab_two [Finite K] [CharP K 2] (hr : 3 ≤ r) {D : Finset ℕ}
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r) (ht2 : D.sup id + 2 = r) :
    HasLeviBlocks ↥(plusFlagStab K r D) (plusBlockOrders (Nat.card K)) := by
  have hD' : ∀ d ∈ D, d ≤ r := fun d hd => (hD d hd).2
  have hD1 : ∀ d ∈ D, 1 ≤ d := fun d hd => (hD d hd).1
  have hDt : ∀ d ∈ D, d ≤ D.sup id := fun d hd => Finset.le_sup (f := id) hd
  have hD₂ : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r - 2 := fun d hd => ⟨hD1 d hd, by have := hDt d hd; omega⟩
  have ht : D.sup id = 0 ∨ D.sup id ∈ D := sup_eq_zero_or_mem D
  refine hasLeviBlocks_of_sum (ι₁ := ↥D) (ι₂ := Fin 2)
    (G₁ := fun b => GL (Fin (b.1 - predCut D b.1)) K) (G₂ := fun _ => GL (Fin 2) K)
    (fun b => (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin (b.1 - predCut D b.1)) K →*
      _).range) (fun _ => (SpecialLinearGroup.toGL : SL(2, K) →* GL (Fin 2) K).range)
    (fun b => plusEBlockHom hD' b.2) (plusFamHom K hr hD₂ hD' ht ht2) ?_ ?_ ?_
    (fun b => commutator_range_plusEBlockHom_le hD' b.2) ?_
    (fun b => isQuasisimple_or_isSolvable_rangeSL _)
    (fun _ => isQuasisimple_or_isSolvable_rangeSL _)
    (fun b => card_rangeSL_quotient_center) (fun _ => card_rangeSL_quotient_center)
  · intro N hN
    refine isPGroup_of_plusBlocks hD' hD1 fun g hg => ⟨fun b hb => (hN g hg).1 ⟨b, hb⟩,
      fun x hx => ?_⟩
    exact sub_mem_of_plusResBlockHom_eq_one hD' ht ht2 (plusResBlockHom_eq_one_of_plusResAut hD'
      ht ht2 (plusResAut_eq_one_of_plusFamHom hr hD₂ hD' ht ht2 ((hN g hg).2 0)
        ((hN g hg).2 1))) hx
  · intro b x hx
    obtain ⟨q, h1, h2, h3⟩ := exists_plusFlagLevi_of_mem hr hD' b.2 hx
    refine ⟨q, h1, fun b' hne => h2 b'.1 b'.2 fun h => hne (Subtype.ext h), fun j => ?_⟩
    refine plusFamHom_eq_one hr hD₂ hD' ht ht2 ?_ j
    change matrixEquiv 2 K (plusResBlockHom hD' ht ht2 q) = 1
    rw [h3 ht ht2 (hDt b b.2), map_one]
  · intro j x hx
    obtain ⟨A, rfl⟩ := hx
    fin_cases j
    · have hq := plusResExt_iotaTwo_mem hr ht2 (D := D) hDt A
      obtain ⟨e0, e1⟩ := plusFamHom_iotaTwo hr hD₂ hD' ht ht2 hq
      refine ⟨⟨_, hq⟩, e0, fun j' hj' => ?_, fun b => plusEBlockHom_plusResExt hD' ht2 hDt b.2 hq⟩
      fin_cases j'
      · exact absurd rfl hj'
      · exact e1
    · have hq := plusResExt_iotaOne_mem hr ht2 (D := D) hDt A
      obtain ⟨e0, e1⟩ := plusFamHom_iotaOne hr hD₂ hD' ht ht2 hq
      refine ⟨⟨_, hq⟩, e1, fun j' hj' => ?_, fun b => plusEBlockHom_plusResExt hD' ht2 hDt b.2 hq⟩
      fin_cases j'
      · exact e0
      · exact absurd rfl hj'
  · intro j
    have hle : (plusFamHom K hr hD₂ hD' ht ht2 j).range ≤
        (SpecialLinearGroup.toGL : SL(2, K) →* GL (Fin 2) K).range := by
      fin_cases j <;> rintro _ ⟨g, rfl⟩ <;> exact ⟨_, rfl⟩
    refine (Subgroup.commutator_mono hle hle).trans (Subgroup.commutator_le.2 fun a ha b hb => ?_)
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem hasLeviBlocks_plusFlagStab [Finite K] [CharP K 2] (hr : 3 ≤ r) {D : Finset ℕ}
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r) (hr1 : r - 1 ∈ D → r ∈ D) :
    HasLeviBlocks ↥(plusFlagStab K r D) (plusBlockOrders (Nat.card K)) := by
  have hle : D.sup id ≤ r := Finset.sup_le fun d hd => (hD d hd).2
  rcases sup_eq_zero_or_mem D with h0 | hmem
  · exact hasLeviBlocks_plusFlagStab_res hr hD (by omega)
  · by_cases htop : D.sup id = r
    · exact hasLeviBlocks_plusFlagStab_top hr hD (htop ▸ hmem)
    · by_cases h1 : D.sup id + 1 = r
      · exfalso
        have := Finset.le_sup (f := id) (hr1 (by rw [← h1, Nat.add_sub_cancel]; exact hmem))
        simp only [id] at this
        omega
      · by_cases h2 : D.sup id + 2 = r
        · exact hasLeviBlocks_plusFlagStab_two hr hD h2
        · exact hasLeviBlocks_plusFlagStab_res hr hD (by omega)

end CFSG.AGLEmbedding
