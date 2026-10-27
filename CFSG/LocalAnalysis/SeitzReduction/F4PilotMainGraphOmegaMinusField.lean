module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusIota
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_coe)

variable {k : Type} [Field k]

section ArtinSchreier

variable [Finite k] [CharP k 2]

theorem exists_minus_coefficient : ∃ c : k, ∀ s : k, s ^ 2 + 1 * s + c ≠ 0 := by
  have hns : ¬ Function.Surjective (fun s : k => s ^ 2 + s) := by
    intro hsurj
    have hinj : Function.Injective (fun s : k => s ^ 2 + s) :=
      Finite.injective_iff_surjective.mpr hsurj
    have h01 : (fun s : k => s ^ 2 + s) 0 = (fun s : k => s ^ 2 + s) 1 := by
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, one_pow]
      exact (CharTwo.add_self_eq_zero (1 : k)).symm
    exact zero_ne_one (hinj h01)
  simp only [Function.Surjective, not_forall, not_exists] at hns
  obtain ⟨c, hc⟩ := hns
  refine ⟨c, fun s hs => hc s ?_⟩
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  linear_combination hs - c * h2

omit [Finite k] in
@[expose] def wp (k : Type) [Field k] [CharP k 2] : k →+ k where
  toFun y := y * y + y
  map_zero' := by simp
  map_add' x y := by
    have : (2 : k) = 0 := CharTwo.two_eq_zero
    linear_combination (x * y) * this

omit [Finite k] in
theorem wp_apply (y : k) : wp k y = y * y + y := rfl

theorem wp_range_index : (wp k).range.index = 2 := by
  have hker : ∀ x : k, x ∈ (wp k).ker ↔ x ∈ ({0, 1} : Set k) := fun x => by
    rw [AddMonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff, wp_apply]
    have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
    have : x * x + x = x * (x - 1) := by linear_combination (x : k) * h2
    rw [this, mul_eq_zero, sub_eq_zero]
  have hcard : Nat.card (wp k).ker = 2 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hker), Nat.card_coe_set_eq,
      Set.ncard_pair zero_ne_one]
  have h1 := AddSubgroup.card_ker_mul_card_range (wp k)
  have h2 := AddSubgroup.card_mul_index (wp k).range
  rw [hcard] at h1
  have hpos : 0 < Nat.card (wp k).range := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h2, ← h1, mul_comm])

theorem exists_sq_add_eq_ringEquiv {c : k} (hc : ∀ s : k, s ^ 2 + 1 * s + c ≠ 0) (ρ : k ≃+* k) :
    ∃ s : k, s ^ 2 + s + c = ρ c := by
  have := Fintype.ofFinite k
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  set H := (wp k).range with hH
  have hidx : H.index = 2 := wp_range_index
  have hcH : c ∉ H := by
    rintro ⟨y, hy⟩
    rw [wp_apply] at hy
    apply hc y
    linear_combination hy + c * h2
  have hρcH : ρ c ∉ H := by
    rintro ⟨y, hy⟩
    rw [wp_apply] at hy
    apply hcH
    refine ⟨ρ.symm y, ?_⟩
    rw [wp_apply, ← map_mul, ← map_add, hy, RingEquiv.symm_apply_apply]
  have hsum : c + ρ c ∈ H :=
    (AddSubgroup.add_mem_iff_of_index_two hidx).mpr (iff_of_false hcH hρcH)
  obtain ⟨s, hs⟩ := hsum
  rw [wp_apply] at hs
  exact ⟨s, by linear_combination hs + c * h2⟩

end ArtinSchreier

section Shear

variable [CharP k 2]

omit [CharP k 2] in
theorem w_ne_u :
    (Sum.inr (Sum.inr 1) : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) ≠ Sum.inr (Sum.inr 0) := by
  simp

@[expose] def minusShearE (s : k) :
    Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k :=
  Matrix.single (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1)) s

@[expose] def minusShearMat (s : k) :
    Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k :=
  1 + minusShearE s

theorem minusShearMat_mul_self (s : k) : minusShearMat s * minusShearMat s = 1 := by
  have hE : minusShearE s * minusShearE s = 0 := by
    rw [minusShearE]
    exact Matrix.single_mul_single_of_ne (h := w_ne_u) ..
  have hEE : minusShearE s + minusShearE s = 0 := by
    ext i j
    rw [Matrix.add_apply, CharTwo.add_self_eq_zero, Matrix.zero_apply]
  rw [minusShearMat, add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, hE, add_zero,
    add_assoc, hEE, add_zero]

@[expose] def minusShear (s : k) : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k :=
  ⟨minusShearMat s, minusShearMat s, minusShearMat_mul_self s, minusShearMat_mul_self s⟩

omit [CharP k 2] in
theorem minusShearMat_mulVec (s : k) (x : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → k) :
    minusShearMat s *ᵥ x =
      x + Function.update (0 : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → k) (Sum.inr (Sum.inr 0))
        (s * x (Sum.inr (Sum.inr 1))) := by
  rw [minusShearMat, minusShearE, add_mulVec, one_mulVec, single_mulVec]

omit [CharP k 2] in
theorem minusShearMat_mulVec_apply_of_ne (s : k) (x : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → k)
    {i : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2} (hi : i ≠ Sum.inr (Sum.inr 0)) :
    (minusShearMat s *ᵥ x) i = x i := by
  rw [minusShearMat_mulVec, Pi.add_apply, Function.update_of_ne hi, Pi.zero_apply, add_zero]

omit [CharP k 2] in
theorem minusShearMat_mulVec_u (s : k) (x : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → k) :
    (minusShearMat s *ᵥ x) (Sum.inr (Sum.inr 0)) =
      x (Sum.inr (Sum.inr 0)) + s * x (Sum.inr (Sum.inr 1)) := by
  rw [minusShearMat_mulVec, Pi.add_apply, Function.update_self]

theorem statedQuadMinus_minusShear {c c' s : k} (hs : s ^ 2 + s + c = c')
    (x : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → k) :
    StatedQuadMinus 4 k 1 c (((minusShear s : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) :
      Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) *ᵥ x) =
        StatedQuadMinus 4 k 1 c' x := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  change StatedQuadMinus 4 k 1 c (minusShearMat s *ᵥ x) = _
  have hsum : ∑ i : Fin (4 - 1), (minusShearMat s *ᵥ x) (Sum.inl i) *
      (minusShearMat s *ᵥ x) (Sum.inr (Sum.inl i)) =
      ∑ i : Fin (4 - 1), x (Sum.inl i) * x (Sum.inr (Sum.inl i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [minusShearMat_mulVec_apply_of_ne _ _ Sum.inl_ne_inr,
      minusShearMat_mulVec_apply_of_ne _ _ (fun h => Sum.inl_ne_inr (Sum.inr_injective h))]
  simp only [StatedQuadMinus]
  rw [hsum, minusShearMat_mulVec_u, minusShearMat_mulVec_apply_of_ne _ _ w_ne_u, ← hs]
  linear_combination (s * x (Sum.inr (Sum.inr 0)) * x (Sum.inr (Sum.inr 1))) * h2

omit [CharP k 2] in
theorem minusShearMat_mulVec_minusVec (s : k) : minusShearMat s *ᵥ minusVec k = minusVec k := by
  rw [minusShearMat_mulVec]
  have h1 : minusVec k (Sum.inr (Sum.inr 1)) = 0 := Pi.single_eq_of_ne w_ne_u _
  rw [h1, mul_zero]
  have h0 : Function.update (0 : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → k) (Sum.inr (Sum.inr 0)) 0 =
      0 := by
    ext i
    simp [Function.update_apply]
  rw [h0, add_zero]

omit [CharP k 2] in
theorem minusShearMat_conj_submatrix (s : k)
    (N : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) :
    (minusShearMat s * N * minusShearMat s).submatrix minusEmb minusEmb =
      N.submatrix minusEmb minusEmb := by
  ext i j
  have h1 : ∀ (M : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k),
      (minusShearE s * M) (minusEmb i) (minusEmb j) = 0 := fun M =>
    Matrix.single_mul_apply_of_ne (h := minusEmb_ne_u i) (M := M) ..
  have h2 : ∀ (M : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k),
      (M * minusShearE s) (minusEmb i) (minusEmb j) = 0 := fun M =>
    Matrix.mul_single_apply_of_ne (hbj := minusEmb_ne_w j) (M := M) ..
  rw [submatrix_apply, submatrix_apply, minusShearMat, mul_add, mul_one, Matrix.add_apply, h2,
    add_zero, add_mul, one_mul, Matrix.add_apply, h1, add_zero]

variable (k)

@[expose] noncomputable def omegaMinusFieldAut (c : k) (ρ : k ≃+* k) (s : k)
    (hs : s ^ 2 + s + c = ρ c) : MulAut (StatedOmega (StatedQuadMinus 4 k 1 c)) :=
  (((glCongr ρ).subgroupMap (StatedOmega (StatedQuadMinus 4 k 1 c))).trans
    (MulEquiv.subgroupCongr (CFSG.ClassicalInvolution.Upgrade.map_statedOmega ρ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp ρ (n := 4) (map_one ρ) rfl)))).trans
  (((MulAut.conj (minusShear s)).subgroupMap (StatedOmega (StatedQuadMinus 4 k 1 (ρ c)))).trans
    (MulEquiv.subgroupCongr (CFSG.ClassicalInvolution.Upgrade.map_statedOmega_conj (minusShear s)
      (statedQuadMinus_minusShear hs))))

variable {k}

theorem coe_omegaMinusFieldAut (c : k) (ρ : k ≃+* k) (s : k) (hs : s ^ 2 + s + c = ρ c)
    (A : StatedOmega (StatedQuadMinus 4 k 1 c)) :
    (((omegaMinusFieldAut k c ρ s hs A : StatedOmega (StatedQuadMinus 4 k 1 c)) :
        GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) :
          Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) =
      minusShearMat s * ((A : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) :
        Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k).map ρ *
          minusShearMat s := rfl

end Shear

theorem comp_minusVec (ρ : k ≃+* k) : (ρ : k → k) ∘ minusVec k = minusVec k := by
  funext i
  simp only [Function.comp_apply, minusVec, Pi.single_apply]
  split_ifs <;> simp

variable [CharP k 2] [Finite k]

theorem omegaMinusFieldAut_iota {c : k} (hc : ∀ s : k, s ^ 2 + 1 * s + c ≠ 0) {f : ℕ}
    (hK : Nat.card k = 2 ^ f) (hf : 2 ≤ f) (ρ : k ≃+* k) (s : k) (hs : s ^ 2 + s + c = ρ c)
    (g : StatedSp 3 k) :
    omegaMinusFieldAut k c ρ s hs (omegaMinusIota hK hf hc g) =
      omegaMinusIota hK hf hc (statedSpMap (ρ : k →+* k) 3 g) := by
  set x := omegaMinusIota hK hf hc g with hxdef
  have hx : x ∈ fixedSubgroup (omegaMinusBetaC k 1 c) :=
    (range_omegaMinusIota hK hf hc) ▸ ⟨g, rfl⟩
  have hρx : omegaMinusFieldAut k c ρ s hs x ∈ fixedSubgroup (omegaMinusBetaC k 1 c) := by
    rw [mem_fixedSubgroup_omegaMinusBetaC_iff k hc] at hx ⊢
    rw [coe_omegaMinusFieldAut, ← mulVec_mulVec, ← mulVec_mulVec, minusShearMat_mulVec_minusVec]
    have h1 : ((x : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕
        Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k).map ρ *ᵥ minusVec k = minusVec k := by
      funext i
      have h2 := RingHom.map_mulVec (ρ : k →+* k)
        ((x : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕
          Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) (minusVec k) i
      rw [hx, RingEquiv.coe_toRingHom, comp_minusVec] at h2
      rw [← h2]
      exact congrFun (comp_minusVec ρ) i
    rw [h1, minusShearMat_mulVec_minusVec]
  symm
  apply omegaMinusIota_eq_of_res hK hf hc (y := ⟨_, hρx⟩)
  have hres := omegaMinusRes_omegaMinusIota hK hf hc g
  have hg : ((g : GL (Fin 3 ⊕ Fin 3) k) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k) =
      ((x : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)
        (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k).submatrix minusEmb minusEmb := by
    rw [← hres, coe_omegaMinusRes]
  apply mat_injective
  rw [CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply, coe_omegaMinusRes,
    coe_omegaMinusFieldAut, minusShearMat_conj_submatrix,
    CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply, coe_statedSpMap, coe_map_GL, hg]
  rfl

end CFSG.SeitzReduction.F4Pilot
