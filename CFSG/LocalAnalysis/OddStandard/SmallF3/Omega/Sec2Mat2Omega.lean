module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Mat2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Block

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

theorem sl2f3_eq_mul_three_pow_three (g : SL2F3) :
    ∃ a b c : SL2F3, a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ c ^ 3 = 1 ∧ g = a * b * c := by
  revert g
  decide +kernel

theorem hom_sl2f3_mem_omegaGroup {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} (hQ : Q.Nondegenerate)
    (f : SL2F3 →* OGroup Q) (g : SL2F3) : f g ∈ omegaGroup hQ := by
  have key : ∀ x : SL2F3, x ^ 3 = 1 → f x ∈ omegaGroup hQ := by
    intro x hx
    have h3 : (f x) ^ 3 = 1 := by rw [← map_pow, hx, map_one]
    have h2 : f x * f x ∈ omegaGroup hQ := mul_self_mem_omegaGroup hQ (f x)
    have h : f x = (f x * f x)⁻¹ * (f x) ^ 3 := by group
    rw [h, h3, mul_one]
    exact (omegaGroup hQ).inv_mem h2
  obtain ⟨a, b, c, ha, hb, hc, rfl⟩ := sl2f3_eq_mul_three_pow_three g
  rw [map_mul, map_mul]
  exact mul_mem (mul_mem (key a ha) (key b hb)) (key c hc)

theorem leftMulHom_mem_omegaGroup (A : SL2F3) :
    leftMulHom A ∈ omegaGroup detForm_nondegenerate :=
  hom_sl2f3_mem_omegaGroup detForm_nondegenerate leftMulHom A

theorem rightMulHom_mem_omegaGroup (B : SL2F3) :
    rightMulHom B ∈ omegaGroup detForm_nondegenerate :=
  hom_sl2f3_mem_omegaGroup detForm_nondegenerate rightMulHom B

theorem natCard_ogroup_detForm : Nat.card (OGroup detForm) = 1152 := by
  haveI : Invertible (2 : ZMod 3) := invertibleOfNonzero (by decide)
  have hpolar : (QuadraticMap.polarBilin detForm).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mpr detForm_nondegenerate
  have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType detForm :=
    (isPlusType_iff_quadSign_eq_one detForm_nondegenerate (d := 2)
      (by rw [finrank_mat2])).mpr quadSign_detForm
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := ZMod 3)
    (Q := detForm) hpolar (m := 1) (by rw [finrank_mat2]) (ε := 1) (Or.inl ⟨rfl, hplus⟩)
  have h3 : Nat.card (ZMod 3) = 3 := Nat.card_zmod 3
  rw [h3, Finset.Icc_self, Finset.prod_singleton] at h
  have h' : ((Nat.card (OGroup detForm) : ℕ) : ℤ) = 1152 := h.trans (by norm_num)
  exact_mod_cast h'

theorem natCard_omegaGroup_detForm : Nat.card (omegaGroup detForm_nondegenerate) = 288 := by
  have h1 := Subgroup.card_mul_index (omegaGroup detForm_nondegenerate)
  rw [index_omegaGroup detForm_nondegenerate (by rw [finrank_mat2]; norm_num),
    natCard_ogroup_detForm] at h1
  omega

@[expose] noncomputable def detPhi : SL2F3 × SL2F3 →* OGroup detForm :=
  MonoidHom.noncommCoprod leftMulHom rightMulHom
    (fun A B => leftMulHom_mul_rightMulHom_comm A B)

theorem detPhi_apply (p : SL2F3 × SL2F3) : detPhi p = leftMulHom p.1 * rightMulHom p.2 := rfl

theorem sl2f3_pair_kernel (A B : SL2F3)
    (h : ∀ X : Mat2, (A : Mat2) * X * ((B⁻¹ : SL2F3) : Mat2) = X) :
    A = B ∧ ((A : Mat2) = 1 ∨ (A : Mat2) = -1) := by
  revert A B
  decide +kernel

theorem natCard_ker_detPhi_le : Nat.card detPhi.ker ≤ 2 := by
  obtain ⟨m, hm⟩ := exists_sl2f3_eq_neg_one
  have hmm : m * m = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hm]
    simp
  have hm1 : m ≠ 1 := by
    intro h
    rw [h] at hm
    exact absurd hm (by decide)
  have hord : orderOf ((m, m) : SL2F3 × SL2F3) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · ext <;> simp [pow_two, hmm]
    · intro h
      exact hm1 (congrArg Prod.fst h)
  have hle : detPhi.ker ≤ Subgroup.zpowers ((m, m) : SL2F3 × SL2F3) := by
    rintro ⟨A, B⟩ hAB
    have hX : ∀ X : Mat2, (A : Mat2) * X * ((B⁻¹ : SL2F3) : Mat2) = X := by
      intro X
      have h := congrArg (fun g : OGroup detForm => (g : Mat2 ≃ₗ[ZMod 3] Mat2) X)
        (MonoidHom.mem_ker.mp hAB)
      simpa [detPhi_apply, leftMulHom_apply, rightMulHom_apply, Matrix.mul_assoc] using h
    obtain ⟨hAB', hs⟩ := sl2f3_pair_kernel A B hX
    rcases hs with h1 | h1
    · have hA : A = 1 := Subtype.ext h1
      have hB : B = 1 := hAB'.symm.trans hA
      rw [hA, hB]
      exact Subgroup.one_mem _
    · have hA : A = m := Subtype.ext (h1.trans hm.symm)
      have hB : B = m := hAB'.symm.trans hA
      rw [hA, hB]
      exact Subgroup.mem_zpowers _
  calc Nat.card detPhi.ker ≤ Nat.card (Subgroup.zpowers ((m, m) : SL2F3 × SL2F3)) :=
        Subgroup.card_le_of_le hle
    _ = 2 := by rw [Nat.card_zpowers, hord]

theorem range_detPhi : detPhi.range = omegaGroup detForm_nondegenerate := by
  have hle : detPhi.range ≤ omegaGroup detForm_nondegenerate := by
    rintro _ ⟨⟨A, B⟩, rfl⟩
    rw [detPhi_apply]
    exact mul_mem (leftMulHom_mem_omegaGroup A) (rightMulHom_mem_omegaGroup B)
  apply Subgroup.eq_of_le_of_card_ge hle
  have h1 := Subgroup.card_ker_mul_card_range detPhi
  have hcard : Nat.card SL2F3 = 24 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [Nat.card_prod, hcard] at h1
  have h2 := natCard_ker_detPhi_le
  have h3 : 0 < Nat.card detPhi.ker := Nat.card_pos
  rw [natCard_omegaGroup_detForm]
  generalize Nat.card detPhi.ker = a at h1 h2 h3
  generalize Nat.card detPhi.range = b at h1 ⊢
  interval_cases a <;> omega

theorem leftMulHom_range_normal :
    (leftMulHom.range.subgroupOf (omegaGroup detForm_nondegenerate)).Normal := by
  constructor
  intro x hx g
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨C, hC⟩ := hx
  have hg : (g : OGroup detForm) ∈ detPhi.range := by
    rw [range_detPhi]
    exact g.2
  obtain ⟨⟨A, B⟩, hAB⟩ := hg
  refine ⟨A * C * A⁻¹, ?_⟩
  have hcomm : rightMulHom B * leftMulHom C = leftMulHom C * rightMulHom B :=
    (leftMulHom_mul_rightMulHom_comm C B).symm
  change leftMulHom (A * C * A⁻¹) =
    (g : OGroup detForm) * (x : OGroup detForm) * (g : OGroup detForm)⁻¹
  rw [← hAB, ← hC, detPhi_apply]
  simp only [map_mul, map_inv]
  calc leftMulHom A * leftMulHom C * (leftMulHom A)⁻¹
      = leftMulHom A * (leftMulHom C * rightMulHom B) * (rightMulHom B)⁻¹ *
          (leftMulHom A)⁻¹ := by group
    _ = leftMulHom A * (rightMulHom B * leftMulHom C) * (rightMulHom B)⁻¹ *
          (leftMulHom A)⁻¹ := by rw [hcomm]
    _ = _ := by group

theorem exists_pocket_model :
    ∃ K : Subgroup (OGroup detForm), piOrth detForm ∈ K ∧
      K ≤ omegaGroup detForm_nondegenerate ∧
      (K.subgroupOf (omegaGroup detForm_nondegenerate)).Normal ∧ Nonempty (K ≃* SL2F3) := by
  obtain ⟨m, hm⟩ := exists_sl2f3_eq_neg_one
  refine ⟨leftMulHom.range, ⟨m, leftMulHom_eq_piOrth hm⟩, ?_, leftMulHom_range_normal,
    ⟨(MonoidHom.ofInjective leftMulHom_injective).symm⟩⟩
  rintro _ ⟨A, rfl⟩
  exact leftMulHom_mem_omegaGroup A

end CFSG.OddStandard.SmallF3.Omega
