module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotAutUBasic

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart linearFieldPart_eq)
open scoped commutatorElement

section FieldAut

variable {K : Type*} [Field K] [Finite K]

theorem isCyclic_ringEquiv : IsCyclic (K ≃+* K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, m, hp, hK⟩ := FiniteField.card' K
  exact (card_ringAut_and_isCyclic hp K (by rw [Nat.card_eq_fintype_card, hK])).2

theorem ringEquiv_mul_comm (σ τ : K ≃+* K) : σ * τ = τ * σ :=
  (isCyclic_ringEquiv (K := K)).commGroup.mul_comm σ τ

end FieldAut

section FieldPart

variable {n : ℕ} {K : Type*} [Field K] [Finite K]

theorem linearFieldPart_conjAut (hn : 3 ≤ n) (A : GL (Fin n) K) :
    linearFieldPart K hn (conjAut n K A) = 1 := by
  have h := linearFieldPart_eq hn (A := A) (σ := 1) (ε := 0) zero_le_one
  rwa [map_one, mul_one, pow_zero, mul_one] at h

theorem linearFieldPart_fieldAut (hn : 3 ≤ n) (σ : K ≃+* K) :
    linearFieldPart K hn (fieldAut n K σ) = σ := by
  have h := linearFieldPart_eq (K := K) hn (A := 1) (σ := σ) (ε := 0) zero_le_one
  rwa [map_one, one_mul, pow_zero, mul_one] at h

theorem linearFieldPart_dualAut (hn : 3 ≤ n) : linearFieldPart K hn (dualAut n K) = 1 := by
  have h := linearFieldPart_eq (K := K) hn (A := 1) (σ := 1) (ε := 1) le_rfl
  rwa [map_one, map_one, one_mul, one_mul, pow_one] at h

theorem linearFieldPart_mulAut_conj (hn : 3 ≤ n) (x : projectiveSL n K) :
    linearFieldPart K hn (MulAut.conj x) = 1 := by
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  rw [← conjAut_toGL, linearFieldPart_conjAut]

theorem linearFieldPart_eq_one_iff (hn : 3 ≤ n) (α : MulAut (projectiveSL n K)) :
    linearFieldPart K hn α = 1 ↔
      ∃ (A : GL (Fin n) K) (ε : ℕ), ε ≤ 1 ∧ α = conjAut n K A * dualAut n K ^ ε := by
  constructor
  · intro h
    obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation hn).2 α
    rw [linearFieldPart_eq hn hε] at h
    subst h
    exact ⟨A, ε, hε, by rw [map_one, mul_one]⟩
  · rintro ⟨A, ε, -, rfl⟩
    rw [map_mul, map_pow, linearFieldPart_conjAut, linearFieldPart_dualAut, one_pow, one_mul]

theorem linearFieldPart_conj_eq (hn : 3 ≤ n) (α β : MulAut (projectiveSL n K)) :
    linearFieldPart K hn (β * α * β⁻¹) = linearFieldPart K hn α := by
  rw [map_mul, map_mul, map_inv, ringEquiv_mul_comm (linearFieldPart K hn β), mul_assoc,
    mul_inv_cancel, mul_one]

theorem linearFieldPart_commutator (hn : 3 ≤ n) (α β : MulAut (projectiveSL n K)) :
    linearFieldPart K hn ⁅α, β⁆ = 1 := by
  rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
    ringEquiv_mul_comm (linearFieldPart K hn α) (linearFieldPart K hn β)]
  group

theorem apply_eq_mul_linearFieldPart_of_apply_transvection (hn : 3 ≤ n)
    (β : MulAut (projectiveSL n K)) {i j : Fin n} (hij : i ≠ j) (μ : K → K)
    (hμ : ∀ c : K, β (proj n K (Matrix.SpecialLinearGroup.transvection hij c)) =
      proj n K (Matrix.SpecialLinearGroup.transvection hij (μ c))) (c : K) :
    μ c = μ 1 * linearFieldPart K hn β c := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation hn).2 β
  rw [linearFieldPart_eq hn hε]
  have key : ∀ x : K, single i j (μ x) * (A : Matrix (Fin n) (Fin n) K) =
      (A : Matrix (Fin n) (Fin n) K) * (if ε = 0 then single i j (σ x) else single j i (-σ x)) := by
    intro x
    have h := hμ x
    rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
    · rw [pow_zero, mul_one] at h
      rw [ite_eq_left rfl]
      exact single_mul_eq_of_conjAut_mul_fieldAut_apply A σ hij x (μ x) h
    · rw [pow_one] at h
      rw [ite_eq_right one_ne_zero]
      exact single_mul_eq_of_conjAut_mul_fieldAut_mul_dualAut_apply A σ hij x (μ x) h
  have hM : ∀ x : K, (if ε = 0 then single i j (σ x) else single j i (-σ x)) =
      σ x • (if ε = 0 then single i j (σ 1) else single j i (-σ 1)) := by
    intro x
    split_ifs <;> rw [smul_single, smul_eq_mul, map_one] <;> ring_nf
  have h1 := key c
  rw [hM c, Matrix.mul_smul, ← key 1, ← Matrix.smul_mul, smul_single, smul_eq_mul] at h1
  have h2 := congrArg (fun M => M * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h1
  simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at h2
  have h3 := congrFun (congrFun h2 i) j
  rw [single_apply_same, single_apply_same] at h3
  rw [h3, mul_comm]

theorem exists_unit_apply_transvection_eq (hn : 3 ≤ n) (β : MulAut (projectiveSL n K))
    {i j : Fin n} (hij : i ≠ j)
    (hU : ∀ c : K, ∃ c' : K, β (proj n K (Matrix.SpecialLinearGroup.transvection hij c)) =
      proj n K (Matrix.SpecialLinearGroup.transvection hij c')) :
    ∃ l : Kˣ, ∀ c : K, β (proj n K (Matrix.SpecialLinearGroup.transvection hij c)) =
      proj n K (Matrix.SpecialLinearGroup.transvection hij
        ((l : K) * linearFieldPart K hn β c)) := by
  choose μ hμ using hU
  have hrel := apply_eq_mul_linearFieldPart_of_apply_transvection hn β hij μ hμ
  have h1 : μ 1 ≠ 0 := by
    intro h0
    have h := hμ 1
    rw [h0, Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one,
      MulEquiv.map_eq_one_iff, proj_eq_one_iff, scalars_eq_center,
      Matrix.SpecialLinearGroup.transvection_mem_center_iff] at h
    exact one_ne_zero h
  refine ⟨Units.mk0 (μ 1) h1, fun c => ?_⟩
  rw [hμ c, hrel c, Units.val_mk0]

end FieldPart

section Parity

theorem exists_zmod_two_hom_of_isCyclic {C A : Type*} [Group C] [Finite C] [Group A]
    [hA : IsCyclic A] (φ : C →* A) (S : Sylow 2 C) (hS : ∃ s ∈ (S : Subgroup C), φ s ≠ 1) :
    ∃ χ : C →* Multiplicative (ZMod 2), φ.ker ≤ χ.ker ∧ ∃ s ∈ (S : Subgroup C), χ s ≠ 1 := by
  obtain ⟨s, hsS, hs1⟩ := hS
  have : Finite φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hHcyc : IsCyclic φ.range := inferInstance
  have hrs : φ.rangeRestrict s ≠ 1 := fun h => hs1 (congrArg Subtype.val h)
  have h2 : 2 ∣ Nat.card φ.range := by
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hsS⟩
    have hk' : φ.rangeRestrict s ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
      rw [this, map_one]
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk')
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hrs (orderOf_eq_one_iff.mp (by rw [hm, pow_zero]))
    refine dvd_trans ?_ (orderOf_dvd_natCard (φ.rangeRestrict s))
    rw [hm]
    exact dvd_pow_self 2 hm0
  set ψ : φ.range →* Multiplicative (ZMod 2) :=
    (ZMod.castHom h2 (ZMod 2)).toAddMonoidHom.toMultiplicative.comp
      (zmodCyclicMulEquiv hHcyc).symm.toMonoidHom with hψ
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx⟩ := ZMod.ringHom_surjective (ZMod.castHom h2 (ZMod 2)) (Multiplicative.toAdd y)
    refine ⟨zmodCyclicMulEquiv hHcyc (Multiplicative.ofAdd x), ?_⟩
    rw [hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact hx
  set χ : C →* Multiplicative (ZMod 2) := ψ.comp φ.rangeRestrict with hχ
  have hχs : Function.Surjective χ := hψs.comp φ.rangeRestrict_surjective
  refine ⟨χ, fun x hx => ?_, ?_⟩
  · rw [MonoidHom.mem_ker] at hx ⊢
    have : φ.rangeRestrict x = 1 := Subtype.ext hx
    rw [hχ, MonoidHom.comp_apply, this, map_one]
  · by_contra hall
    push Not at hall
    have hidx : χ.ker.index = 2 := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hχs, Subgroup.card_top,
        Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    have hdvd := Subgroup.index_dvd_of_le (fun x hx => (MonoidHom.mem_ker.mpr (hall x hx)) :
      (S : Subgroup C) ≤ χ.ker)
    rw [hidx] at hdvd
    exact S.not_dvd_index hdvd

end Parity

end CFSG.SeitzReduction.LinearPilot
