module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L4Gen
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OutU

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q5U4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatFactsL4U4
  CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem odd_of_pow_mod_four_eq_three' {p f : ℕ} (hq : p ^ f % 4 = 3) : Odd f := by
  rcases Nat.even_or_odd f with ⟨k, rfl⟩ | hf
  · exfalso
    rw [pow_add, Nat.mul_mod] at hq
    have hr : p ^ k % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases hr' : p ^ k % 4 <;> omega
  · exact hf

theorem semilinearAutHom_inl (g : hypSU h 2 0) :
    semilinearAutHom h (by norm_num : 1 ≤ 2) (by norm_num : (0 : ℕ) ≤ 1)
      ⟨SemidirectProduct.inl (g : GL (HypIndex 2 0) K), inl_mem_semilinearSimilitudes g⟩ =
      MulAut.conj (hypProj h 2 0 g) := by
  refine MulEquiv.ext fun z => ?_
  obtain ⟨g', rfl⟩ := hypProj_surjective h 2 0 z
  rw [semilinearAutHom_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem right_eq_one_of_mem_inner (x : semilinearSimilitudes h 2 0)
    (hx : semilinearAutHom h (by norm_num : 1 ≤ 2) (by norm_num : (0 : ℕ) ≤ 1) x ∈
      inner (hypPSU h 2 0)) :
    (x : SemiGL (HypIndex 2 0) K).right = 1 := by
  obtain ⟨y, hy⟩ := hx
  obtain ⟨g, rfl⟩ := hypProj_surjective h 2 0 y
  rw [← semilinearAutHom_inl h g] at hy
  set x₁ : semilinearSimilitudes h 2 0 :=
    ⟨SemidirectProduct.inl (g : GL (HypIndex 2 0) K), inl_mem_semilinearSimilitudes g⟩ with hx₁
  have h1 : semilinearAutHom h (by norm_num : 1 ≤ 2) (by norm_num : (0 : ℕ) ≤ 1)
      (x₁⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, hy, inv_mul_cancel]
  obtain ⟨hr, -⟩ := (semilinearAutHom_eq_one_iff h (by norm_num) (by norm_num) (by norm_num)
    _).mp h1
  rw [Subgroup.coe_mul, Subgroup.coe_inv, SemidirectProduct.mul_right,
    SemidirectProduct.inv_right, hx₁] at hr
  have h1 : (1 : K ≃+* K) = RingEquiv.refl K := rfl
  rw [h1]
  simpa using hr

theorem bar_det_mul_det {A : GL (HypIndex 2 0) K} (hA : A ∈ hypUnitary h 2 0) :
    h.bar (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).det *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).det = 1 := by
  have h1 := congrArg Matrix.det (mem_hypUnitary.mp hA)
  rw [det_mul, det_mul, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h1
  have h0 := det_hypGram_ne_zero (r := 2) (ε := 0) (K := K)
  have : (h.bar (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).det *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).det - 1) * (hypGram 2 0 K).det = 0 := by
    linear_combination h1
  rcases mul_eq_zero.1 this with h2 | h2
  · linear_combination h2
  · exact absurd h2 h0

theorem sq_mem_inner_of_bar (x : semilinearSimilitudes h 2 0)
    (hxU : (x : SemiGL (HypIndex 2 0) K).left ∈ hypUnitary h 2 0)
    (hxb : ∀ c, (x : SemiGL (HypIndex 2 0) K).right c = h.bar c)
    (hsq : (x : SemiGL (HypIndex 2 0) K).right * (x : SemiGL (HypIndex 2 0) K).right = 1) :
    (semilinearAutHom h (by norm_num : 1 ≤ 2) (by norm_num : (0 : ℕ) ≤ 1) x) ^ 2 ∈
      inner (hypPSU h 2 0) := by
  set A := (x : SemiGL (HypIndex 2 0) K).left with hA
  set σ := (x : SemiGL (HypIndex 2 0) K).right with hσ
  have hσU : glAut σ A ∈ hypUnitary h 2 0 := by
    rw [mem_hypUnitary, coe_glAut]
    have h1 := map_conjTranspose_mul_mul h σ (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
      (hypGram 2 0 K)
    rw [mem_hypUnitary.mp hxU, hypGram_map_ringEquiv] at h1
    exact h1.symm
  have hB : A * glAut σ A ∈ hypSU h 2 0 := by
    rw [mem_hypSU]
    refine ⟨mem_hypUnitary.mp (mul_mem hxU hσU), ?_⟩
    rw [Units.val_mul, det_mul, coe_glAut, ← RingEquiv.mapMatrix_apply, ← RingEquiv.map_det]
    change (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).det *
      σ (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).det = 1
    rw [hxb, mul_comm]
    exact bar_det_mul_det h hxU
  have hxx : x * x = ⟨SemidirectProduct.inl (A * glAut σ A),
      inl_mem_semilinearSimilitudes ⟨_, hB⟩⟩ := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rw [Subgroup.coe_mul, SemidirectProduct.mul_left]
      rfl
    · rw [Subgroup.coe_mul, SemidirectProduct.mul_right]
      exact hsq
  rw [sq, ← map_mul, hxx]
  exact ⟨_, (semilinearAutHom_inl h ⟨_, hB⟩).symm⟩

theorem commutator_mem_inner_of_refl (x y : semilinearSimilitudes h 2 0)
    (hxU : (x : SemiGL (HypIndex 2 0) K).left ∈ hypUnitary h 2 0)
    (hyU : (y : SemiGL (HypIndex 2 0) K).left ∈ hypUnitary h 2 0)
    (hx1 : (x : SemiGL (HypIndex 2 0) K).right = 1)
    (hy1 : (y : SemiGL (HypIndex 2 0) K).right = 1) :
    ⁅semilinearAutHom h (by norm_num : 1 ≤ 2) (by norm_num : (0 : ℕ) ≤ 1) x,
      semilinearAutHom h (by norm_num : 1 ≤ 2) (by norm_num : (0 : ℕ) ≤ 1) y⁆ ∈
      inner (hypPSU h 2 0) := by
  set A := (x : SemiGL (HypIndex 2 0) K).left with hA
  set B := (y : SemiGL (HypIndex 2 0) K).left with hB
  have hxA : (x : SemiGL (HypIndex 2 0) K) = SemidirectProduct.inl A :=
    SemidirectProduct.ext rfl (by rw [hx1]; rfl)
  have hyB : (y : SemiGL (HypIndex 2 0) K) = SemidirectProduct.inl B :=
    SemidirectProduct.ext rfl (by rw [hy1]; rfl)
  have hC : ⁅A, B⁆ ∈ hypSU h 2 0 := by
    rw [mem_hypSU]
    have hCU : ⁅A, B⁆ ∈ hypUnitary h 2 0 := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hxU hyU) (inv_mem hxU)) (inv_mem hyU)
    refine ⟨mem_hypUnitary.mp hCU, ?_⟩
    rw [← GeneralLinearGroup.val_det_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _), Units.val_one]
  have hcomm : ⁅x, y⁆ = ⟨SemidirectProduct.inl ⁅A, B⁆,
      inl_mem_semilinearSimilitudes ⟨_, hC⟩⟩ := by
    apply Subtype.ext
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hxA, hyB, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
  rw [← map_commutatorElement, hcomm]
  exact ⟨_, (semilinearAutHom_inl h ⟨_, hC⟩).symm⟩

theorem noQ8Outer_hypPSU (hp2 : p ≠ 2) (hf : Odd f) :
    ∀ φ : QuaternionGroup 2 →* Outer (hypPSU h 2 0), ¬ Function.Injective φ := by
  have := h.finite
  have hn : 3 ≤ 2 * 2 + 0 := by norm_num
  have key : ∀ γ : MulAut (hypPSU h 2 0), γ ^ 4 ∈ inner (hypPSU h 2 0) →
      γ ^ 2 ∉ inner (hypPSU h 2 0) → ∃ x : semilinearSimilitudes h 2 0,
        semilinearAutHom h (by norm_num : 1 ≤ 2) (by norm_num : (0 : ℕ) ≤ 1) x = γ ∧
        (x : SemiGL (HypIndex 2 0) K).left ∈ hypUnitary h 2 0 ∧
        (x : SemiGL (HypIndex 2 0) K).right = 1 := by
    intro γ h4 h2
    obtain ⟨x₀, rfl⟩ := semilinearAutHom_surjective h (by norm_num) (by norm_num) hp2 hn γ
    obtain ⟨x, hxΦ, -, hxU⟩ := exists_unitary_rep h (by norm_num) (by norm_num) hn x₀
    rw [← hxΦ] at h4 h2 ⊢
    refine ⟨x, rfl, hxU, ?_⟩
    have h4' := right_eq_one_of_mem_inner h (x ^ 4) (by rw [map_pow]; exact h4)
    rw [Subgroup.coe_pow, ← SemidirectProduct.rightHom_eq_right, map_pow,
      SemidirectProduct.rightHom_eq_right] at h4'
    set σ := (x : SemiGL (HypIndex 2 0) K).right with hσ
    have h2f : σ ^ (2 * f) = 1 := by
      rw [← (card_ringAut_and_isCyclic h.prime K h.card).1]
      exact pow_card_eq_one'
    obtain ⟨k, rfl⟩ := hf
    have hsq : σ * σ = 1 := by
      rw [show 2 * (2 * k + 1) = 2 + 4 * k by ring, pow_add, pow_mul, h4', one_pow,
        mul_one, sq] at h2f
      exact h2f
    rcases ringEquiv_eq_refl_or_bar h hsq with h1 | hb
    · exact h1
    · exact absurd (sq_mem_inner_of_bar h x hxU hb hsq) h2
  refine noQ8Outer_of_commutator fun α β hα4 hβ4 hα2 hβ2 => ?_
  obtain ⟨x, rfl, hxU, hx1⟩ := key α hα4 hα2
  obtain ⟨y, rfl, hyU, hy1⟩ := key β hβ4 hβ2
  exact commutator_mem_inner_of_refl h x y hxU hyU hx1 hy1

include h in
theorem noQ8Outer_statedPSU (hp2 : p ≠ 2) :
    ∀ φ : QuaternionGroup 2 →* Outer (StatedProj (StatedSU 4 (p ^ f) K)),
      ¬ Function.Injective φ := by
  have hodd : Odd (p ^ f) := (h.prime.odd_of_ne_two hp2).pow
  rcases (by obtain ⟨k, hk⟩ := hodd; omega : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3) with hq | hq
  · exact noQ8Outer_of_commutator fun α β _ _ _ _ =>
      UnitaryOut.out_comm_statedSU_four h hp2 hq α β
  · obtain ⟨R₀, hR₀⟩ := exists_isHypTransport (r := 2) (ε := 0) h
    exact noQ8Outer_of_mulEquiv (hypPSUEquivStatedProj h hR₀ (by norm_num)).symm
      (noQ8Outer_hypPSU h hp2 (odd_of_pow_mod_four_eq_three' hq))

end CFSG.ClassicalInvolution.Q3.TA3.Q5U4
