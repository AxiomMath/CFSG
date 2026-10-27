module

public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut
public import CFSG.LinearAlgebra.SL2CoprimeOrder

public section

open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local

namespace SL2Pure

variable {F : Type} [Field F]

theorem eq_of_smul_one_add_smul_eq {G : Matrix (Fin 2) (Fin 2) F}
    (hG : ∀ c : F, G ≠ c • (1 : Matrix (Fin 2) (Fin 2) F)) {a b a' b' : F}
    (h : a • (1 : Matrix (Fin 2) (Fin 2) F) + b • G = a' • 1 + b' • G) : a = a' ∧ b = b' := by
  have hb : b = b' := by
    by_contra hne
    have hsub : b - b' ≠ 0 := sub_ne_zero.2 hne
    apply hG ((a' - a) / (b - b'))
    have h' : (b - b') • G = (a' - a) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      linear_combination (norm := module) h
    calc G = ((b - b')⁻¹ * (b - b')) • G := by rw [inv_mul_cancel₀ hsub, one_smul]
      _ = (b - b')⁻¹ • ((b - b') • G) := by rw [mul_smul]
      _ = (b - b')⁻¹ • ((a' - a) • (1 : Matrix (Fin 2) (Fin 2) F)) := by rw [h']
      _ = ((a' - a) / (b - b')) • (1 : Matrix (Fin 2) (Fin 2) F) := by
        rw [smul_smul, div_eq_inv_mul]
  subst hb
  refine ⟨?_, rfl⟩
  have h1 := add_right_cancel h
  have h00 := congrFun (congrFun h1 0) 0
  simpa using h00

theorem det_smul_one_add_smul (M : Matrix (Fin 2) (Fin 2) F) (a b : F) :
    (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • M).det = a ^ 2 + a * b * M.trace + b ^ 2 * M.det := by
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff,
    OfNat.ofNat_ne_one, not_false_eq_true, smul_eq_mul, mul_zero, mul_one, zero_add]
  ring

theorem smul_one_add_smul_mul {M : Matrix (Fin 2) (Fin 2) F} {τ : F} (hsq : M * M = τ • M - 1)
    (a b a' b' : F) :
    (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • M) * (a' • (1 : Matrix (Fin 2) (Fin 2) F) + b' • M) =
      (a * a' - b * b') • (1 : Matrix (Fin 2) (Fin 2) F) +
        (a * b' + a' * b + b * b' * τ) • M := by
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_smul, hsq]
  module

theorem trace_sq_ne_four_of_pow_eq_one {A : Matrix (Fin 2) (Fin 2) F} (hA : A.det = 1)
    (hns : ∀ c : F, A ≠ c • (1 : Matrix (Fin 2) (Fin 2) F)) {m : ℕ} (hm : (m : F) ≠ 0)
    (hpow : A ^ m = 1) : A.trace ^ 2 ≠ 4 := by
  intro h4
  obtain ⟨μ, hτ, hμ⟩ : ∃ μ : F, A.trace = 2 * μ ∧ μ ^ 2 = 1 := by
    by_cases h2 : (2 : F) = 0
    · refine ⟨1, ?_, by norm_num⟩
      have h0 : A.trace ^ 2 = 0 := by
        rw [h4]
        linear_combination (2 : F) * h2
      rw [pow_eq_zero_iff (two_ne_zero' ℕ)] at h0
      rw [h0, h2]; ring
    · refine ⟨A.trace / 2, by field_simp, ?_⟩
      field_simp
      linear_combination h4
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp at hμ
  have hA2 : A * A = (2 * μ) • A - (μ ^ 2) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [CFSG.LinearAlgebra.mul_self_eq_trace_smul_sub_one A hA, hτ, hμ, one_smul]
  have hm0 : m ≠ 0 := fun h => hm (by rw [h, Nat.cast_zero])
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hp := CFSG.LinearAlgebra.pow_succ_of_sq_eq A hA2 n
  rw [hpow] at hp
  have hcoef : ((n : F) + 1) * μ ^ n ≠ 0 := by
    refine mul_ne_zero ?_ (pow_ne_zero _ hμ0)
    simpa [Nat.cast_succ] using hm
  apply hns ((((n : F) + 1) * μ ^ n)⁻¹ * (1 + (n : F) * μ ^ (n + 1)))
  have h1 : (((n : F) + 1) * μ ^ n) • A =
      (1 + (n : F) * μ ^ (n + 1)) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [eq_sub_iff_add_eq] at hp
    rw [← hp, add_smul, one_smul]
  rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hcoef, one_smul]

theorem exists_extension_root (τ : F) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K) (μ : K), μ ^ 2 - algebraMap F K τ * μ + 1 = 0 := by
  have hdeg : (Polynomial.C (1 : AlgebraicClosure F) * Polynomial.X ^ 2 +
      Polynomial.C (-(algebraMap F (AlgebraicClosure F) τ)) * Polynomial.X +
        Polynomial.C 1).degree ≠ 0 := by
    rw [Polynomial.degree_quadratic one_ne_zero]
    norm_num
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨AlgebraicClosure F, inferInstance, inferInstance, μ, ?_⟩
  simpa [Polynomial.IsRoot, sub_eq_add_neg] using hμ

theorem exists_embedding_of_commute {G : SL(2, F)} (hG : G ∉ Subgroup.center SL(2, F))
    (hτ : (Matrix.trace (G : Matrix (Fin 2) (Fin 2) F)) ^ 2 ≠ 4)
    (X : Subgroup SL(2, F)) (hX : ∀ x ∈ X, x * G = G * x) :
    ∃ (K : Type) (_ : Field K) (ψ : ↥X →* K), Function.Injective ψ := by
  classical
  have hns := CFSG.GH74.GLS.IVK.Lifted.nonscalar_of_not_mem_center G hG
  set M : Matrix (Fin 2) (Fin 2) F := (G : Matrix (Fin 2) (Fin 2) F) with hM
  set τ : F := Matrix.trace M with hτdef
  have hdet : M.det = 1 := G.2
  have hsq : M * M = τ • M - 1 := CFSG.LinearAlgebra.mul_self_eq_trace_smul_sub_one M hdet
  obtain ⟨K, _, _, μ, hμ⟩ := exists_extension_root τ
  have hcoord : ∀ x : ↥X, ∃ a b : F,
      ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = a • (1 : Matrix (Fin 2) (Fin 2) F) + b • M := by
    intro x
    refine CFSG.GH74.GLS.IVK.Lifted.exists_eq_smul_add_of_commute M hns _ ?_
    have := congrArg (fun z : SL(2, F) => (z : Matrix (Fin 2) (Fin 2) F)) (hX x x.2)
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using this
  choose α β hαβ using hcoord
  have huniq : ∀ (x : ↥X) (a' b' : F),
      ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = a' • (1 : Matrix (Fin 2) (Fin 2) F) + b' • M →
        a' = α x ∧ b' = β x :=
    fun x a' b' h => eq_of_smul_one_add_smul_eq hns (h.symm.trans (hαβ x))
  have hmulc : ∀ x y : ↥X, α (x * y) = α x * α y - β x * β y ∧
      β (x * y) = α x * β y + α y * β x + β x * β y * τ := by
    intro x y
    have hxy : (((x * y : ↥X) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        (α x * α y - β x * β y) • (1 : Matrix (Fin 2) (Fin 2) F) +
          (α x * β y + α y * β x + β x * β y * τ) • M := by
      rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hαβ x, hαβ y]
      exact smul_one_add_smul_mul hsq _ _ _ _
    have := huniq (x * y) _ _ hxy
    exact ⟨this.1.symm, this.2.symm⟩
  have hone : α 1 = 1 ∧ β 1 = 0 := by
    have := huniq 1 1 0 (by simp)
    exact ⟨this.1.symm, this.2.symm⟩
  let ψ₀ : ↥X → K := fun x => algebraMap F K (α x) + algebraMap F K (β x) * μ
  have hψone : ψ₀ 1 = 1 := by
    simp [ψ₀, hone.1, hone.2]
  have hψmul : ∀ x y : ↥X, ψ₀ (x * y) = ψ₀ x * ψ₀ y := by
    intro x y
    obtain ⟨h1, h2⟩ := hmulc x y
    simp only [ψ₀, h1, h2, map_sub, map_mul, map_add]
    linear_combination (-(algebraMap F K (β x) * algebraMap F K (β y))) * hμ
  refine ⟨K, inferInstance, { toFun := ψ₀, map_one' := hψone, map_mul' := hψmul }, ?_⟩
  rw [injective_iff_map_eq_one]
  intro x hx
  have hx' : algebraMap F K (α x) + algebraMap F K (β x) * μ = 1 := hx
  have hdetF : (α x) ^ 2 + α x * β x * τ + (β x) ^ 2 = 1 := by
    have h1 : (((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)).det = 1 := (x : SL(2, F)).2
    rw [hαβ x, det_smul_one_add_smul, ← hτdef, hdet, mul_one] at h1
    exact h1
  have hdetK : (algebraMap F K (α x)) ^ 2 + algebraMap F K (α x) * algebraMap F K (β x) *
      algebraMap F K τ + (algebraMap F K (β x)) ^ 2 = 1 := by
    have := congrArg (algebraMap F K) hdetF
    simpa only [map_add, map_mul, map_pow, map_one] using this
  have hbT : algebraMap F K (β x) * (algebraMap F K τ - 2 * μ) = 0 := by
    linear_combination hdetK - (algebraMap F K (β x)) ^ 2 * hμ -
      (2 * (1 - algebraMap F K (β x) * μ) + (algebraMap F K (α x) + algebraMap F K (β x) * μ - 1) +
        algebraMap F K (β x) * algebraMap F K τ) * hx'
  have hne : algebraMap F K τ - 2 * μ ≠ 0 := by
    intro h0
    apply hτ
    have h4 : (algebraMap F K τ) ^ 2 = 4 := by
      linear_combination (algebraMap F K τ - 2 * μ) * h0 - 4 * hμ
    apply (algebraMap F K).injective
    simpa only [map_pow, map_ofNat] using h4
  have hβ0 : β x = 0 := by
    have := (mul_eq_zero.1 hbT).resolve_right hne
    exact (map_eq_zero_iff _ (algebraMap F K).injective).1 this
  have hα1 : α x = 1 := by
    apply (algebraMap F K).injective
    rw [map_one]
    simpa [hβ0] using hx'
  apply Subtype.ext
  apply Subtype.ext
  rw [hαβ x, hα1, hβ0]
  simp

end SL2Pure

variable {F : Type} [Field F]

theorem sl2_commute_of_centralizer {g a b : SL(2, F)} (hg : g ∉ Subgroup.center SL(2, F))
    (ha : a * g = g * a) (hb : b * g = g * b) : a * b = b * a := by
  have hns := CFSG.GH74.GLS.IVK.Lifted.nonscalar_of_not_mem_center g hg
  have ha' : (a : Matrix (Fin 2) (Fin 2) F) * g = g * a := by
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using
      congrArg (fun z : SL(2, F) => (z : Matrix (Fin 2) (Fin 2) F)) ha
  have hb' : (b : Matrix (Fin 2) (Fin 2) F) * g = g * b := by
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using
      congrArg (fun z : SL(2, F) => (z : Matrix (Fin 2) (Fin 2) F)) hb
  exact CFSG.GH74.GLS.IVK.Lifted.comm_of_commute_matrix _ hns a b ha' hb'

theorem sl2_involution_central (h2 : (2 : F) ≠ 0) {a : SL(2, F)} (ha : a * a = 1) :
    a ∈ Subgroup.center SL(2, F) := by
  by_contra hnc
  have hns := CFSG.GH74.GLS.IVK.Lifted.nonscalar_of_not_mem_center a hnc
  have hM : (a : Matrix (Fin 2) (Fin 2) F) * a = 1 := by
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using
      congrArg (fun z : SL(2, F) => (z : Matrix (Fin 2) (Fin 2) F)) ha
  have hcay := CFSG.LinearAlgebra.mul_self_eq_trace_smul_sub_one (a : Matrix (Fin 2) (Fin 2) F) a.2
  rw [hM] at hcay
  have h1 : (Matrix.trace (a : Matrix (Fin 2) (Fin 2) F)) • (a : Matrix (Fin 2) (Fin 2) F) =
      (1 : Matrix (Fin 2) (Fin 2) F) + 1 := sub_eq_iff_eq_add.mp hcay.symm
  have ht : Matrix.trace (a : Matrix (Fin 2) (Fin 2) F) ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at h1
    have h00 := congrFun (congrFun h1 0) 0
    simp at h00
    apply h2
    linear_combination -h00
  apply hns ((Matrix.trace (a : Matrix (Fin 2) (Fin 2) F))⁻¹ * 2)
  calc (a : Matrix (Fin 2) (Fin 2) F)
      = (Matrix.trace (a : Matrix (Fin 2) (Fin 2) F))⁻¹ •
          ((Matrix.trace (a : Matrix (Fin 2) (Fin 2) F)) • (a : Matrix (Fin 2) (Fin 2) F)) := by
        rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    _ = ((Matrix.trace (a : Matrix (Fin 2) (Fin 2) F))⁻¹ * 2) •
          (1 : Matrix (Fin 2) (Fin 2) F) := by
        rw [h1, mul_smul, two_smul]

theorem sl2_abelian_two_group_cyclic [Finite F] (h2 : (2 : F) ≠ 0) (X : Subgroup SL(2, F))
    (hab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (h2g : ∀ x ∈ X, ∃ n : ℕ, x ^ (2 ^ n) = 1) :
    IsCyclic ↥X := by
  obtain ⟨g, hgc, hgcomm, hτ⟩ : ∃ g : SL(2, F), g ∉ Subgroup.center SL(2, F) ∧
      (∀ x ∈ X, x * g = g * x) ∧ (Matrix.trace (g : Matrix (Fin 2) (Fin 2) F)) ^ 2 ≠ 4 := by
    by_cases hcen : ∀ x ∈ X, x ∈ Subgroup.center SL(2, F)
    ·
      let g₀ : SL(2, F) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
      refine ⟨g₀, ?_, fun x hx => (Subgroup.mem_center_iff.1 (hcen x hx) g₀).symm, ?_⟩
      · intro hc
        obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
        have h01 := congrFun (congrFun hc 0) 1
        simp [g₀] at h01
      · have h4 : (4 : F) ≠ 0 := by
          simpa [show (4 : F) = 2 * 2 by norm_num] using mul_ne_zero h2 h2
        simpa [g₀, Matrix.trace_fin_two] using h4.symm
    · push Not at hcen
      obtain ⟨g, hgX, hgc⟩ := hcen
      refine ⟨g, hgc, fun x hx => hab x hx g hgX, ?_⟩
      obtain ⟨n, hn⟩ := h2g g hgX
      refine SL2Pure.trace_sq_ne_four_of_pow_eq_one g.2
        (CFSG.GH74.GLS.IVK.Lifted.nonscalar_of_not_mem_center g hgc) (m := 2 ^ n) ?_ ?_
      · rw [Nat.cast_pow, Nat.cast_ofNat]
        exact pow_ne_zero n h2
      · rw [← Matrix.SpecialLinearGroup.coe_pow, hn]
        rfl
  obtain ⟨K, _, ψ, hψ⟩ := SL2Pure.exists_embedding_of_commute hgc hτ X hgcomm
  exact isCyclic_of_injective_ringHom ψ hψ

theorem sl2_elem_abelian_card_le [Finite F] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrF : (r : F) ≠ 0)
    (X : Subgroup SL(2, F)) (hab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hexp : ∀ x ∈ X, x ^ r = 1) :
    Nat.card ↥X ≤ r := by
  by_cases hX : ∀ x ∈ X, x = 1
  · have hsub : Subsingleton ↥X := ⟨fun a b => Subtype.ext ((hX a a.2).trans (hX b b.2).symm)⟩
    rw [Nat.card_of_subsingleton (1 : ↥X)]
    exact hr.one_lt.le
  · push Not at hX
    obtain ⟨g, hgX, hg1⟩ := hX
    have hodd : Odd r := hr.odd_of_ne_two hr2
    have hgc : g ∉ Subgroup.center SL(2, F) := by
      intro hc
      apply hg1
      have hsq := CFSG.GH74.GLS.IVK.Lifted.sq_eq_one_of_mem_center_sl2 hc
      obtain ⟨k, hk⟩ := hodd
      have h := hexp g hgX
      rw [hk, pow_succ, pow_mul, sq, hsq, one_pow, one_mul] at h
      exact h
    have hτ : (Matrix.trace (g : Matrix (Fin 2) (Fin 2) F)) ^ 2 ≠ 4 := by
      refine SL2Pure.trace_sq_ne_four_of_pow_eq_one g.2
        (CFSG.GH74.GLS.IVK.Lifted.nonscalar_of_not_mem_center g hgc) hrF ?_
      rw [← Matrix.SpecialLinearGroup.coe_pow, hexp g hgX]
      rfl
    obtain ⟨K, _, ψ, hψ⟩ :=
      SL2Pure.exists_embedding_of_commute hgc hτ X (fun x hx => hab x hx g hgX)
    have : NeZero r := ⟨hr.ne_zero⟩
    have hmem : ∀ x : ↥X, ψ.toHomUnits x ∈ rootsOfUnity r K := by
      intro x
      rw [mem_rootsOfUnity, ← map_pow]
      have : x ^ r = 1 := Subtype.ext (hexp x x.2)
      rw [this, map_one]
    let φ : ↥X →* rootsOfUnity r K := (ψ.toHomUnits).codRestrict _ hmem
    have hφ : Function.Injective φ := by
      intro x y hxy
      apply hψ
      have := congrArg (fun z : rootsOfUnity r K => ((z : Kˣ) : K)) hxy
      simpa [φ] using this
    calc Nat.card ↥X ≤ Nat.card (rootsOfUnity r K) := Nat.card_le_card_of_injective φ hφ
      _ ≤ r := card_rootsOfUnity K r

end CFSG.GH74.GLS.LU.Local
