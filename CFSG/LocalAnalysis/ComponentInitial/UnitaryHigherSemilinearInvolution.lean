module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearAut
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem ringEquiv_eq_refl_or_bar (h : UnitaryFieldData p f K) {σ : K ≃+* K}
    (hσ : σ * σ = 1) : σ = RingEquiv.refl K ∨ ∀ c, σ c = h.bar c := by
  classical
  obtain ⟨φ, -, -, hzp, hcard, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality h.prime (by have := h.one_le; omega) h.card
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; have := h.one_le; omega)
  have : Fintype (K ≃+* K) := Fintype.ofFinite _
  have : IsCyclic (K ≃+* K) := ⟨⟨φ, fun x =>
    Subgroup.mem_zpowers_iff.mp (by rw [hzp]; exact Subgroup.mem_top x)⟩⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨β, hβ⟩ : ∃ β : K ≃+* K, ∀ c, β c = h.bar c :=
    ⟨RingEquiv.ofBijective h.bar ⟨h.bar.injective, fun c => ⟨h.bar c, h.bar_bar c⟩⟩,
      fun _ => rfl⟩
  have hβ1 : β ≠ 1 := fun h1 => by
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    exact hc (by rw [← hβ, h1]; rfl)
  have hβ2 : β ^ 2 = 1 := RingEquiv.ext fun c => by
    rw [pow_two]
    change β (β c) = c
    rw [hβ, hβ, h.bar_bar]
  by_cases hσ1 : σ = 1
  · exact Or.inl hσ1
  · right
    have hd : 2 ∣ Fintype.card (K ≃+* K) := by
      rw [Fintype.card_eq_nat_card, hcard]
      exact dvd_mul_right 2 f
    have h1 := IsCyclic.card_orderOf_eq_totient hd
    rw [Nat.totient_two] at h1
    obtain ⟨g, hg⟩ := Finset.card_eq_one.mp h1
    have hσmem : σ ∈ ({g} : Finset (K ≃+* K)) := by
      rw [← hg, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, orderOf_eq_prime (by rw [pow_two]; exact hσ) hσ1⟩
    have hβmem : β ∈ ({g} : Finset (K ≃+* K)) := by
      rw [← hg, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, orderOf_eq_prime hβ2 hβ1⟩
    rw [Finset.mem_singleton] at hσmem hβmem
    intro c
    rw [hσmem, ← hβmem, hβ]

section Unitary

@[expose] def hypUnitary (h : UnitaryFieldData p f K) (r ε : ℕ) :
    Subgroup (GL (HypIndex r ε) K) where
  carrier := {A | ((A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ * hypGram r ε K *
    (A : Matrix (HypIndex r ε) (HypIndex r ε) K) = hypGram r ε K}
  mul_mem' {A B} hA hB := by
    change (((A * B : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map
      h.bar)ᵀ * hypGram r ε K * ((A * B : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) = hypGram r ε K
    rw [Units.val_mul, conjTranspose_mul_mul, hA, hB]
  one_mem' := by
    change (((1 : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map
      h.bar)ᵀ * hypGram r ε K * ((1 : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) = hypGram r ε K
    rw [Units.val_one, Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one,
      Matrix.one_mul, Matrix.mul_one]
  inv_mem' {A} hA := by
    have hAB : ((A : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        ((A⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h1 := inv_similitude h one_ne_zero (by rw [one_smul]; exact hA) hAB
    rw [inv_one, one_smul] at h1
    exact h1

theorem mem_hypUnitary {h : UnitaryFieldData p f K} {A : GL (HypIndex r ε) K} :
    A ∈ hypUnitary h r ε ↔ ((A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ *
      hypGram r ε K * (A : Matrix (HypIndex r ε) (HypIndex r ε) K) = hypGram r ε K :=
  Iff.rfl

abbrev hypUnitaryMod (h : UnitaryFieldData p f K) (r ε : ℕ) : Type :=
  hypUnitary h r ε ⧸ normOneScalars h (hypUnitary h r ε) 0

end Unitary

section Scalars

variable (h : UnitaryFieldData p f K)

theorem scalar_gram (c : K) :
    ((Matrix.scalar (HypIndex r ε) c).map h.bar)ᵀ * hypGram r ε K *
      Matrix.scalar (HypIndex r ε) c = h.norm c • hypGram r ε K := by
  rw [scalar_apply, diagonal_map (map_zero h.bar), diagonal_transpose]
  ext a b
  rw [mul_diagonal, diagonal_mul, Matrix.smul_apply, smul_eq_mul, UnitaryFieldData.norm]
  ring

theorem scalarSim_mem (c : Kˣ) :
    SemidirectProduct.inl (GeneralLinearGroup.scalar (HypIndex r ε) c) ∈
      semilinearSimilitudes h r ε :=
  ⟨h.norm c, norm_ne_zero_of_ne_zero h c.ne_zero, h.mem_fixedField.mp (h.norm_mem_fixedField c),
    by rw [SemidirectProduct.left_inl, GeneralLinearGroup.coe_scalar]; exact scalar_gram h c⟩

variable (hr : 1 ≤ r) (hε : ε ≤ 1)

theorem exists_unitary_rep (hn : 3 ≤ 2 * r + ε) (x₀ : semilinearSimilitudes h r ε) :
    ∃ x : semilinearSimilitudes h r ε,
      semilinearAutHom h hr hε x = semilinearAutHom h hr hε x₀ ∧
      (x : SemiGL (HypIndex r ε) K).right = (x₀ : SemiGL (HypIndex r ε) K).right ∧
      (x : SemiGL (HypIndex r ε) K).left ∈ hypUnitary h r ε := by
  obtain ⟨μ, hμ0, hμ, hA⟩ := x₀.2
  have hμF : μ⁻¹ ∈ h.fixedField := h.mem_fixedField.mpr (by rw [map_inv₀, hμ])
  have hne : (⟨μ⁻¹, hμF⟩ : h.fixedField) ≠ 0 := fun h0 =>
    inv_ne_zero hμ0 (congrArg Subtype.val h0)
  obtain ⟨d, hd⟩ := (unitary_field_norm h).2.1 (Units.mk0 _ hne)
  have hdN : h.norm (d : K) = μ⁻¹ := by
    have h1 := congrArg (fun u : h.fixedFieldˣ => ((u : h.fixedField) : K)) hd
    exact h1
  obtain ⟨s, hs⟩ : ∃ s : semilinearSimilitudes h r ε, s = ⟨_, scalarSim_mem h d⟩ := ⟨_, rfl⟩
  have hs1 : semilinearAutHom h hr hε s = 1 :=
    (semilinearAutHom_eq_one_iff h hr hε hn s).mpr ⟨by rw [hs]; rfl, d, by rw [hs]; rfl⟩
  have e : ((s * x₀ : semilinearSimilitudes h r ε) : SemiGL (HypIndex r ε) K) =
      SemidirectProduct.inl (GeneralLinearGroup.scalar (HypIndex r ε) d) *
        (x₀ : SemiGL (HypIndex r ε) K) := by
    rw [Subgroup.coe_mul, hs]
  refine ⟨s * x₀, by rw [map_mul, hs1, one_mul], ?_, ?_⟩
  · rw [e, SemidirectProduct.mul_right, SemidirectProduct.right_inl, one_mul]
  · rw [e, mem_hypUnitary, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply, Units.val_mul,
      conjTranspose_mul_mul, GeneralLinearGroup.coe_scalar, scalar_gram, Matrix.mul_smul,
      Matrix.smul_mul, hA, smul_smul, hdN, inv_mul_cancel₀ hμ0, one_smul]

end Scalars

theorem odd_unitary_automorphism_semilinear_representation (h : UnitaryFieldData p f K)
    (hp : p ≠ 2) (hr : 1 ≤ r) (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε) :
    (∀ (x : semilinearSimilitudes h r ε) (g : hypSU h r ε),
      semilinearAutHom h hr hε x (hypProj h r ε g) = hypProj h r ε ⟨_, conj_mem_hypSU x.2 g⟩) ∧
    Function.Surjective (semilinearAutHom h hr hε) ∧
    (∀ x : semilinearSimilitudes h r ε, semilinearAutHom h hr hε x = 1 ↔
      (x : SemiGL (HypIndex r ε) K).right = RingEquiv.refl K ∧
        ∃ c : Kˣ, (x : SemiGL (HypIndex r ε) K).left = GeneralLinearGroup.scalar _ c) ∧
    ∀ α : MulAut (hypPSU h r ε), orderOf α = 2 →
      ∃ (A : GL (HypIndex r ε) K) (σ : K ≃+* K)
        (hx : (⟨A, σ⟩ : SemiGL (HypIndex r ε) K) ∈ semilinearSimilitudes h r ε)
        (hA : A ∈ hypUnitary h r ε),
        semilinearAutHom h hr hε ⟨_, hx⟩ = α ∧
        (σ = RingEquiv.refl K ∨ ∀ c, σ c = h.bar c) ∧
        (σ = RingEquiv.refl K →
          orderOf (QuotientGroup.mk ⟨A, hA⟩ : hypUnitaryMod h r ε) = 2) ∧
        ((∀ c, σ c = h.bar c) → ∃ c : K, c ≠ 0 ∧
          (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
            (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar = c • 1) := by
  refine ⟨semilinearAutHom_apply h hr hε, semilinearAutHom_surjective h hr hε hp hn,
    semilinearAutHom_eq_one_iff h hr hε hn, fun α hα => ?_⟩
  obtain ⟨x₀, hx₀⟩ := semilinearAutHom_surjective h hr hε hp hn α
  obtain ⟨x, hxΦ, -, hxU⟩ := exists_unitary_rep h hr hε hn x₀
  rw [hx₀] at hxΦ
  obtain ⟨⟨A, σ⟩, hx⟩ := x
  change A ∈ hypUnitary h r ε at hxU
  have hsq : semilinearAutHom h hr hε (⟨⟨A, σ⟩, hx⟩ * ⟨⟨A, σ⟩, hx⟩) = 1 := by
    rw [map_mul, hxΦ, ← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hα])
  obtain ⟨hσσ, c, hc⟩ := (semilinearAutHom_eq_one_iff h hr hε hn _).mp hsq
  change σ * σ = RingEquiv.refl K at hσσ
  change A * glAut σ A = GeneralLinearGroup.scalar (HypIndex r ε) c at hc
  refine ⟨A, σ, hx, hxU, hxΦ, ringEquiv_eq_refl_or_bar h hσσ, fun hσ => ?_, fun hσ => ?_⟩
  · subst hσ
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hAA : A * A = GeneralLinearGroup.scalar (HypIndex r ε) c := by
      have h1 : glAut (RingEquiv.refl K) A = A :=
        congrArg (fun φ : MulAut (GL (HypIndex r ε) K) => φ A) (map_one glAut)
      rwa [h1] at hc
    have hcN : h.norm (c : K) = 1 := by
      have hU := mul_mem hxU hxU
      rw [hAA, mem_hypUnitary, GeneralLinearGroup.coe_scalar, scalar_gram] at hU
      have h2 := congrFun (congrFun hU (.inl ⟨0, hr⟩)) (hypPartner (.inl ⟨0, hr⟩))
      simpa [hypGram_apply] using h2
    refine orderOf_eq_prime ?_ ?_
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, pow_two]
      exact ⟨c, hcN, pow_zero c, by rw [Subgroup.coe_mul, hAA]⟩
    · intro h1
      rw [QuotientGroup.eq_one_iff] at h1
      obtain ⟨c', -, -, hc'⟩ := h1
      have hΦ1 := (semilinearAutHom_eq_one_iff h hr hε hn ⟨⟨A, RingEquiv.refl K⟩, hx⟩).mpr
        ⟨rfl, c', hc'⟩
      rw [hxΦ] at hΦ1
      rw [hΦ1, orderOf_one] at hα
      exact absurd hα (by norm_num)
  · have hmap : (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map σ =
        (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar :=
      Matrix.ext fun i j => hσ _
    refine ⟨c, c.ne_zero, ?_⟩
    have h1 := congrArg (fun g : GL (HypIndex r ε) K =>
      (g : Matrix (HypIndex r ε) (HypIndex r ε) K)) hc
    simp only [Units.val_mul, coe_glAut, GeneralLinearGroup.coe_scalar, hmap] at h1
    rw [h1, scalar_apply, smul_one_eq_diagonal]

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
