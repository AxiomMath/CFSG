module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTPFieldBasic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRecenterCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRecenter

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart linearFieldPart_eq
  exists_standard_form)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (blockSwapJ)
open CFSG.Quasithin (perfectCore)
open CFSG.RankThree.PartOne (linearSubfieldInclusion linearSubfieldInclusion_injective)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (fixedField)

variable {n : ℕ} {K : Type} [Field K] [Finite K]

variable (n K) in
@[expose] def TransvectionIntrinsicStdField : Prop :=
  ∀ σ : K ≃+* K, σ ≠ 1 → fieldAut n K σ ^ 2 = 1 →
    ∀ β : MulAut (projectiveSL n K), β ^ 2 = 1 → β ≠ 1 →
      ∀ (Γ : Type) [Group Γ] [Finite Γ] (φ₁ φ₂ : projectiveSL n K →* Γ),
        Function.Injective φ₁ → Function.Injective φ₂ →
          (perfectCore (autFixSubgroup (fieldAut n K σ))).map φ₁ =
            (perfectCore (autFixSubgroup β)).map φ₂ →
          ∀ y ∈ perfectCore (autFixSubgroup (fieldAut n K σ)), IsInvolutionClass 1 y →
            ∃ z : projectiveSL n K, IsInvolutionClass 1 z ∧ φ₂ z = φ₁ y

omit [Finite K] in
theorem transvectionIntrinsicStd_of_field (h0 : TransvectionIntrinsicStdField n K)
    (h1 : ∀ σ : K ≃+* K, σ ≠ 1 → (fieldAut n K σ * dualAut n K) ^ 2 = 1 →
      ∀ β : MulAut (projectiveSL n K), β ^ 2 = 1 → β ≠ 1 →
        ∀ (Γ : Type) [Group Γ] [Finite Γ] (φ₁ φ₂ : projectiveSL n K →* Γ),
          Function.Injective φ₁ → Function.Injective φ₂ →
            (perfectCore (autFixSubgroup (fieldAut n K σ * dualAut n K))).map φ₁ =
              (perfectCore (autFixSubgroup β)).map φ₂ →
            ∀ y ∈ perfectCore (autFixSubgroup (fieldAut n K σ * dualAut n K)),
              IsInvolutionClass 1 y →
                ∃ z : projectiveSL n K, IsInvolutionClass 1 z ∧ φ₂ z = φ₁ y) :
    TransvectionIntrinsicStd n K := by
  intro σ ε hσ hε hα β hβ2 hβ1 Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hXY y hy hyt
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · rw [pow_zero, mul_one] at hα hXY hy
    exact h0 σ hσ hα β hβ2 hβ1 Γ φ₁ φ₂ hφ₁ hφ₂ hXY y hy hyt
  · rw [pow_one] at hα hXY hy
    exact h1 σ hσ hα β hβ2 hβ1 Γ φ₁ φ₂ hφ₁ hφ₂ hXY y hy hyt

theorem sq_eq_one_of_fieldAut_sq (hn : 3 ≤ n) {σ : K ≃+* K} (h : fieldAut n K σ ^ 2 = 1) :
    σ ^ 2 = 1 := by
  have h1 := congrArg (linearFieldPart K hn) h
  rwa [map_pow, map_one, linearFieldPart_fieldAut hn] at h1

theorem four_le_card_of_fieldAut_sq {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n)
    {σ : K ≃+* K} (hσ : σ ≠ 1) (h : fieldAut n K σ ^ 2 = 1) : 4 ≤ Nat.card K := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h1
    · have h1 := Finite.one_lt_card (α := K)
      rw [hK, h0, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h1
  obtain ⟨hfe, -, -⟩ := even_linear_field_involution_descent hf hK hn 1 σ hσ
    (by rwa [map_one, one_mul])
  obtain ⟨m, hm⟩ := hfe
  have hm1 : 1 ≤ m := by omega
  rw [hK, hm, ← two_mul, pow_mul]
  calc 4 = 4 ^ 1 := by norm_num
    _ ≤ (2 ^ 2) ^ m := Nat.pow_le_pow_right (by norm_num) hm1

variable (n K) in
@[expose] def TwoCentralTransvection (Y : Subgroup (projectiveSL n K)) : Prop :=
  ∀ z (hz : z ∈ Y), z ≠ 1 → CentralizesSylow 2 (⟨z, hz⟩ : Y) → IsInvolutionClass 1 z

theorem exists_isInvolutionClass_one_of_map_eq {Γ : Type*} [Group Γ]
    {φ₁ φ₂ : projectiveSL n K →* Γ} (hφ₁ : Function.Injective φ₁)
    (hφ₂ : Function.Injective φ₂) {X Y : Subgroup (projectiveSL n K)}
    (hXY : X.map φ₁ = Y.map φ₂) (hY : TwoCentralTransvection n K Y) {y : projectiveSL n K}
    (hy : y ∈ X) (hy1 : y ≠ 1) (hyc : CentralizesSylow 2 (⟨y, hy⟩ : X)) :
    ∃ z : projectiveSL n K, IsInvolutionClass 1 z ∧ φ₂ z = φ₁ y := by
  have hr : (φ₁.comp X.subtype).range = (φ₂.comp Y.subtype).range := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype,
      Subgroup.range_subtype, hXY]
  obtain ⟨z, hz, hzc⟩ := exists_centralizesSylow_of_range_eq (p := 2)
    (ψ₁ := φ₁.comp X.subtype) (ψ₂ := φ₂.comp Y.subtype)
    (hφ₁.comp X.subtype_injective) (hφ₂.comp Y.subtype_injective) hr hyc
  refine ⟨z, hY z z.2 ?_ hzc, hz⟩
  intro h1
  apply hy1
  apply hφ₁
  have h2 : φ₂ (z : projectiveSL n K) = φ₁ y := hz
  rw [← h2, h1, map_one, map_one]

theorem TwoCentralTransvection.map_conjAut {Y : Subgroup (projectiveSL n K)}
    (hY : TwoCentralTransvection n K Y) (H : GL (Fin n) K) :
    TwoCentralTransvection n K (Y.map (conjAut n K H).toMonoidHom) := by
  intro z hz hz1 hzc
  have hr : (Y.map (conjAut n K H).toMonoidHom).subtype.range =
      ((conjAut n K H).toMonoidHom.comp Y.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.range_subtype]
  obtain ⟨z₀, hz₀, hz₀c⟩ := exists_centralizesSylow_of_range_eq (p := 2)
    (ψ₂ := (conjAut n K H).toMonoidHom.comp Y.subtype)
    (Subgroup.subtype_injective _) ((conjAut n K H).injective.comp Y.subtype_injective) hr hzc
  have hz₀' : conjAut n K H (z₀ : projectiveSL n K) = z := hz₀
  have hz₀1 : (z₀ : projectiveSL n K) ≠ 1 := by
    intro h1
    apply hz1
    rw [← hz₀', h1, map_one]
  rw [← hz₀']
  exact (hY _ z₀.2 hz₀1 hz₀c).conjAut H

theorem twoCentralTransvection_range_linearSubfieldInclusion [CharP K 2] (hn : 2 ≤ n)
    (k : Subfield K) :
    TwoCentralTransvection n K (linearSubfieldInclusion n k).range := by
  intro z hz hz1 hzc
  have hinj := linearSubfieldInclusion_injective (K := K) (n := n) (by omega) k
  have hr : (linearSubfieldInclusion n k).range.subtype.range =
      (linearSubfieldInclusion n k).range := Subgroup.range_subtype _
  obtain ⟨z₀, hz₀, hz₀c⟩ := exists_centralizesSylow_of_range_eq (p := 2)
    (Subgroup.subtype_injective _) hinj hr hzc
  have hz₀' : linearSubfieldInclusion n k z₀ = z := hz₀
  have hz₀1 : z₀ ≠ 1 := by
    intro h1
    apply hz1
    rw [← hz₀', h1, map_one]
  rw [← hz₀']
  exact isInvolutionClass_one_linearSubfieldInclusion hn
    (isInvolutionClass_one_of_centralizesSylow hn hz₀1 hz₀c)

theorem centralizesSylow_range_linearSubfieldInclusion [CharP K 2] (hn : 2 ≤ n) (k : Subfield K)
    {y : projectiveSL n K} (hy : y ∈ (linearSubfieldInclusion n k).range)
    (hyt : IsInvolutionClass 1 y) :
    CentralizesSylow 2 (⟨y, hy⟩ : (linearSubfieldInclusion n k).range) := by
  obtain ⟨y₀, rfl⟩ := hy
  have hinj := linearSubfieldInclusion_injective (K := K) (n := n) (by omega) k
  have hy₀ : IsInvolutionClass 1 y₀ := isInvolutionClass_one_of_linearSubfieldInclusion
    (by omega) hyt
  have hr : (linearSubfieldInclusion n k).range =
      (linearSubfieldInclusion n k).range.subtype.range := (Subgroup.range_subtype _).symm
  obtain ⟨c, hc, hcc⟩ := exists_centralizesSylow_of_range_eq (p := 2) hinj
    (Subgroup.subtype_injective _) hr (centralizesSylow_of_isInvolutionClass_one hn hy₀)
  have hc' : c = ⟨linearSubfieldInclusion n k y₀, ⟨y₀, rfl⟩⟩ := Subtype.ext hc
  rwa [hc'] at hcc

theorem centralizesSylow_perfectCore_fieldAut {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n)
    {σ : K ≃+* K} (hσ : σ ^ 2 = 1) {y : projectiveSL n K}
    (hy : y ∈ perfectCore (autFixSubgroup (fieldAut n K σ))) (hyt : IsInvolutionClass 1 y) :
    CentralizesSylow 2 (⟨y, hy⟩ : perfectCore (autFixSubgroup (fieldAut n K σ))) := by
  have := charP_two_of_card_eq_two_pow hK
  have hX := perfectCore_autFixSubgroup_fieldAut hK hn σ hσ
  have hy' : y ∈ (linearSubfieldInclusion n (fixedField K σ)).range := hX ▸ hy
  have hr : (linearSubfieldInclusion n (fixedField K σ)).range.subtype.range =
      (perfectCore (autFixSubgroup (fieldAut n K σ))).subtype.range := by
    rw [Subgroup.range_subtype, Subgroup.range_subtype, hX]
  obtain ⟨c, hc, hcc⟩ := exists_centralizesSylow_of_range_eq (p := 2)
    (Subgroup.subtype_injective _) (Subgroup.subtype_injective _) hr
    (centralizesSylow_range_linearSubfieldInclusion (by omega) _ hy' hyt)
  have hc' : c = ⟨y, hy⟩ := Subtype.ext hc
  rwa [hc'] at hcc

theorem twoCentralTransvection_perfectCore_field {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n)
    (A : GL (Fin n) K) {τ : K ≃+* K} (hτ : τ ≠ 1)
    (hβ : (conjAut n K A * fieldAut n K τ) ^ 2 = 1) :
    TwoCentralTransvection n K (perfectCore (autFixSubgroup (conjAut n K A * fieldAut n K τ))) := by
  have := charP_two_of_card_eq_two_pow hK
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h1
    · have h1 := Finite.one_lt_card (α := K)
      rw [hK, h0, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h1
  have hτ2 : τ ^ 2 = 1 := by
    have h := congrArg (linearFieldPart K hn) hβ
    rwa [map_pow, map_one, show conjAut n K A * fieldAut n K τ =
      conjAut n K A * fieldAut n K τ * dualAut n K ^ 0 by rw [pow_zero, mul_one],
      linearFieldPart_eq hn (Nat.zero_le 1)] at h
  obtain ⟨-, -, H, hH⟩ := even_linear_field_involution_descent hf hK hn A τ hτ hβ
  rw [hH, perfectCore_autFixSubgroup_conj, perfectCore_autFixSubgroup_fieldAut hK hn τ hτ2]
  exact (twoCentralTransvection_range_linearSubfieldInclusion (by omega) _).map_conjAut H

theorem exists_isInvolutionClass_one_of_map_perfectCore_eq_field {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) {σ : K ≃+* K} (hσ : σ ^ 2 = 1) (A : GL (Fin n) K)
    {τ : K ≃+* K} (hτ : τ ≠ 1) (hβ : (conjAut n K A * fieldAut n K τ) ^ 2 = 1) {Γ : Type*}
    [Group Γ] {φ₁ φ₂ : projectiveSL n K →* Γ} (hφ₁ : Function.Injective φ₁)
    (hφ₂ : Function.Injective φ₂)
    (hXY : (perfectCore (autFixSubgroup (fieldAut n K σ))).map φ₁ =
      (perfectCore (autFixSubgroup (conjAut n K A * fieldAut n K τ))).map φ₂)
    {y : projectiveSL n K} (hy : y ∈ perfectCore (autFixSubgroup (fieldAut n K σ)))
    (hyt : IsInvolutionClass 1 y) :
    ∃ z : projectiveSL n K, IsInvolutionClass 1 z ∧ φ₂ z = φ₁ y := by
  have := charP_two_of_card_eq_two_pow hK
  exact exists_isInvolutionClass_one_of_map_eq hφ₁ hφ₂ hXY
    (twoCentralTransvection_perfectCore_field hK hn A hτ hβ) hy (hyt.ne_one one_ne_zero)
    (centralizesSylow_perfectCore_fieldAut hK hn hσ hy hyt)

theorem map_perfectCore_fieldAut_ne_conjAut {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {σ : K ≃+* K} (hσ : σ ≠ 1) (hα : fieldAut n K σ ^ 2 = 1) (B : GL (Fin n) K)
    (hβ : conjAut n K B ^ 2 = 1) (hβ1 : conjAut n K B ≠ 1) {Γ : Type*} [Group Γ]
    {φ₁ φ₂ : projectiveSL n K →* Γ} (hφ₁ : Function.Injective φ₁)
    (hφ₂ : Function.Injective φ₂) :
    (perfectCore (autFixSubgroup (fieldAut n K σ))).map φ₁ ≠
      (perfectCore (autFixSubgroup (conjAut n K B))).map φ₂ := by
  have := charP_two_of_card_eq_two_pow hK
  have hq := four_le_card_of_fieldAut_sq hK (by omega) hσ hα
  have h := map_perfectCore_field_ne_inner hK hq hn 1 σ hσ (by rwa [map_one, one_mul]) B hβ hβ1
    hφ₁ hφ₂
  rwa [map_one, one_mul] at h

variable (n K) in
@[expose] def FieldCoreNeGraphFieldCore : Prop :=
  ∀ σ τ : K ≃+* K, σ ≠ 1 → σ ^ 2 = 1 → τ ≠ 1 → (fieldAut n K τ * dualAut n K) ^ 2 = 1 →
    ∀ (Γ : Type) [Group Γ] (φ₁ φ₂ : projectiveSL n K →* Γ), Function.Injective φ₁ →
      Function.Injective φ₂ →
        (perfectCore (autFixSubgroup (fieldAut n K σ))).map φ₁ ≠
          (perfectCore (autFixSubgroup (fieldAut n K τ * dualAut n K))).map φ₂

variable (n K) in
@[expose] def FieldCoreNeGraphCore : Prop :=
  ∀ σ : K ≃+* K, σ ≠ 1 → σ ^ 2 = 1 → ∀ C : GL (Fin n) K,
    ((C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r) →
    ∀ (Γ : Type) [Group Γ] (φ₁ φ₂ : projectiveSL n K →* Γ), Function.Injective φ₁ →
      Function.Injective φ₂ →
        (perfectCore (autFixSubgroup (fieldAut n K σ))).map φ₁ ≠
          (perfectCore (autFixSubgroup (conjAut n K C * dualAut n K))).map φ₂

theorem map_perfectCore_fieldAut_ne_graphField (hGF : FieldCoreNeGraphFieldCore n K) {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) {σ : K ≃+* K} (hσ1 : σ ≠ 1) (hσ : σ ^ 2 = 1)
    (A : GL (Fin n) K) {τ : K ≃+* K} (hτ : τ ≠ 1)
    (hβ : (conjAut n K A * fieldAut n K τ * dualAut n K) ^ 2 = 1) (Γ : Type) [Group Γ]
    {φ₁ φ₂ : projectiveSL n K →* Γ} (hφ₁ : Function.Injective φ₁)
    (hφ₂ : Function.Injective φ₂) :
    (perfectCore (autFixSubgroup (fieldAut n K σ))).map φ₁ ≠
      (perfectCore (autFixSubgroup (conjAut n K A * fieldAut n K τ * dualAut n K))).map φ₂ := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h1
    · have h1 := Finite.one_lt_card (α := K)
      rw [hK, h0, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h1
  obtain ⟨-, -, H, hH⟩ :=
    UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two hf hK hn A τ hτ hβ
  set α' := conjAut n K A * fieldAut n K τ * dualAut n K with hα'
  set β₀ := fieldAut n K τ * dualAut n K with hβ₀
  set ψ := conjAut n K H with hψ
  have hβ₀2 : β₀ ^ 2 = 1 := by
    have e1 : β₀ = ψ⁻¹ * α' * ψ := by rw [hH]; group
    calc β₀ ^ 2 = ψ⁻¹ * α' ^ 2 * ψ := by rw [e1, sq, sq]; group
      _ = 1 := by rw [hβ]; group
  rw [hH, perfectCore_autFixSubgroup_conj, Subgroup.map_map]
  exact hGF σ τ hσ1 hσ hτ hβ₀2 Γ φ₁ (φ₂.comp ψ.toMonoidHom) hφ₁ (hφ₂.comp ψ.injective)

theorem map_perfectCore_fieldAut_ne_graph (hG : FieldCoreNeGraphCore n K) {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) {σ : K ≃+* K} (hσ1 : σ ≠ 1) (hσ : σ ^ 2 = 1)
    (A : GL (Fin n) K) (hβ : (conjAut n K A * dualAut n K) ^ 2 = 1) (Γ : Type) [Group Γ]
    {φ₁ φ₂ : projectiveSL n K →* Γ} (hφ₁ : Function.Injective φ₁)
    (hφ₂ : Function.Injective φ₂) :
    (perfectCore (autFixSubgroup (fieldAut n K σ))).map φ₁ ≠
      (perfectCore (autFixSubgroup (conjAut n K A * dualAut n K))).map φ₂ := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h1
    · have h1 := Finite.one_lt_card (α := K)
      rw [hK, h0, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h1
  obtain ⟨-, ⟨H, C, -, hconj, hC⟩, -⟩ :=
    UnitaryHigher.even_linear_pure_graph_involution_normal_forms hf hK hn A hβ
  have hC' : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r := by
    rcases hC with ⟨h1, -⟩ | ⟨r, hr, hJ, -⟩
    · exact Or.inl h1
    · exact Or.inr ⟨r, hr, hJ⟩
  rw [hconj, perfectCore_autFixSubgroup_conj, Subgroup.map_map]
  exact hG σ hσ1 hσ C hC' Γ φ₁ (φ₂.comp (conjAut n K H).toMonoidHom) hφ₁
    (hφ₂.comp (conjAut n K H).injective)

theorem transvectionIntrinsicStdField_of_ne {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    (hGF : FieldCoreNeGraphFieldCore n K) (hG : FieldCoreNeGraphCore n K) :
    TransvectionIntrinsicStdField n K := by
  intro σ hσ1 hσ2 β hβ2 hβ1 Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hXY y hy hyt
  have hn3 : 3 ≤ n := by omega
  have hσ : σ ^ 2 = 1 := sq_eq_one_of_fieldAut_sq hn3 hσ2
  obtain ⟨τ, A, η, hη, rfl⟩ := exists_standard_form K n hn3 β
  rcases (by omega : η = 0 ∨ η = 1) with rfl | rfl
  · rw [pow_zero, mul_one] at hβ2 hβ1 hXY
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hβ2 hβ1 hXY
      exact absurd hXY (map_perfectCore_fieldAut_ne_conjAut hK hn hσ1 hσ2 A hβ2 hβ1 hφ₁ hφ₂)
    · exact exists_isInvolutionClass_one_of_map_perfectCore_eq_field hK hn3 hσ A hτ hβ2 hφ₁ hφ₂
        hXY hy hyt
  · rw [pow_one] at hβ2 hXY
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hβ2 hXY
      exact absurd hXY (map_perfectCore_fieldAut_ne_graph hG hK hn3 hσ1 hσ A hβ2 Γ hφ₁ hφ₂)
    · exact absurd hXY
        (map_perfectCore_fieldAut_ne_graphField hGF hK hn3 hσ1 hσ A hτ hβ2 Γ hφ₁ hφ₂)

end CFSG.SeitzReduction.LinearPilot
