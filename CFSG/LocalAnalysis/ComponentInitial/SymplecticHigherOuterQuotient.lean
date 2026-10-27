module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherTransport
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import Mathlib.GroupTheory.Commutator.Basic

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Matrix Subgroup SymplecticFlag CFSG.Assembly.LowTwoRank

open scoped commutatorElement

variable {r : ℕ} {K : Type} [Field K]

theorem conjAut_statedSp (g : StatedSp r K) :
    conjAut r K ⟨g, statedSp_le_gsp g.2⟩ = MulAut.conj (proj r K g) := by
  ext x
  obtain ⟨h, rfl⟩ := proj_surjective x
  rw [conjAut_proj, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  rfl

theorem spLinearAutGroup_eq_range : spLinearAutGroup r K = (conjAut r K).range := by
  rw [spLinearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]

theorem mem_spLinearAutGroup_iff {x : MulAut (StatedProj (StatedSp r K))} :
    x ∈ spLinearAutGroup r K ↔ ∃ A : gsp r K, conjAut r K A = x := by
  rw [spLinearAutGroup_eq_range, MonoidHom.mem_range]

theorem conjAut_mul_fieldAut_mul (A B : gsp r K) (σ τ : K ≃+* K) :
    conjAut r K A * fieldAut r K σ * (conjAut r K B * fieldAut r K τ) =
      conjAut r K (A * gspFieldMap σ B) * fieldAut r K (σ * τ) := by
  calc conjAut r K A * fieldAut r K σ * (conjAut r K B * fieldAut r K τ)
      _ = conjAut r K A * (fieldAut r K σ * conjAut r K B * (fieldAut r K σ)⁻¹) *
          (fieldAut r K σ * fieldAut r K τ) := by group
      _ = _ := by rw [fieldAut_mul_conjAut_mul_inv, ← map_mul, ← map_mul]

theorem mem_spSemilinearAutGroup_iff {x : MulAut (StatedProj (StatedSp r K))} :
    x ∈ spSemilinearAutGroup r K ↔
      ∃ (A : gsp r K) (σ : K ≃+* K), x = conjAut r K A * fieldAut r K σ := by
  constructor
  · intro hx
    let T : Subgroup (MulAut (StatedProj (StatedSp r K))) :=
      { carrier := {x | ∃ (A : gsp r K) (σ : K ≃+* K), x = conjAut r K A * fieldAut r K σ}
        mul_mem' := by
          rintro _ _ ⟨A, σ, rfl⟩ ⟨B, τ, rfl⟩
          exact ⟨_, _, conjAut_mul_fieldAut_mul A B σ τ⟩
        one_mem' := ⟨1, 1, by rw [map_one, map_one, one_mul]⟩
        inv_mem' := by
          rintro _ ⟨A, σ, rfl⟩
          refine ⟨gspFieldMap σ⁻¹ A⁻¹, σ⁻¹, ?_⟩
          rw [← fieldAut_mul_conjAut_mul_inv]
          simp only [_root_.mul_inv_rev, map_inv]
          group }
    have hle : spSemilinearAutGroup r K ≤ T := by
      rw [spSemilinearAutGroup, Subgroup.closure_le]
      rintro _ (hD | ⟨σ, rfl⟩)
      · obtain ⟨A, rfl⟩ := mem_spLinearAutGroup_iff.mp hD
        exact ⟨A, 1, by rw [map_one, mul_one]⟩
      · exact ⟨1, σ, by rw [map_one, one_mul]⟩
    exact hle hx
  · rintro ⟨A, σ, rfl⟩
    exact mul_mem (spLinearAutGroup_le_spSemilinearAutGroup (conjAut_mem_spLinearAutGroup A))
      (fieldAut_mem_spSemilinearAutGroup σ)

theorem standard_outer_quotient [Finite K] (hr : 1 ≤ r) :
    (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range ≤
      spLinearAutGroup r K ∧
    (Subgroup.subgroupOf
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range
      (spSemilinearAutGroup r K)).Normal ∧
    ((spLinearAutGroup r K).subgroupOf (spSemilinearAutGroup r K)).Normal ∧
    (∀ a ∈ spLinearAutGroup r K, ∀ b ∈ spLinearAutGroup r K, a * b * a⁻¹ * b⁻¹ ∈
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range) ∧
    (∃ g ∈ spSemilinearAutGroup r K, ∀ x ∈ spSemilinearAutGroup r K,
      ∃ k : ℤ, g ^ k * x ∈ spLinearAutGroup r K) ∧
    ⁅⁅spSemilinearAutGroup r K, spSemilinearAutGroup r K⁆,
        ⁅spSemilinearAutGroup r K, spSemilinearAutGroup r K⁆⁆ ≤
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range := by
  classical
  have : NeZero r := ⟨by omega⟩
  set I := (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range
    with hI
  set D := spLinearAutGroup r K with hD
  set E := spSemilinearAutGroup r K with hE
  have hID : I ≤ D := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨g, rfl⟩ := proj_surjective x
    rw [← conjAut_statedSp]
    exact conjAut_mem_spLinearAutGroup _
  have hInorm : ∀ φ : MulAut (StatedProj (StatedSp r K)), ∀ i ∈ I, φ * i * φ⁻¹ ∈ I := by
    rintro φ _ ⟨x, rfl⟩
    refine ⟨φ x, ?_⟩
    ext z
    simp [MulAut.conj_apply]
  have hDnormE : ∀ e ∈ E, ∀ d ∈ D, e * d * e⁻¹ ∈ D := by
    intro e he d hd
    obtain ⟨A, σ, rfl⟩ := mem_spSemilinearAutGroup_iff.mp he
    obtain ⟨B, rfl⟩ := mem_spLinearAutGroup_iff.mp hd
    have h : conjAut r K A * fieldAut r K σ * conjAut r K B * (conjAut r K A * fieldAut r K σ)⁻¹ =
        conjAut r K A * (fieldAut r K σ * conjAut r K B * (fieldAut r K σ)⁻¹) *
          (conjAut r K A)⁻¹ := by group
    rw [h, fieldAut_mul_conjAut_mul_inv, ← map_inv, ← map_mul, ← map_mul]
    exact conjAut_mem_spLinearAutGroup _
  have hnormal : ∀ H : Subgroup (MulAut (StatedProj (StatedSp r K))),
      (∀ x ∈ E, ∀ h ∈ H, x * h * x⁻¹ ∈ H) → (H.subgroupOf E).Normal := fun H hH =>
    ⟨fun a ha g => by
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      simpa using hH g g.2 a ha⟩
  have hDI : ∀ a ∈ D, ∀ b ∈ D, a * b * a⁻¹ * b⁻¹ ∈ I := by
    intro a ha b hb
    obtain ⟨A, rfl⟩ := mem_spLinearAutGroup_iff.mp ha
    obtain ⟨B, rfl⟩ := mem_spLinearAutGroup_iff.mp hb
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    have hker : A * B * A⁻¹ * B⁻¹ ∈ (multiplier r K).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
        mul_comm (multiplier r K A)]
      group
    rw [ker_multiplier, Subgroup.mem_subgroupOf] at hker
    have hC : A * B * A⁻¹ * B⁻¹ = ⟨((⟨_, hker⟩ : StatedSp r K) : GL (Fin r ⊕ Fin r) K),
        statedSp_le_gsp hker⟩ := rfl
    rw [hC, conjAut_statedSp]
    exact ⟨_, rfl⟩
  obtain ⟨p, k, hp, hk⟩ : ∃ (p : ℕ) (k : ℕ+), p.Prime ∧ Nat.card K = p ^ (k : ℕ) := by
    have := Fintype.ofFinite K
    obtain ⟨p, -, k, hp, hk⟩ := FiniteField.card' K
    exact ⟨p, k, hp, by rw [Nat.card_eq_fintype_card, hk]⟩
  obtain ⟨φ, -, -, hφ, -⟩ := finite_field_automorphism_fixed_field_cardinality hp k.pos hk
  have hcyc : ∀ σ : K ≃+* K, ∃ m : ℤ, φ ^ m = σ := fun σ =>
    Subgroup.mem_zpowers_iff.mp (hφ ▸ Subgroup.mem_top σ)
  have hcomm : ∀ σ τ : K ≃+* K, σ * τ = τ * σ := by
    intro σ τ
    obtain ⟨a, rfl⟩ := hcyc σ
    obtain ⟨b, rfl⟩ := hcyc τ
    exact zpow_mul_comm φ a b
  have hED : ∃ g ∈ E, ∀ x ∈ E, ∃ k : ℤ, g ^ k * x ∈ D := by
    refine ⟨fieldAut r K φ, fieldAut_mem_spSemilinearAutGroup φ, fun x hx => ?_⟩
    obtain ⟨A, σ, rfl⟩ := mem_spSemilinearAutGroup_iff.mp hx
    obtain ⟨m, rfl⟩ := hcyc σ
    refine ⟨-m, ?_⟩
    have h : fieldAut r K φ ^ (-m) * (conjAut r K A * fieldAut r K (φ ^ m)) =
        fieldAut r K (φ ^ (-m)) * conjAut r K A * (fieldAut r K (φ ^ (-m)))⁻¹ := by
      rw [map_zpow, map_zpow]
      group
    rw [h, fieldAut_mul_conjAut_mul_inv]
    exact conjAut_mem_spLinearAutGroup _
  have hEE : ⁅E, E⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨A, σ, rfl⟩ := mem_spSemilinearAutGroup_iff.mp hx
    obtain ⟨B, τ, rfl⟩ := mem_spSemilinearAutGroup_iff.mp hy
    rw [commutatorElement_def]
    have h : conjAut r K A * fieldAut r K σ * (conjAut r K B * fieldAut r K τ) *
        (conjAut r K A * fieldAut r K σ)⁻¹ * (conjAut r K B * fieldAut r K τ)⁻¹ =
        conjAut r K A * fieldAut r K σ * (conjAut r K B * fieldAut r K τ) *
          (conjAut r K B * fieldAut r K τ * (conjAut r K A * fieldAut r K σ))⁻¹ := by group
    rw [h, conjAut_mul_fieldAut_mul, conjAut_mul_fieldAut_mul, hcomm τ σ,
      show ∀ a b c : MulAut (StatedProj (StatedSp r K)), a * c * (b * c)⁻¹ = a * b⁻¹ from
        fun a b c => by group]
    exact mul_mem (conjAut_mem_spLinearAutGroup _) (inv_mem (conjAut_mem_spLinearAutGroup _))
  have hDD : ⁅D, D⁆ ≤ I := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact hDI a ha b hb
  exact ⟨hID, hnormal I fun x _ i hi => hInorm x i hi, hnormal D hDnormE, hDI, hED,
    (Subgroup.commutator_mono hEE hEE).trans hDD⟩

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
