module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismTransport
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix Subgroup

open scoped commutatorElement

variable {K : Type*} [Field K] {n : ℕ}

theorem conjAut_toGL (g : SpecialLinearGroup (Fin n) K) :
    conjAut n K (SpecialLinearGroup.toGL g) = MulAut.conj (proj n K g) := by
  ext x
  obtain ⟨h, rfl⟩ := proj_surjective n K x
  rw [conjAut_proj, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  rfl

theorem linearAutGroup_eq_range : linearAutGroup n K = (conjAut n K).range := by
  rw [linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]

theorem mem_linearAutGroup_iff {x : MulAut (projectiveSL n K)} :
    x ∈ linearAutGroup n K ↔ ∃ A : GL (Fin n) K, conjAut n K A = x := by
  rw [linearAutGroup_eq_range, MonoidHom.mem_range]

theorem conjAut_mul_fieldAut_mul (A B : GL (Fin n) K) (σ τ : K ≃+* K) :
    conjAut n K A * fieldAut n K σ * (conjAut n K B * fieldAut n K τ) =
      conjAut n K (A * GeneralLinearGroup.map (σ : K →+* K) B) * fieldAut n K (σ * τ) := by
  have htrans := standard_automorphism_transport (K := K) (n := n)
  calc conjAut n K A * fieldAut n K σ * (conjAut n K B * fieldAut n K τ)
      _ = conjAut n K A * (fieldAut n K σ * conjAut n K B * (fieldAut n K σ)⁻¹) *
          (fieldAut n K σ * fieldAut n K τ) := by group
      _ = _ := by rw [htrans.2.2.1, htrans.2.1, htrans.1]

theorem mem_semilinearAutGroup_iff {x : MulAut (projectiveSL n K)} :
    x ∈ semilinearAutGroup n K ↔
      ∃ (A : GL (Fin n) K) (σ : K ≃+* K), x = conjAut n K A * fieldAut n K σ := by
  have htrans := standard_automorphism_transport (K := K) (n := n)
  constructor
  · intro hx
    let S : Subgroup (MulAut (projectiveSL n K)) :=
      { carrier := {x | ∃ (A : GL (Fin n) K) (σ : K ≃+* K), x = conjAut n K A * fieldAut n K σ}
        mul_mem' := by
          rintro _ _ ⟨A, σ, rfl⟩ ⟨B, τ, rfl⟩
          exact ⟨_, _, conjAut_mul_fieldAut_mul A B σ τ⟩
        one_mem' := ⟨1, 1, by rw [map_one, map_one, one_mul]⟩
        inv_mem' := by
          rintro _ ⟨A, σ, rfl⟩
          refine ⟨GeneralLinearGroup.map ((σ⁻¹ : K ≃+* K) : K →+* K) A⁻¹, σ⁻¹, ?_⟩
          rw [← htrans.2.2.1]
          simp only [_root_.mul_inv_rev, map_inv]
          group }
    have hle : semilinearAutGroup n K ≤ S := by
      rw [semilinearAutGroup, Subgroup.closure_le]
      rintro _ (hD | ⟨σ, rfl⟩)
      · obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hD
        exact ⟨A, 1, by rw [map_one, mul_one]⟩
      · exact ⟨1, σ, by rw [map_one, one_mul]⟩
    exact hle hx
  · rintro ⟨A, σ, rfl⟩
    exact mul_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup A))
      (fieldAut_mem_semilinearAutGroup σ)

theorem dualAut_mul_mul_dualAut_mem {e : MulAut (projectiveSL n K)}
    (he : e ∈ semilinearAutGroup n K) : dualAut n K * e * dualAut n K ∈ semilinearAutGroup n K := by
  have htrans := standard_automorphism_transport (K := K) (n := n)
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp he
  have h : dualAut n K * (conjAut n K A * fieldAut n K σ) * dualAut n K =
      dualAut n K * conjAut n K A * dualAut n K * (dualAut n K * fieldAut n K σ * dualAut n K) := by
    calc dualAut n K * (conjAut n K A * fieldAut n K σ) * dualAut n K
        _ = dualAut n K * conjAut n K A * 1 * fieldAut n K σ * dualAut n K := by group
        _ = dualAut n K * conjAut n K A * (dualAut n K * dualAut n K) * fieldAut n K σ *
            dualAut n K := by rw [htrans.2.2.2.1]
        _ = _ := by group
  rw [h, htrans.2.2.2.2.1, htrans.2.2.2.2.2.1]
  exact mem_semilinearAutGroup_iff.mpr ⟨_, _, rfl⟩

theorem mem_or_mul_dualAut_mem {x : MulAut (projectiveSL n K)} (hx : x ∈ standardAutGroup n K) :
    x ∈ semilinearAutGroup n K ∨ x * dualAut n K ∈ semilinearAutGroup n K := by
  have hδδ := (standard_automorphism_transport (K := K) (n := n)).2.2.2.1
  set E := semilinearAutGroup n K
  set δ := dualAut n K
  let T : Subgroup (MulAut (projectiveSL n K)) :=
    { carrier := {x | x ∈ E ∨ x * δ ∈ E}
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (mul_mem hx hy)
        · exact Or.inr (by rw [mul_assoc]; exact mul_mem hx hy)
        · refine Or.inr ?_
          have h : x * y * δ = x * δ * (δ * y * δ) := by
            rw [show x * δ * (δ * y * δ) = x * (δ * δ) * y * δ by group, hδδ, mul_one]
          rw [h]
          exact mul_mem hx (dualAut_mul_mul_dualAut_mem hy)
        · refine Or.inl ?_
          have h : x * y = x * δ * (δ * (y * δ) * δ) := by
            rw [show x * δ * (δ * (y * δ) * δ) = x * (δ * δ) * y * (δ * δ) by group, hδδ,
              mul_one, mul_one]
          rw [h]
          exact mul_mem hx (dualAut_mul_mul_dualAut_mem hy)
      one_mem' := Or.inl (one_mem E)
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (inv_mem hx)
        · refine Or.inr ?_
          have h : x⁻¹ * δ = δ * (x * δ)⁻¹ * δ := by group
          rw [h]
          exact dualAut_mul_mul_dualAut_mem (inv_mem hx) }
  have hle : standardAutGroup n K ≤ T := by
    rw [standardAutGroup, Subgroup.closure_le]
    rintro _ (hE | rfl)
    · exact Or.inl hE
    · exact Or.inr (by rw [hδδ]; exact one_mem E)
  exact hle hx

theorem standard_outer_quotients [Finite K] :
    (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ linearAutGroup n K ∧
    ((MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range.subgroupOf
      (standardAutGroup n K)).Normal ∧
    ((linearAutGroup n K).subgroupOf (standardAutGroup n K)).Normal ∧
    ((semilinearAutGroup n K).subgroupOf (standardAutGroup n K)).Normal ∧
    (∀ a ∈ linearAutGroup n K, ∀ b ∈ linearAutGroup n K,
      a * b * a⁻¹ * b⁻¹ ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range) ∧
    (∃ g ∈ semilinearAutGroup n K, ∀ x ∈ semilinearAutGroup n K,
      ∃ k : ℤ, g ^ k * x ∈ linearAutGroup n K) ∧
    (∃ g ∈ standardAutGroup n K, ∀ x ∈ standardAutGroup n K,
      ∃ k : ℤ, g ^ k * x ∈ semilinearAutGroup n K) ∧
    ((semilinearAutGroup n K).subgroupOf (standardAutGroup n K)).index ≤ 2 ∧
    ⁅⁅semilinearAutGroup n K, semilinearAutGroup n K⁆,
        ⁅semilinearAutGroup n K, semilinearAutGroup n K⁆⁆ ≤
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ∧
    ⁅⁅⁅standardAutGroup n K, standardAutGroup n K⁆, ⁅standardAutGroup n K, standardAutGroup n K⁆⁆,
        ⁅⁅standardAutGroup n K, standardAutGroup n K⁆,
          ⁅standardAutGroup n K, standardAutGroup n K⁆⁆⁆ ≤
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  classical
  have htrans := standard_automorphism_transport (K := K) (n := n)
  have hδδ : dualAut n K * dualAut n K = 1 := htrans.2.2.2.1
  set I := (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range with hI
  set D := linearAutGroup n K with hD
  set E := semilinearAutGroup n K with hE
  set R := standardAutGroup n K with hR
  set δ := dualAut n K with hδ
  have hID : I ≤ D := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨g, rfl⟩ := proj_surjective n K x
    rw [← conjAut_toGL]
    exact conjAut_mem_linearAutGroup _
  have hInorm : ∀ φ : MulAut (projectiveSL n K), ∀ i ∈ I, φ * i * φ⁻¹ ∈ I := by
    rintro φ _ ⟨x, rfl⟩
    refine ⟨φ x, ?_⟩
    ext z
    simp [MulAut.conj_apply]
  have hDnormE : ∀ e ∈ E, ∀ d ∈ D, e * d * e⁻¹ ∈ D := by
    intro e he d hd
    obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp he
    obtain ⟨B, rfl⟩ := mem_linearAutGroup_iff.mp hd
    have h : conjAut n K A * fieldAut n K σ * conjAut n K B * (conjAut n K A * fieldAut n K σ)⁻¹ =
        conjAut n K A * (fieldAut n K σ * conjAut n K B * (fieldAut n K σ)⁻¹) *
          (conjAut n K A)⁻¹ := by group
    rw [h, htrans.2.2.1, ← map_inv, ← map_mul, ← map_mul]
    exact conjAut_mem_linearAutGroup _
  have hDnormR : ∀ x ∈ R, ∀ d ∈ D, x * d * x⁻¹ ∈ D := by
    intro x hx d hd
    rcases mem_or_mul_dualAut_mem hx with hxE | hxE
    · exact hDnormE x hxE d hd
    · obtain ⟨B, rfl⟩ := mem_linearAutGroup_iff.mp hd
      have h : x * conjAut n K B * x⁻¹ =
          x * δ * (δ * conjAut n K B * δ) * (x * δ)⁻¹ := by
        rw [show x * δ * (δ * conjAut n K B * δ) * (x * δ)⁻¹ =
          x * (δ * δ) * conjAut n K B * x⁻¹ by group, hδδ, mul_one]
      rw [h, htrans.2.2.2.2.1]
      exact hDnormE _ hxE _ (conjAut_mem_linearAutGroup _)
  have hEnormR : ∀ x ∈ R, ∀ e ∈ E, x * e * x⁻¹ ∈ E := by
    intro x hx e he
    rcases mem_or_mul_dualAut_mem hx with hxE | hxE
    · exact mul_mem (mul_mem hxE he) (inv_mem hxE)
    · have h : x * e * x⁻¹ = x * δ * (δ * e * δ) * (x * δ)⁻¹ := by
        rw [show x * δ * (δ * e * δ) * (x * δ)⁻¹ = x * (δ * δ) * e * x⁻¹ by group, hδδ, mul_one]
      rw [h]
      exact mul_mem (mul_mem hxE (dualAut_mul_mul_dualAut_mem he)) (inv_mem hxE)
  have hnormal : ∀ H : Subgroup (MulAut (projectiveSL n K)),
      (∀ x ∈ R, ∀ h ∈ H, x * h * x⁻¹ ∈ H) → (H.subgroupOf R).Normal := fun H hH =>
    ⟨fun a ha g => by
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      simpa using hH g g.2 a ha⟩
  have hDI : ∀ a ∈ D, ∀ b ∈ D, a * b * a⁻¹ * b⁻¹ ∈ I := by
    intro a ha b hb
    obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp ha
    obtain ⟨B, rfl⟩ := mem_linearAutGroup_iff.mp hb
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    have hdet : GeneralLinearGroup.det (A * B * A⁻¹ * B⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (GeneralLinearGroup.det A)]
      group
    obtain ⟨g, hg⟩ : A * B * A⁻¹ * B⁻¹ ∈
        (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin n) K →*
          GL (Fin n) K).range := by
      rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
      exact hdet
    rw [← hg, conjAut_toGL]
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
    refine ⟨fieldAut n K φ, fieldAut_mem_semilinearAutGroup φ, fun x hx => ?_⟩
    obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp hx
    obtain ⟨m, rfl⟩ := hcyc σ
    refine ⟨-m, ?_⟩
    have h : fieldAut n K φ ^ (-m) * (conjAut n K A * fieldAut n K (φ ^ m)) =
        fieldAut n K (φ ^ (-m)) * conjAut n K A * (fieldAut n K (φ ^ (-m)))⁻¹ := by
      rw [map_zpow, map_zpow]
      group
    rw [h, htrans.2.2.1]
    exact conjAut_mem_linearAutGroup _
  have hRE : ∃ g ∈ R, ∀ x ∈ R, ∃ k : ℤ, g ^ k * x ∈ E := by
    refine ⟨δ, dualAut_mem_standardAutGroup, fun x hx => ?_⟩
    rcases mem_or_mul_dualAut_mem hx with hxE | hxE
    · exact ⟨0, by rwa [zpow_zero, one_mul]⟩
    · refine ⟨1, ?_⟩
      have h : δ ^ (1 : ℤ) * x = δ * (x * δ) * δ := by
        rw [zpow_one, show δ * (x * δ) * δ = δ * x * (δ * δ) by group, hδδ, mul_one]
      rw [h]
      exact dualAut_mul_mul_dualAut_mem hxE
  have hindex : (E.subgroupOf R).index ≤ 2 := by
    let δR : R := ⟨δ, dualAut_mem_standardAutGroup⟩
    let f : Bool → R ⧸ E.subgroupOf R := fun b => QuotientGroup.mk (if b then δR else 1)
    have hsurj : Function.Surjective f := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      rcases mem_or_mul_dualAut_mem x.2 with hxE | hxE
      · refine ⟨false, QuotientGroup.eq.mpr ?_⟩
        rw [Subgroup.mem_subgroupOf]
        simpa using hxE
      · refine ⟨true, QuotientGroup.eq.mpr ?_⟩
        rw [Subgroup.mem_subgroupOf]
        have hδinv : δ⁻¹ = δ := inv_eq_of_mul_eq_one_right hδδ
        have h : δ⁻¹ * (x : MulAut (projectiveSL n K)) = δ * (x * δ) * δ := by
          rw [hδinv, show δ * (x * δ) * δ = δ * x * (δ * δ) by group, hδδ, mul_one]
        simp only [ite_true, Subgroup.coe_mul, Subgroup.coe_inv, δR]
        rw [h]
        exact dualAut_mul_mul_dualAut_mem hxE
    have := Nat.card_le_card_of_surjective f hsurj
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
    exact this
  have hEE : ⁅E, E⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp hx
    obtain ⟨B, τ, rfl⟩ := mem_semilinearAutGroup_iff.mp hy
    rw [commutatorElement_def]
    have h : conjAut n K A * fieldAut n K σ * (conjAut n K B * fieldAut n K τ) *
        (conjAut n K A * fieldAut n K σ)⁻¹ * (conjAut n K B * fieldAut n K τ)⁻¹ =
        conjAut n K A * fieldAut n K σ * (conjAut n K B * fieldAut n K τ) *
          (conjAut n K B * fieldAut n K τ * (conjAut n K A * fieldAut n K σ))⁻¹ := by group
    rw [h, conjAut_mul_fieldAut_mul, conjAut_mul_fieldAut_mul, hcomm τ σ,
      show ∀ a b c : MulAut (projectiveSL n K), a * c * (b * c)⁻¹ = a * b⁻¹ from
        fun a b c => by group]
    exact mul_mem (conjAut_mem_linearAutGroup _) (inv_mem (conjAut_mem_linearAutGroup _))
  have hRR : ⁅R, R⁆ ≤ E := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    rcases mem_or_mul_dualAut_mem hx with hxE | hxE
    · rw [show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
      exact mul_mem hxE (hEnormR y hy _ (inv_mem hxE))
    rcases mem_or_mul_dualAut_mem hy with hyE | hyE
    · exact mul_mem (hEnormR x hx y hyE) (inv_mem hyE)
    · have h : x * y * x⁻¹ * y⁻¹ = x * δ * (δ * (y * δ * (x * δ)⁻¹) * δ) * (y * δ)⁻¹ := by
        rw [show x * δ * (δ * (y * δ * (x * δ)⁻¹) * δ) * (y * δ)⁻¹ =
          x * (δ * δ) * y * x⁻¹ * y⁻¹ by group, hδδ, mul_one]
      rw [h]
      exact mul_mem (mul_mem hxE (dualAut_mul_mul_dualAut_mem (mul_mem hyE (inv_mem hxE))))
        (inv_mem hyE)
  have hDD : ⁅D, D⁆ ≤ I := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact hDI a ha b hb
  have h2 : ⁅⁅E, E⁆, ⁅E, E⁆⁆ ≤ I := (Subgroup.commutator_mono hEE hEE).trans hDD
  have h3 : ⁅⁅⁅R, R⁆, ⁅R, R⁆⁆, ⁅⁅R, R⁆, ⁅R, R⁆⁆⁆ ≤ I :=
    (Subgroup.commutator_mono (Subgroup.commutator_mono hRR hRR)
      (Subgroup.commutator_mono hRR hRR)).trans h2
  exact ⟨hID, hnormal I fun x _ i hi => hInorm x i hi, hnormal D hDnormR, hnormal E hEnormR, hDI,
    hED, hRE, hindex, h2, h3⟩

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
