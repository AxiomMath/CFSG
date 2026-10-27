module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Alpha
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAlpha

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard
open scoped Matrix

variable {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  {H : Subgroup (GL ι K)} {e : rankTwoQuot A ≃* StatedProj H}

section Diag

variable [CharP K 2] {E₁ E₂ : Matrix ι ι K} {h11 : E₁ * E₁ = 0} {h22 : E₂ * E₂ = 0}
  {φ₁ φ₂ : Multiplicative K →* G}

omit [CharP K 2] in
theorem coe_unipGL_mul_unipGL (h12 : E₁ * E₂ = 0) (s t : K) :
    ((unipGL E₁ h11 s * unipGL E₂ h22 t : GL ι K) : Matrix ι ι K) = 1 + s • E₁ + t • E₂ := by
  rw [Units.val_mul, coe_unipGL, coe_unipGL]
  simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, h12, smul_zero, add_zero]

theorem unipGL_mul_unipGL_sq (h12 : E₁ * E₂ = 0) (h21 : E₂ * E₁ = 0) (s t : K) :
    (unipGL E₁ h11 s * unipGL E₂ h22 t) ^ 2 = 1 := by
  apply Units.ext
  rw [pow_two, Units.val_mul, coe_unipGL_mul_unipGL h12, Units.val_one]
  have hT : (s • E₁ + t • E₂) * (s • E₁ + t • E₂) = 0 := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, h11, h12, h21,
      h22, smul_zero, add_zero]
  rw [add_assoc, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, hT, add_zero,
    add_assoc, matrix_add_self, add_zero]

omit [CharP K 2] in
theorem actsByScalar_of_conj_unipGL (hZ : Odd (Nat.card (center ↥A))) {E : Matrix ι ι K}
    {hE : E * E = 0} {φ : Multiplicative K →* G}
    (hφ : ∀ t : K, φ (Multiplicative.ofAdd t) ^ 2 = 1 ∧
      Represents e (φ (Multiplicative.ofAdd t)) (unipGL E hE t))
    {a : G} {X : GL ι K} (ha : Represents e a X) {l : K}
    (hX : (X : Matrix ι ι K) * E * ((X⁻¹ : GL ι K) : Matrix ι ι K) = l • E) :
    ActsByScalar φ a l := fun t => by
  have h1 : Represents e (a * φ (Multiplicative.ofAdd t) * a⁻¹) (unipGL E hE (l * t)) := by
    have h := (hφ t).2.conj ha
    have heq : X * unipGL E hE t * X⁻¹ = unipGL E hE (l * t) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_unipGL, coe_unipGL, Matrix.mul_add, Matrix.mul_one,
        Matrix.add_mul, Units.mul_inv, Matrix.mul_smul, Matrix.smul_mul, hX, smul_smul,
        mul_comm t]
    rwa [heq] at h
  have h2 : (a * φ (Multiplicative.ofAdd t) * a⁻¹) ^ 2 ^ 1 = 1 := by
    rw [pow_one, conj_pow, (hφ t).1, mul_one, mul_inv_cancel]
  exact eq_of_represents hZ h1 (hφ (l * t)).2 h2 (k' := 1) (by rw [pow_one]; exact (hφ (l * t)).1)

theorem eq_one_of_sq_mul_scalar [Nonempty ι] {U : GL ι K} {c : Kˣ} (hU : U ^ 2 = 1)
    (hUc : (U * Matrix.GeneralLinearGroup.scalar ι c) ^ 2 = 1) : c = 1 := by
  have hcomm : Commute U (Matrix.GeneralLinearGroup.scalar ι c) :=
    (Matrix.GeneralLinearGroup.scalar_commute c U).symm
  rw [hcomm.mul_pow, hU, one_mul, ← map_pow] at hUc
  have hc2 : c ^ 2 = 1 := by
    apply Units.ext
    have h4 := congrArg (fun N : GL ι K => (N : Matrix ι ι K)) hUc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_one] at h4
    have h5 : Matrix.scalar ι ((c ^ 2 : Kˣ) : K) = Matrix.scalar ι (1 : K) := by
      rw [h4]; exact (Matrix.scalar_apply (1 : K)).trans Matrix.diagonal_one |>.symm
    rw [Matrix.scalar_inj] at h5
    exact h5
  have h3 : ((c : K) - 1) ^ 2 = 0 := by
    have h4 := congrArg Units.val hc2
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h4
    rw [sub_sq, h4, mul_one, CharTwo.two_eq_zero, zero_mul, sub_zero, one_pow,
      CharTwo.add_self_eq_zero]
  exact Units.ext (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h3))

variable (hZ : Odd (Nat.card (center ↥A))) (h12 : E₁ * E₂ = 0) (h21 : E₂ * E₁ = 0)
  (hφ₁ : ∀ t : K, φ₁ (Multiplicative.ofAdd t) ^ 2 = 1 ∧
    Represents e (φ₁ (Multiplicative.ofAdd t)) (unipGL E₁ h11 t))
  (hφ₂ : ∀ t : K, φ₂ (Multiplicative.ofAdd t) ^ 2 = 1 ∧
    Represents e (φ₂ (Multiplicative.ofAdd t)) (unipGL E₂ h22 t))

omit [CharP K 2] in
include hZ h12 h21 hφ₁ hφ₂ in
theorem commute_diag (s t : Multiplicative K) : Commute (φ₁ s) (φ₂ t) := by
  have h := commute_of_represents hZ (hφ₁ (Multiplicative.toAdd s)).2
    (hφ₂ (Multiplicative.toAdd t)).2 (hφ₂ (Multiplicative.toAdd t)).1 (Units.ext (by
      rw [Units.val_mul, Units.val_mul, coe_unipGL, coe_unipGL]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
        Matrix.mul_smul, h12, h21, smul_zero, add_zero]
      abel))
  rwa [ofAdd_toAdd, ofAdd_toAdd] at h

omit [CharP K 2] in
include hZ h12 h21 hφ₁ hφ₂ in
theorem mem_sup_diag_iff {y : G} :
    y ∈ φ₁.range ⊔ φ₂.range ↔
      ∃ s t : K, y = φ₁ (Multiplicative.ofAdd s) * φ₂ (Multiplicative.ofAdd t) := by
  rw [← MonoidHom.noncommCoprod_range φ₁ φ₂ (commute_diag hZ h12 h21 hφ₁ hφ₂)]
  constructor
  · rintro ⟨⟨s, t⟩, rfl⟩
    exact ⟨Multiplicative.toAdd s, Multiplicative.toAdd t, by
      rw [MonoidHom.noncommCoprod_apply, ofAdd_toAdd, ofAdd_toAdd]⟩
  · rintro ⟨s, t, rfl⟩
    exact ⟨⟨Multiplicative.ofAdd s, Multiplicative.ofAdd t⟩, by
      rw [MonoidHom.noncommCoprod_apply]⟩

omit [CharP K 2] in
include hZ h12 h21 hφ₁ hφ₂ in
theorem represents_diag (s t : K) :
    (φ₁ (Multiplicative.ofAdd s) * φ₂ (Multiplicative.ofAdd t)) ^ 2 = 1 ∧
      Represents e (φ₁ (Multiplicative.ofAdd s) * φ₂ (Multiplicative.ofAdd t))
        (unipGL E₁ h11 s * unipGL E₂ h22 t) := by
  refine ⟨?_, (hφ₁ s).2.mul (hφ₂ t).2⟩
  rw [(commute_diag hZ h12 h21 hφ₁ hφ₂ _ _).mul_pow, (hφ₁ s).1, (hφ₂ t).1, one_mul]

include hZ h12 h21 hφ₁ hφ₂ in
theorem eq_of_diag_eq (hE₂0 : E₂ ≠ 0) (hind : ∀ a b : K, a • E₁ + b • E₂ = 0 → a = 0 ∧ b = 0)
    {s t s' t' : K}
    (h : φ₁ (Multiplicative.ofAdd s) * φ₂ (Multiplicative.ofAdd t) =
      φ₁ (Multiplicative.ofAdd s') * φ₂ (Multiplicative.ofAdd t')) : s = s' ∧ t = t' := by
  have hne : Nonempty ι := by
    by_contra hι
    have : IsEmpty ι := not_nonempty_iff.mp hι
    exact hE₂0 (Subsingleton.elim _ _)
  have h1 := (represents_diag hZ h12 h21 hφ₁ hφ₂ s t).2
  have h2 := (represents_diag hZ h12 h21 hφ₁ hφ₂ s' t').2
  rw [← h] at h2
  obtain ⟨c, hc⟩ := h1.exists_scalar h2
  have hsq : ∀ s t : K, (unipGL E₁ h11 s * unipGL E₂ h22 t) ^ 2 = 1 :=
    unipGL_mul_unipGL_sq h12 h21
  have hc1 : c = 1 := eq_one_of_sq_mul_scalar (hsq s t) (by rw [← hc]; exact hsq s' t')
  rw [hc1, map_one, mul_one] at hc
  have h3 := congrArg (fun N : GL ι K => (N : Matrix ι ι K)) hc
  simp only [coe_unipGL_mul_unipGL h12] at h3
  have h4 : (s' - s) • E₁ + (t' - t) • E₂ = 0 := by
    rw [sub_smul, sub_smul]
    have h5 := congrArg (· - (1 + s • E₁ + t • E₂)) h3
    simp only [sub_self] at h5
    rw [← h5]
    abel
  obtain ⟨h6, h7⟩ := hind _ _ h4
  exact ⟨(sub_eq_zero.mp h6).symm, (sub_eq_zero.mp h7).symm⟩

include hZ h12 h21 hφ₁ hφ₂ in
theorem deltaNormal_diag_of {p : G} {M : GL ι K} (hpM : Represents e p M) (hM2 : M ^ 2 = 1)
    (hME : (M : Matrix ι ι K) = 1 + E₁ + E₂)
    (hcent : ∀ X ∈ H, X * M = M * X →
      (X : Matrix ι ι K) * E₁ = E₁ * X ∧ (X : Matrix ι ι K) * E₂ = E₂ * X) :
    DeltaNormal A p (φ₁.range ⊔ φ₂.range) := by
  have hmem := fun y => mem_sup_diag_iff (y := y) hZ h12 h21 hφ₁ hφ₂
  have hcJ : ∀ x ∈ A ⊓ centralizer ({p} : Set G), ∀ y ∈ φ₁.range ⊔ φ₂.range, x * y = y * x := by
    intro x hx y hy
    obtain ⟨hxA, hxp⟩ := mem_inf.mp hx
    obtain ⟨X, hX⟩ := exists_represents e hxA
    have hXM : X * M = M * X := Units.ext (by
      rw [Units.val_mul, Units.val_mul]
      exact hX.mul_comm_of_commute hpM hM2 (mem_centralizer_singleton_iff.mp hxp))
    obtain ⟨hX1, hX2⟩ := hcent X hX.2.1 hXM
    obtain ⟨s, t, rfl⟩ := (hmem y).mp hy
    have h := represents_diag hZ h12 h21 hφ₁ hφ₂ s t
    exact (commute_of_represents hZ hX h.2 h.1 (Units.ext (by
      rw [Units.val_mul X, Units.val_mul _ X, coe_unipGL_mul_unipGL h12]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
        Matrix.mul_smul, Matrix.smul_mul, hX1, hX2]))).symm.symm
  refine ⟨?_, fun x hx => ?_, fun y => ?_, fun y hy => ?_⟩
  · intro y hy
    obtain ⟨s, t, rfl⟩ := (hmem y).mp hy
    have h := represents_diag hZ h12 h21 hφ₁ hφ₂ s t
    refine mem_inf.mpr ⟨h.2.1, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := commute_of_represents hZ hpM h.2 h.1 (Units.ext (by
      rw [Units.val_mul M, Units.val_mul _ M, coe_unipGL_mul_unipGL h12, hME]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
        Matrix.mul_smul, Matrix.smul_mul, h11, h12, h21, h22, smul_zero, add_zero]
      abel))
    exact h1.symm
  · refine mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · rw [hcJ x hx y hy, mul_inv_cancel_right]
      exact hy
    · have hy' : x * y * x⁻¹ * x = x * (x * y * x⁻¹) := (hcJ x hx _ hy).symm
      have h1 : y = x * y * x⁻¹ := by
        have h2 : x * y * x⁻¹ * x = x * y := by group
        rw [h2] at hy'
        exact mul_left_cancel hy'
      rw [h1]
      exact hy
  · obtain ⟨s, t, hst⟩ := (hmem y).mp y.2
    refine ⟨1, ?_⟩
    rw [pow_one]
    apply Subtype.ext
    rw [Subgroup.coe_pow, hst, (represents_diag hZ h12 h21 hφ₁ hφ₂ s t).1, Subgroup.coe_one]
  · refine mem_centralizer_iff.mpr fun d hd => ?_
    obtain ⟨b, hbA, rfl, hbp⟩ := hd
    have hdC : b * p * b⁻¹ ∈ A ⊓ centralizer ({p} : Set G) :=
      mem_inf.mpr ⟨mul_mem (mul_mem hbA hpM.1) (inv_mem hbA),
        mem_centralizer_singleton_iff.mpr hbp⟩
    exact hcJ _ hdC y hy

include hZ h12 h21 hφ₁ hφ₂ in
theorem deltaCentral_diag_of {p : G} (hp2 : p ^ 2 = 1) {M : GL ι K} (hpM : Represents e p M)
    (hM2 : orderOf M = 2)
    (hkey : ∀ X ∈ H, X * M = M * X →
      (∀ g ∈ H, g * M * g⁻¹ * M = M * (g * M * g⁻¹) → X * (g * M * g⁻¹) = g * M * g⁻¹ * X) →
      ∃ c : Kˣ, ∃ s t : K, X = unipGL E₁ h11 s * unipGL E₂ h22 t *
        Matrix.GeneralLinearGroup.scalar ι c) :
    DeltaCentral A p (φ₁.range ⊔ φ₂.range) := by
  intro x hx hxΔ hx2
  obtain ⟨hxA, hxp⟩ := mem_inf.mp hx
  have hxp' : x * p = p * x := mem_centralizer_singleton_iff.mp hxp
  obtain ⟨X, hX⟩ := exists_represents e hxA
  have hM2' : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
  have hXM : X * M = M * X := Units.ext (by
    rw [Units.val_mul, Units.val_mul]
    exact hX.mul_comm_of_commute hpM hM2' hxp')
  obtain ⟨c, s, t, hc⟩ := hkey X hX.2.1 hXM fun g hg hgM => by
    obtain ⟨b, hb⟩ := exists_represents_of_mem (e := e) hg
    have hrep := hpM.conj hb
    have hb2 : (b * p * b⁻¹) ^ 2 = 1 := by rw [conj_pow, hp2, mul_one, mul_inv_cancel]
    have hcomm : p * (b * p * b⁻¹) = b * p * b⁻¹ * p :=
      commute_of_represents hZ hpM hrep hb2 hgM.symm
    have hmem : b * p * b⁻¹ ∈ conjCommuting A p := ⟨b, hb.1, rfl, hcomm.symm⟩
    have hxc : b * p * b⁻¹ * x = x * (b * p * b⁻¹) := mem_centralizer_iff.mp hxΔ _ hmem
    have hgM2 : (g * M * g⁻¹) ^ 2 = 1 := by rw [conj_pow, hM2', mul_one, mul_inv_cancel]
    exact Units.ext (by
      rw [Units.val_mul, Units.val_mul]
      exact hX.mul_comm_of_commute hrep hgM2 hxc.symm)
  have h := represents_diag hZ h12 h21 hφ₁ hφ₂ s t
  have hY := hX.of_eq_mul_scalar h.2.2.1 hc
  obtain ⟨k, hk⟩ := hx2
  have hxy := eq_of_represents hZ hY h.2 hk (k' := 1) (by rw [pow_one]; exact h.1)
  rw [hxy]
  exact (mem_sup_diag_iff hZ h12 h21 hφ₁ hφ₂).mpr ⟨s, t, rfl⟩

include hZ h12 h21 hφ₁ hφ₂ in
theorem exists_actsByScalar_diag (hE₁0 : E₁ ≠ 0) (hE₂0 : E₂ ≠ 0)
    (hsep : ∀ X ∈ H, (∀ s t : K, (X : Matrix ι ι K) * E₁ * ((X⁻¹ : GL ι K) : Matrix ι ι K) =
        s • E₁ + t • E₂ → t = 0) ∧
      (∀ s t : K, (X : Matrix ι ι K) * E₂ * ((X⁻¹ : GL ι K) : Matrix ι ι K) =
        s • E₁ + t • E₂ → s = 0))
    {a : G} (haA : a ∈ A) (han : a ∈ normalizer ((φ₁.range ⊔ φ₂.range : Subgroup G) : Set G)) :
    ∃ l m : K, l ≠ 0 ∧ m ≠ 0 ∧ ActsByScalar φ₁ a l ∧ ActsByScalar φ₂ a m := by
  classical
  have hne : Nonempty ι := by
    by_contra hι
    have : IsEmpty ι := not_nonempty_iff.mp hι
    exact hE₁0 (Subsingleton.elim _ _)
  obtain ⟨X, hX⟩ := exists_represents e haA
  have hmem := fun y => mem_sup_diag_iff (y := y) hZ h12 h21 hφ₁ hφ₂
  have hconj : ∀ {E : Matrix ι ι K} {hE : E * E = 0} {φ : Multiplicative K →* G},
      (∀ t : K, φ (Multiplicative.ofAdd t) ^ 2 = 1 ∧
        Represents e (φ (Multiplicative.ofAdd t)) (unipGL E hE t)) →
      φ (Multiplicative.ofAdd 1) ∈ φ₁.range ⊔ φ₂.range →
      ∃ s t : K, (X : Matrix ι ι K) * E * ((X⁻¹ : GL ι K) : Matrix ι ι K) = s • E₁ + t • E₂ := by
    intro E hE φ hφ hφ1
    have hm := (mem_normalizer_iff.mp han _).mp hφ1
    obtain ⟨s, t, hst⟩ := (hmem _).mp hm
    have h1 := (hφ 1).2.conj hX
    have h2 := (represents_diag hZ h12 h21 hφ₁ hφ₂ s t).2
    rw [← hst] at h2
    obtain ⟨c, hc⟩ := h1.exists_scalar h2
    have hU2 : (X * unipGL E hE 1 * X⁻¹) ^ 2 = 1 := by
      rw [conj_pow, unipGL_sq, mul_one, mul_inv_cancel]
    have hsq : (unipGL E₁ h11 s * unipGL E₂ h22 t) ^ 2 = 1 := unipGL_mul_unipGL_sq h12 h21 s t
    have hc1 : c = 1 := eq_one_of_sq_mul_scalar hU2 (by rw [← hc]; exact hsq)
    rw [hc1, map_one, mul_one] at hc
    refine ⟨s, t, ?_⟩
    have h3 := congrArg (fun N : GL ι K => (N : Matrix ι ι K)) hc
    simp only [Units.val_mul, coe_unipGL, coe_unipGL_mul_unipGL h12, one_smul, Matrix.mul_add,
      Matrix.mul_one, Matrix.add_mul, Units.mul_inv] at h3
    rw [add_assoc] at h3
    exact add_left_cancel h3.symm
  obtain ⟨s₁, t₁, h1⟩ := hconj hφ₁ (mem_sup_left ⟨_, rfl⟩)
  obtain ⟨s₂, t₂, h2⟩ := hconj hφ₂ (mem_sup_right ⟨_, rfl⟩)
  have ht₁ := (hsep X hX.2.1).1 s₁ t₁ h1
  have hs₂ := (hsep X hX.2.1).2 s₂ t₂ h2
  rw [ht₁, zero_smul, add_zero] at h1
  rw [hs₂, zero_smul, zero_add] at h2
  have hnz : ∀ {E : Matrix ι ι K} {l : K}, E ≠ 0 →
      (X : Matrix ι ι K) * E * ((X⁻¹ : GL ι K) : Matrix ι ι K) = l • E → l ≠ 0 := by
    intro E l hE0 hXE hl
    rw [hl, zero_smul] at hXE
    apply hE0
    calc E = ((X⁻¹ : GL ι K) : Matrix ι ι K) * ((X : Matrix ι ι K) * E *
          ((X⁻¹ : GL ι K) : Matrix ι ι K)) * X := by
          simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
          rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      _ = 0 := by rw [hXE, Matrix.mul_zero, Matrix.zero_mul]
  exact ⟨s₁, t₂, hnz hE₁0 h1, hnz hE₂0 h2, actsByScalar_of_conj_unipGL hZ hφ₁ hX h1,
    actsByScalar_of_conj_unipGL hZ hφ₂ hX h2⟩

include hZ h12 h21 hφ₁ hφ₂ in
theorem regularOn_autDiagonal_of [Finite K] (hE₁0 : E₁ ≠ 0) (hE₂0 : E₂ ≠ 0)
    (hind : ∀ a b : K, a • E₁ + b • E₂ = 0 → a = 0 ∧ b = 0)
    (hinj₁ : Function.Injective φ₁) (hinj₂ : Function.Injective φ₂)
    (hsep : ∀ X ∈ H, (∀ s t : K, (X : Matrix ι ι K) * E₁ * ((X⁻¹ : GL ι K) : Matrix ι ι K) =
        s • E₁ + t • E₂ → t = 0) ∧
      (∀ s t : K, (X : Matrix ι ι K) * E₂ * ((X⁻¹ : GL ι K) : Matrix ι ι K) =
        s • E₁ + t • E₂ → s = 0))
    (htorus : ∀ l m : K, l ≠ 0 → m ≠ 0 → ∃ d ∈ H,
      (d : Matrix ι ι K) * E₁ * ((d⁻¹ : GL ι K) : Matrix ι ι K) = l • E₁ ∧
        (d : Matrix ι ι K) * E₂ * ((d⁻¹ : GL ι K) : Matrix ι ι K) = m • E₂) :
    RegularOn A (φ₁.range ⊔ φ₂.range)
        {j | j ∈ φ₁.range ⊔ φ₂.range ∧ j ∉ φ₁.range ∧ j ∉ φ₂.range} ∧
      AutDiagonal A (φ₁.range ⊔ φ₂.range) φ₁.range φ₂.range (Nat.card K - 1) := by
  classical
  set J := φ₁.range ⊔ φ₂.range with hJdef
  have hmem := fun y => mem_sup_diag_iff (y := y) hZ h12 h21 hφ₁ hφ₂
  have hcomm := commute_diag hZ h12 h21 hφ₁ hφ₂
  have hφ0 : ∀ {φ : Multiplicative K →* G}, Function.Injective φ →
      ∀ t : K, φ (Multiplicative.ofAdd t) = 1 → t = 0 := fun {φ} hinj t h => by
    have h1 := hinj (h.trans (map_one φ).symm)
    exact congrArg Multiplicative.toAdd h1
  have hmemU : ∀ s t : K, φ₁ (Multiplicative.ofAdd s) * φ₂ (Multiplicative.ofAdd t) ∈ φ₁.range →
      t = 0 := fun s t ⟨r, hr⟩ => by
    have h1 : φ₁ (Multiplicative.ofAdd (Multiplicative.toAdd r)) * φ₂ (Multiplicative.ofAdd 0) =
        φ₁ (Multiplicative.ofAdd s) * φ₂ (Multiplicative.ofAdd t) := by
      rw [ofAdd_toAdd, hr, ofAdd_zero, map_one, mul_one]
    exact (eq_of_diag_eq hZ h12 h21 hφ₁ hφ₂ hE₂0 hind h1).2.symm
  have hmemW : ∀ s t : K, φ₁ (Multiplicative.ofAdd s) * φ₂ (Multiplicative.ofAdd t) ∈ φ₂.range →
      s = 0 := fun s t ⟨r, hr⟩ => by
    have h1 : φ₁ (Multiplicative.ofAdd 0) * φ₂ (Multiplicative.ofAdd (Multiplicative.toAdd r)) =
        φ₁ (Multiplicative.ofAdd s) * φ₂ (Multiplicative.ofAdd t) := by
      rw [ofAdd_toAdd, hr, ofAdd_zero, map_one, one_mul]
    exact (eq_of_diag_eq hZ h12 h21 hφ₁ hφ₂ hE₂0 hind h1).1.symm
  have hact : ∀ {a : G} {l m : K}, ActsByScalar φ₁ a l → ActsByScalar φ₂ a m → ∀ s t : K,
      a * (φ₁ (Multiplicative.ofAdd s) * φ₂ (Multiplicative.ofAdd t)) * a⁻¹ =
        φ₁ (Multiplicative.ofAdd (l * s)) * φ₂ (Multiplicative.ofAdd (m * t)) :=
    fun {a l m} h1 h2 s t => by
      rw [← h1 s, ← h2 t]
      group
  have hnorm : ∀ {a : G} {l m : K}, l ≠ 0 → m ≠ 0 → ActsByScalar φ₁ a l →
      ActsByScalar φ₂ a m → a ∈ normalizer (J : Set G) :=
    fun {a l m} hl hm h1 h2 => mem_normalizer_iff.mpr fun y => by
      rw [hmem, hmem]
      constructor
      · rintro ⟨s, t, rfl⟩
        exact ⟨l * s, m * t, hact h1 h2 s t⟩
      · rintro ⟨s, t, hst⟩
        refine ⟨l⁻¹ * s, m⁻¹ * t, ?_⟩
        have h3 := hact (h1.inv hl) (h2.inv hm) s t
        rw [inv_inv] at h3
        rw [← h3, ← hst]
        group
  have hlift : ∀ l m : K, l ≠ 0 → m ≠ 0 →
      ∃ a ∈ A, ActsByScalar φ₁ a l ∧ ActsByScalar φ₂ a m := fun l m hl hm => by
    obtain ⟨d, hdH, hd1, hd2⟩ := htorus l m hl hm
    obtain ⟨a, ha⟩ := exists_represents_of_mem (e := e) hdH
    exact ⟨a, ha.1, actsByScalar_of_conj_unipGL hZ hφ₁ ha hd1,
      actsByScalar_of_conj_unipGL hZ hφ₂ ha hd2⟩
  have hcent1 : ∀ {φ : Multiplicative K →* G} {a : G}, ActsByScalar φ a 1 →
      a ∈ centralizer (φ.range : Set G) := fun {φ a} h => mem_centralizer_iff.mpr fun y hy => by
    obtain ⟨s, rfl⟩ := hy
    have h1 := h (Multiplicative.toAdd s)
    rw [one_mul, ofAdd_toAdd] at h1
    calc φ s * a = a * φ s * a⁻¹ * a := by rw [h1]
      _ = a * φ s := by group
  have hcent : ∀ {a : G} {l m : K}, ActsByScalar φ₁ a l → ActsByScalar φ₂ a m →
      (a ∈ centralizer (J : Set G) ↔ l = 1 ∧ m = 1) := fun {a l m} h1 h2 => by
    constructor
    · intro hc
      have e1 := mem_centralizer_iff.mp hc _ (mem_sup_left (⟨Multiplicative.ofAdd 1, rfl⟩ :
        φ₁ (Multiplicative.ofAdd 1) ∈ φ₁.range))
      have e2 := mem_centralizer_iff.mp hc _ (mem_sup_right (⟨Multiplicative.ofAdd 1, rfl⟩ :
        φ₂ (Multiplicative.ofAdd 1) ∈ φ₂.range))
      have f1 : a * φ₁ (Multiplicative.ofAdd 1) * a⁻¹ = φ₁ (Multiplicative.ofAdd 1) := by
        rw [← e1]; group
      have f2 : a * φ₂ (Multiplicative.ofAdd 1) * a⁻¹ = φ₂ (Multiplicative.ofAdd 1) := by
        rw [← e2]; group
      rw [h1 1, mul_one] at f1
      rw [h2 1, mul_one] at f2
      exact ⟨congrArg Multiplicative.toAdd (hinj₁ f1), congrArg Multiplicative.toAdd (hinj₂ f2)⟩
    · rintro ⟨rfl, rfl⟩
      refine mem_centralizer_iff.mpr fun y hy => ?_
      obtain ⟨s, t, rfl⟩ := (hmem y).mp hy
      have h3 := hact h1 h2 s t
      rw [one_mul, one_mul] at h3
      calc φ₁ (Multiplicative.ofAdd s) * φ₂ (Multiplicative.ofAdd t) * a =
          a * (φ₁ (Multiplicative.ofAdd s) * φ₂ (Multiplicative.ofAdd t)) * a⁻¹ * a := by
            rw [h3]
        _ = a * (φ₁ (Multiplicative.ofAdd s) * φ₂ (Multiplicative.ofAdd t)) := by group
  have hscal : ∀ a : ↥(A ⊓ normalizer (J : Set G)),
      ∃ lm : K × K, lm.1 ≠ 0 ∧ lm.2 ≠ 0 ∧ ActsByScalar φ₁ a lm.1 ∧ ActsByScalar φ₂ a lm.2 :=
    fun a => by
      obtain ⟨l, m, hl, hm, h1, h2⟩ := exists_actsByScalar_diag hZ h12 h21 hφ₁ hφ₂ hE₁0 hE₂0
        hsep (mem_inf.mp a.2).1 (mem_inf.mp a.2).2
      exact ⟨(l, m), hl, hm, h1, h2⟩
  choose μ hμ1 hμ2 hμa hμb using hscal
  have hμmul1 : ∀ a b, (μ (a * b)).1 = (μ a).1 * (μ b).1 := fun a b =>
    ActsByScalar.eq hinj₁ (hμa (a * b)) ((hμa a).mul (hμa b))
  have hμmul2 : ∀ a b, (μ (a * b)).2 = (μ a).2 * (μ b).2 := fun a b =>
    ActsByScalar.eq hinj₂ (hμb (a * b)) ((hμb a).mul (hμb b))
  let μu : ↥(A ⊓ normalizer (J : Set G)) →* Kˣ × Kˣ :=
    { toFun := fun a => (Units.mk0 (μ a).1 (hμ1 a), Units.mk0 (μ a).2 (hμ2 a))
      map_one' := Prod.ext (Units.ext (ActsByScalar.eq hinj₁ (hμa 1) fun t => by simp))
        (Units.ext (ActsByScalar.eq hinj₂ (hμb 1) fun t => by simp))
      map_mul' := fun a b => Prod.ext (Units.ext (hμmul1 a b)) (Units.ext (hμmul2 a b)) }
  have hμu1 : ∀ a, (((μu a).1 : Kˣ) : K) = (μ a).1 := fun _ => rfl
  have hμu2 : ∀ a, (((μu a).2 : Kˣ) : K) = (μ a).2 := fun _ => rfl
  have hS : ∀ j, j ∈ J ∧ j ∉ φ₁.range ∧ j ∉ φ₂.range →
      ∃ s t : K, s ≠ 0 ∧ t ≠ 0 ∧
        j = φ₁ (Multiplicative.ofAdd s) * φ₂ (Multiplicative.ofAdd t) := by
    rintro j ⟨hj, hjU, hjW⟩
    obtain ⟨s, t, rfl⟩ := (hmem j).mp hj
    refine ⟨s, t, fun hs => hjW ?_, fun ht => hjU ?_, rfl⟩
    · rw [hs, ofAdd_zero, map_one, one_mul]
      exact ⟨_, rfl⟩
    · rw [ht, ofAdd_zero, map_one, mul_one]
      exact ⟨_, rfl⟩
  refine ⟨⟨fun j hj j' hj' => ?_, fun a ha j hj haj => ?_⟩, ?_, ?_⟩
  · obtain ⟨s, t, hs, ht, rfl⟩ := hS j hj
    obtain ⟨s', t', hs', ht', rfl⟩ := hS j' hj'
    obtain ⟨a, haA, h1, h2⟩ := hlift (s' * s⁻¹) (t' * t⁻¹) (mul_ne_zero hs' (inv_ne_zero hs))
      (mul_ne_zero ht' (inv_ne_zero ht))
    refine ⟨a, mem_inf.mpr ⟨haA, hnorm (mul_ne_zero hs' (inv_ne_zero hs))
      (mul_ne_zero ht' (inv_ne_zero ht)) h1 h2⟩, ?_⟩
    rw [hact h1 h2, mul_assoc, inv_mul_cancel₀ hs, mul_one, mul_assoc, inv_mul_cancel₀ ht,
      mul_one]
  · obtain ⟨s, t, hs, ht, rfl⟩ := hS j hj
    have h1 := hμa ⟨a, ha⟩
    have h2 := hμb ⟨a, ha⟩
    rw [hact h1 h2] at haj
    obtain ⟨e1, e2⟩ := eq_of_diag_eq hZ h12 h21 hφ₁ hφ₂ hE₂0 hind haj
    have f1 : (μ ⟨a, ha⟩).1 * s = 1 * s := by rw [one_mul]; exact e1
    have f2 : (μ ⟨a, ha⟩).2 * t = 1 * t := by rw [one_mul]; exact e2
    exact (hcent h1 h2).mpr ⟨mul_right_cancel₀ hs f1, mul_right_cancel₀ ht f2⟩
  · have hker : (A ⊓ centralizer (J : Set G)).subgroupOf (A ⊓ normalizer (J : Set G)) =
        μu.ker := by
      ext a
      rw [mem_subgroupOf, MonoidHom.mem_ker, Prod.ext_iff, Units.ext_iff, Units.ext_iff, hμu1,
        hμu2, Prod.fst_one, Prod.snd_one, Units.val_one, mem_inf]
      exact ⟨fun h => (hcent (hμa a) (hμb a)).mp h.2,
        fun h => ⟨(mem_inf.mp a.2).1, (hcent (hμa a) (hμb a)).mpr h⟩⟩
    have hsurj : Function.Surjective μu := fun lm => by
      obtain ⟨a, haA, h1, h2⟩ := hlift (lm.1 : K) (lm.2 : K) lm.1.ne_zero lm.2.ne_zero
      refine ⟨⟨a, mem_inf.mpr ⟨haA, hnorm lm.1.ne_zero lm.2.ne_zero h1 h2⟩⟩, Prod.ext
        (Units.ext ?_) (Units.ext ?_)⟩
      · rw [hμu1]
        exact ActsByScalar.eq hinj₁ (hμa _) h1
      · rw [hμu2]
        exact ActsByScalar.eq hinj₂ (hμb _) h2
    rw [Subgroup.relIndex, hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj,
      Subgroup.card_top, Nat.card_prod, Nat.card_units]
  · obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
    obtain ⟨y₁, hy₁A, hy₁a, hy₁b⟩ := hlift 1 (g : K) one_ne_zero g.ne_zero
    obtain ⟨y₂, hy₂A, hy₂a, hy₂b⟩ := hlift (g : K) 1 g.ne_zero one_ne_zero
    refine ⟨y₁, mem_inf.mpr ⟨hy₁A, hnorm one_ne_zero g.ne_zero hy₁a hy₁b⟩, y₂,
      mem_inf.mpr ⟨hy₂A, hnorm g.ne_zero one_ne_zero hy₂a hy₂b⟩, hcent1 hy₁a, hcent1 hy₂b,
      fun a ha => ?_⟩
    have hpow : ∀ {y : G} {l m : K}, ActsByScalar φ₁ y l → ActsByScalar φ₂ y m → ∀ k : ℕ,
        ActsByScalar φ₁ (y ^ k) (l ^ k) ∧ ActsByScalar φ₂ (y ^ k) (m ^ k) :=
      fun {y l m} h1 h2 k => by
        induction k with
        | zero => exact ⟨fun t => by simp, fun t => by simp⟩
        | succ k ih =>
          rw [pow_succ, pow_succ, pow_succ]
          exact ⟨ih.1.mul h1, ih.2.mul h2⟩
    obtain ⟨k₁, hk₁⟩ := (mem_powers_iff_mem_zpowers (y := (μu ⟨a, ha⟩).2)).mpr (hg _)
    obtain ⟨k₂, hk₂⟩ := (mem_powers_iff_mem_zpowers (y := (μu ⟨a, ha⟩).1)).mpr (hg _)
    refine ⟨k₁, k₂, ?_⟩
    obtain ⟨p₁a, p₁b⟩ := hpow hy₁a hy₁b k₁
    obtain ⟨p₂a, p₂b⟩ := hpow hy₂a hy₂b k₂
    have hgk : ∀ k : ℕ, (g : K) ^ k ≠ 0 := fun k => pow_ne_zero _ g.ne_zero
    have q₁ := ((p₁a.mul p₂a).inv (by rw [one_pow, one_mul]; exact hgk k₂)).mul (hμa ⟨a, ha⟩)
    have q₂ := ((p₁b.mul p₂b).inv (by rw [one_pow, mul_one]; exact hgk k₁)).mul (hμb ⟨a, ha⟩)
    refine (hcent q₁ q₂).mpr ⟨?_, ?_⟩
    · rw [← hμu1, ← hk₂, Units.val_pow_eq_pow_val, one_pow, one_mul,
        inv_mul_cancel₀ (hgk k₂)]
    · rw [← hμu2, ← hk₁, Units.val_pow_eq_pow_val, one_pow, mul_one,
        inv_mul_cancel₀ (hgk k₁)]

end Diag

end CFSG.ComponentClassification.RankTwoClassical
