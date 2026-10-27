module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseBTorus
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA

variable {r f p : ℕ} {K : Type} [Field K]

@[expose] noncomputable def herm (h : UnitaryFieldData r f K) (u v : Fin p → K) : K :=
  ∑ i, h.bar (u i) * v i

theorem herm_smul_smul (h : UnitaryFieldData r f K) (c c' : K) (u v : Fin p → K) :
    herm h (c • u) (c' • v) = h.bar c * c' * herm h u v := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem herm_mulVec (h : UnitaryFieldData r f K) {g : GL (Fin p) K}
    (hg : g ∈ primeFormUnitary h ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K))
    (u v : Fin p → K) :
    herm h ((g : Matrix (Fin p) (Fin p) K) *ᵥ u) ((g : Matrix (Fin p) (Fin p) K) *ᵥ v) =
      herm h u v := by
  rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one] at hg
  have h1 : (fun i => h.bar (((g : Matrix (Fin p) (Fin p) K) *ᵥ u) i)) =
      ((g : Matrix (Fin p) (Fin p) K).map h.bar) *ᵥ (fun i => h.bar (u i)) := by
    funext i
    exact RingHom.map_mulVec h.bar _ _ i
  change (fun i => h.bar (((g : Matrix (Fin p) (Fin p) K) *ᵥ u) i)) ⬝ᵥ
    ((g : Matrix (Fin p) (Fin p) K) *ᵥ v) = (fun i => h.bar (u i)) ⬝ᵥ v
  rw [h1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hg,
    Matrix.one_mulVec]


section Cycle

theorem gram_diagonal {ι : Type*} {σ : Equiv.Perm (Fin p)} (hcyc : σ.IsCycle)
    (hord : orderOf σ = p) (hp : p.Prime) (hp2 : p ≠ 2) (bar : K →+* K)
    (hbb : ∀ c, bar (bar c) = c) (Γ : Fin p → Fin p → K) (δ : Fin p → K)
    (hδ : ∀ a, bar (δ a) * δ a = 1)
    (R1 : ∀ a b, Γ a b = bar (δ a) * δ b * Γ (σ a) (σ b)) (dd : ι → Fin p → K)
    (R2 : ∀ a b, Γ a b ≠ 0 → ∀ t, bar (dd t a) * dd t b = 1)
    (R3 : ∀ a b, a ≠ b → ∃ t, dd t a ≠ dd t b) :
    (∀ a b, a ≠ b → Γ a b = 0) ∧ ∀ a b, Γ a a = Γ b b := by
  have hsupp : σ.support = Finset.univ := Finset.eq_univ_of_card _ (by
    rw [← hcyc.orderOf, hord, Fintype.card_fin])
  have hmove : ∀ x, σ x ≠ x := fun x => by
    have : x ∈ σ.support := by rw [hsupp]; exact Finset.mem_univ x
    exact Equiv.Perm.mem_support.1 this
  have hσp : σ ^ p = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hord] at this
  refine ⟨fun a b hab => ?_, fun a b => ?_⟩
  · by_contra hΓ
    have hstep : ∀ x y, Γ x y ≠ 0 → Γ (σ x) (σ y) ≠ 0 := fun x y hxy hz =>
      hxy (by rw [R1 x y, hz, mul_zero])
    have hiter : ∀ m : ℕ, Γ ((σ ^ m) a) ((σ ^ m) b) ≠ 0 := by
      intro m
      induction m with
      | zero => simpa using hΓ
      | succ m ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
        exact hstep _ _ ih
    obtain ⟨s, hs⟩ := hcyc.exists_pow_eq (hmove a) (hmove b)
    have hall : ∀ u, Γ u ((σ ^ s) u) ≠ 0 := by
      intro u
      obtain ⟨m, hm⟩ := hcyc.exists_pow_eq (hmove a) (hmove u)
      have h1 := hiter m
      have h2 : (σ ^ m) b = (σ ^ s) u := by
        rw [← hs, ← hm, ← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← pow_add, ← pow_add,
          add_comm]
      rw [h2, hm] at h1
      exact h1
    have hchar : ∀ t u, dd t ((σ ^ s) u) = (bar (dd t u))⁻¹ := by
      intro t u
      exact eq_inv_of_mul_eq_one_right (R2 _ _ (hall u) t)
    have hdd : ∀ t u, dd t ((σ ^ s) ((σ ^ s) u)) = dd t u := by
      intro t u
      rw [hchar t ((σ ^ s) u), hchar t u, map_inv₀, hbb, inv_inv]
    have hfix : ∀ u, (σ ^ s) ((σ ^ s) u) = u := by
      intro u
      by_contra hne
      obtain ⟨t, ht⟩ := R3 _ _ hne
      exact ht (hdd t u)
    have h1 : σ ^ (s + s) = 1 := by
      rw [hcyc.pow_eq_one_iff' (hmove a), pow_add, Equiv.Perm.mul_apply]
      exact hfix a
    have hdvd : p ∣ s + s := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one h1
    have hps : p ∣ s := by
      have h2 : p ∣ 2 * s := by rwa [two_mul]
      rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3) hp2
      · exact h3
    obtain ⟨k, rfl⟩ := hps
    apply hab
    rw [← hs, pow_mul, hσp, one_pow]
    rfl
  · have hdiag : ∀ x, Γ x x = Γ (σ x) (σ x) := fun x => by
      rw [R1 x x, hδ, one_mul]
    have hiter : ∀ m : ℕ, Γ ((σ ^ m) a) ((σ ^ m) a) = Γ a a := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, ← hdiag, ih]
    obtain ⟨m, hm⟩ := hcyc.exists_pow_eq (hmove a) (hmove b)
    rw [← hm, hiter m]

end Cycle


section Rescale

variable (h : UnitaryFieldData r f K)

theorem bar_herm_self (u : Fin p → K) : h.bar (herm h u u) = herm h u u := by
  simp only [herm, map_sum, map_mul, h.bar_bar]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

@[expose] def col (B : GL (Fin p) K) (j : Fin p) : Fin p → K :=
  (B : Matrix (Fin p) (Fin p) K) *ᵥ Pi.single j 1

theorem col_apply (B : GL (Fin p) K) (i j : Fin p) :
    col B j i = (B : Matrix (Fin p) (Fin p) K) i j := by
  simp [col, Matrix.mulVec_single_one]

theorem mulVec_conj_eq {B g X : GL (Fin p) K} (hX : B⁻¹ * g * B = X) (v : Fin p → K) :
    (g : Matrix (Fin p) (Fin p) K) *ᵥ ((B : Matrix (Fin p) (Fin p) K) *ᵥ v) =
      (B : Matrix (Fin p) (Fin p) K) *ᵥ ((X : Matrix (Fin p) (Fin p) K) *ᵥ v) := by
  have e : g * B = B * X := by
    rw [← hX]
    group
  have e' : (g : Matrix (Fin p) (Fin p) K) * (B : Matrix (Fin p) (Fin p) K) =
      (B : Matrix (Fin p) (Fin p) K) * (X : Matrix (Fin p) (Fin p) K) := by
    rw [← Units.val_mul, ← Units.val_mul, e]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e']

theorem mulVec_single_smul (M : Matrix (Fin p) (Fin p) K) (j : Fin p) (c : K) :
    M *ᵥ Pi.single j c = c • (M *ᵥ Pi.single j 1) := by
  rw [← Matrix.mulVec_smul]
  congr 1
  ext i
  by_cases hi : i = j <;> simp [Pi.single_apply, hi]

theorem mulVec_col_diag {B g : GL (Fin p) K} {d : Fin p → Kˣ}
    (hd : B⁻¹ * g * B = diagGL p K d) (j : Fin p) :
    (g : Matrix (Fin p) (Fin p) K) *ᵥ col B j = (d j : K) • col B j := by
  unfold col
  rw [mulVec_conj_eq hd, diagGL_mulVec_single, mulVec_single_smul, mul_one]

theorem mulVec_col_rot {B ŷ : GL (Fin p) K} {δ : Fin p → Kˣ}
    (hrot : B⁻¹ * ŷ * B = rotGL p K * diagGL p K δ) (j : Fin p) :
    (ŷ : Matrix (Fin p) (Fin p) K) *ᵥ col B j = (δ j : K) • col B (finRotate p j) := by
  unfold col
  rw [mulVec_conj_eq hrot, Units.val_mul, ← Matrix.mulVec_mulVec, diagGL_mulVec_single,
    rotGL_mulVec_single, mulVec_single_smul, mul_one]

end Rescale


section Main

variable (h : UnitaryFieldData r f K)

theorem conj_scalar_mul (c : Kˣ) (B g : GL (Fin p) K) :
    (GeneralLinearGroup.scalar (Fin p) c * B)⁻¹ * g * (GeneralLinearGroup.scalar (Fin p) c * B) =
      B⁻¹ * g * B := by
  have hs : ∀ x : GL (Fin p) K, GeneralLinearGroup.scalar (Fin p) c * x =
      x * GeneralLinearGroup.scalar (Fin p) c := scalar_comm c
  calc (GeneralLinearGroup.scalar (Fin p) c * B)⁻¹ * g * (GeneralLinearGroup.scalar (Fin p) c * B)
      = B⁻¹ * ((GeneralLinearGroup.scalar (Fin p) c)⁻¹ * g * GeneralLinearGroup.scalar (Fin p) c) *
          B := by group
    _ = B⁻¹ * g * B := by
      have hin : (GeneralLinearGroup.scalar (Fin p) c)⁻¹ * g * GeneralLinearGroup.scalar (Fin p) c =
          g := by
        rw [mul_assoc, ← hs g, inv_mul_cancel_left]
      rw [hin]


theorem exists_unitary_diag_basis [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    {Th : Subgroup (GL (Fin p) K)}
    (hThU : Th ≤ primeFormUnitary h ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K))
    {ŷ B : GL (Fin p) K} {ω : K}
    (hŷU : ŷ ∈ primeFormUnitary h ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K))
    (hωN : h.bar ω * ω = 1) {δ : Fin p → Kˣ}
    (hrot : B⁻¹ * ŷ * B = rotGL p K * diagGL p K δ)
    (hδ : ∀ j, (δ j : K) = 1 ∨ (δ j : K) = ω)
    (hdiag : ∀ g ∈ Th, ∃ d : Fin p → Kˣ, B⁻¹ * g * B = diagGL p K d)
    (hsep : ∀ i j : Fin p, i ≠ j → ∃ g ∈ Th,
      ((B⁻¹ * g * B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) i i ≠
        ((B⁻¹ * g * B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) j j) :
    ∃ B' : GL (Fin p) K,
      B' ∈ primeFormUnitary h ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) ∧
        DiagData Th ŷ B' := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set σ : Equiv.Perm (Fin p) := finRotate p with hσ
  have hp2' : 2 ≤ p := hp.two_le
  have hcyc : σ.IsCycle := isCycle_finRotate_of_le hp2'
  have hord : orderOf σ = p := by
    rw [hcyc.orderOf, hσ, support_finRotate_of_le hp2', Finset.card_univ, Fintype.card_fin]
  set Γ : Fin p → Fin p → K := fun i j => herm h (col B i) (col B j) with hΓ
  have hδN : ∀ a, h.bar (δ a : K) * (δ a : K) = 1 := by
    intro a
    rcases hδ a with h1 | h1
    · rw [h1, map_one, one_mul]
    · rw [h1]
      exact hωN
  have R1 : ∀ a b, Γ a b = h.bar (δ a : K) * (δ b : K) * Γ (σ a) (σ b) := by
    intro a b
    have := herm_mulVec h hŷU (col B a) (col B b)
    rw [mulVec_col_rot hrot a, mulVec_col_rot hrot b, herm_smul_smul] at this
    exact this.symm
  let dd : ↥Th → Fin p → K := fun t a =>
    ((B⁻¹ * (t : GL (Fin p) K) * B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) a a
  have hdd : ∀ (t : ↥Th) a, ((t : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *ᵥ col B a =
      dd t a • col B a := by
    intro t a
    obtain ⟨d, hd⟩ := hdiag t t.2
    have := mulVec_col_diag hd a
    have e : dd t a = (d a : K) := by
      show ((B⁻¹ * (t : GL (Fin p) K) * B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) a a = _
      rw [hd, diagGL_val, Matrix.diagonal_apply_eq]
    rw [e]
    exact this
  have R2 : ∀ a b, Γ a b ≠ 0 → ∀ t, h.bar (dd t a) * dd t b = 1 := by
    intro a b hab t
    have := herm_mulVec h (hThU t.2) (col B a) (col B b)
    rw [hdd t a, hdd t b, herm_smul_smul] at this
    exact mul_right_cancel₀ hab (by rw [one_mul]; exact this)
  have R3 : ∀ a b, a ≠ b → ∃ t : ↥Th, dd t a ≠ dd t b := by
    intro a b hab
    obtain ⟨g, hg, hne⟩ := hsep a b hab
    exact ⟨⟨g, hg⟩, hne⟩
  obtain ⟨hoff, hconst⟩ := gram_diagonal hcyc hord hp hp2 h.bar h.bar_bar Γ (fun a => (δ a : K))
    hδN R1 dd R2 R3
  set i0 : Fin p := ⟨0, hp.pos⟩ with hi0
  set a₀ : K := Γ i0 i0 with ha₀
  have hMat : ((B : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ * (B : Matrix (Fin p) (Fin p) K) =
      Matrix.diagonal (fun _ => a₀) := by
    ext i j
    rw [Matrix.mul_apply]
    have e : ∑ k, ((B : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ i k *
        (B : Matrix (Fin p) (Fin p) K) k j = Γ i j := by
      simp [hΓ, herm, col_apply, Matrix.transpose_apply, Matrix.map_apply]
    rw [e]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
      exact hconst i i0
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact hoff i j hij
  have hMunit : IsUnit (Matrix.diagonal (fun _ : Fin p => a₀)) := by
    rw [← hMat]
    exact ((Matrix.isUnit_transpose _).2
      ((Units.isUnit B).map (RingHom.mapMatrix h.bar))).mul (Units.isUnit B)
  have ha0 : a₀ ≠ 0 := by
    intro h0
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal, h0] at hMunit
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hMunit
    rw [zero_pow hp.ne_zero] at hMunit
    exact not_isUnit_zero hMunit
  have hbar0 : h.bar a₀ = a₀ := bar_herm_self h (col B i0)
  obtain ⟨u, hu⟩ := h.normHom_surjective ⟨a₀⁻¹, (h.mem_fixedField).2 (by rw [map_inv₀, hbar0])⟩
  have hu' : u * h.bar u = a₀⁻¹ := by
    have := congrArg Subtype.val hu
    rw [UnitaryFieldData.coe_normHom] at this
    exact this
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hu'
    exact (inv_ne_zero ha0) hu'.symm
  refine ⟨GeneralLinearGroup.scalar (Fin p) (Units.mk0 u hu0) * B, ?_, ?_⟩
  · rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one]
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have e : ∀ k, ((GeneralLinearGroup.scalar (Fin p) (Units.mk0 u hu0) * B : GL (Fin p) K) :
        Matrix (Fin p) (Fin p) K) k j = u * (B : Matrix (Fin p) (Fin p) K) k j := by
      intro k
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_mul]
      rfl
    have e' : ∀ k, ((GeneralLinearGroup.scalar (Fin p) (Units.mk0 u hu0) * B : GL (Fin p) K) :
        Matrix (Fin p) (Fin p) K) k i = u * (B : Matrix (Fin p) (Fin p) K) k i := by
      intro k
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_mul]
      rfl
    simp only [Matrix.transpose_apply, Matrix.map_apply, e, e', map_mul]
    have hΓij : ∑ k, h.bar ((B : Matrix (Fin p) (Fin p) K) k i) *
        (B : Matrix (Fin p) (Fin p) K) k j = Γ i j := by
      simp [hΓ, herm, col_apply]
    have h1 : ∑ k, h.bar u * h.bar ((B : Matrix (Fin p) (Fin p) K) k i) *
        (u * (B : Matrix (Fin p) (Fin p) K) k j) =
        (u * h.bar u) * ∑ k, h.bar ((B : Matrix (Fin p) (Fin p) K) k i) *
          (B : Matrix (Fin p) (Fin p) K) k j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h1, hΓij, hu']
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, hconst i i0]
      exact inv_mul_cancel₀ ha0
    · rw [if_neg hij, hoff i j hij, mul_zero]
  · refine ⟨⟨δ, ?_⟩, fun g hg => ?_, fun i j hij => ?_⟩
    · rw [conj_scalar_mul]
      exact hrot
    · rw [conj_scalar_mul]
      exact hdiag g hg
    · simp only [conj_scalar_mul]
      exact hsep i j hij

end Main

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB
