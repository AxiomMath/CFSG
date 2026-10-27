module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSL3M
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLInner
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSL3X
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLTools

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open CFSG Subgroup Matrix
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBLinearSemilinear
open scoped MatrixGroups

variable {k : Type} [Field k] [Finite k] {n : ℕ} {X : Type} [Group X]

theorem exists_scalar_of_trivial (hk : Nat.card k = 3) (hn : 0 < n) {Ψ : SL(n, k) →* X}
    (hker : Ψ.ker ≤ center SL(n, k)) {D : GL (Fin n) k}
    (hD : ∀ y, Ψ (slConjugation n k D y) = Ψ y) :
    ∃ c : kˣ, D = GeneralLinearGroup.scalar (Fin n) c := by
  have htr : ∀ (i j : Fin n) (hij : i ≠ j), slConjugation n k D
      (SpecialLinearGroup.transvection hij (1 : k)) = SpecialLinearGroup.transvection hij 1 := by
    intro i j hij
    set t := SpecialLinearGroup.transvection hij (1 : k) with ht
    set z := slConjugation n k D t * t⁻¹ with hz
    have hzc : z ∈ center SL(n, k) := hker (by
      rw [MonoidHom.mem_ker, hz, map_mul, map_inv, hD, mul_inv_cancel])
    have hzt : slConjugation n k D t = z * t := by rw [hz, inv_mul_cancel_right]
    have ht3 : t ^ 3 = 1 := transvection_pow_three hk hij 1
    have h3 : z ^ 3 = 1 := by
      have h1 : (slConjugation n k D t) ^ 3 = 1 := by rw [← map_pow, ht3, map_one]
      rw [hzt, (show Commute z t from (mem_center_iff.mp hzc t).symm).mul_pow, ht3,
        mul_one] at h1
      exact h1
    rw [hzt, eq_one_of_mul_self (center_mul_self hk hzc) (by decide) h3, one_mul]
  have hcomm : ∀ (i j : Fin n), i ≠ j →
      D.val * single i j (1 : k) = single i j (1 : k) * D.val := by
    intro i j hij
    have h1 := congrArg (fun y : SL(n, k) => (y : Matrix (Fin n) (Fin n) k)) (htr i j hij)
    simp only [slConjugation_matrix, SpecialLinearGroup.transvection_coe] at h1
    have h2 : D.val * (1 + single i j 1) = (1 + single i j 1) * D.val := by
      calc D.val * (1 + single i j 1) = D.val * (1 + single i j 1) * ((D⁻¹).val * D.val) := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
        _ = (1 + single i j 1) * D.val := by rw [← Matrix.mul_assoc, h1]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h2
    exact add_left_cancel h2
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single fun i j hij =>
    (hcomm i j hij).symm
  have hc0 : c ≠ 0 := by
    intro h0
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have h1 := congrArg Matrix.det hc
    rw [h0, map_zero, Matrix.det_zero] at h1
    exact (D.isUnit.map Matrix.detMonoidHom).ne_zero h1.symm
  refine ⟨Units.mk0 c hc0, ?_⟩
  ext a b
  rw [← hc]
  rfl

theorem slConjugation_eq_of_commute (hk : Nat.card k = 3) {Ψ : SL(n, k) →* X}
    (hker : Ψ.ker ≤ center SL(n, k)) {r : X} {B : GL (Fin n) k}
    (hB : ∀ y, r * Ψ y * r⁻¹ = Ψ (slConjugation n k B y)) {m : ℕ} (hm : Odd m)
    (hBm : B ^ m = 1) {s : SL(n, k)} (hs : r * Ψ s = Ψ s * r) :
    slConjugation n k B s = s := by
  set z := slConjugation n k B s * s⁻¹ with hz
  have h1 : Ψ (slConjugation n k B s) = Ψ s := by rw [← hB s, hs, mul_inv_cancel_right]
  have hzc : z ∈ center SL(n, k) := hker (by
    rw [MonoidHom.mem_ker, hz, map_mul, map_inv, h1, mul_inv_cancel])
  have hzs : slConjugation n k B s = z * s := by rw [hz, inv_mul_cancel_right]
  have hpow : ∀ j : ℕ, slConjugation n k (B ^ j) s = z ^ j * s := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', map_mul, MulAut.mul_apply, ih, map_mul,
        slConjugation_center _ (pow_mem hzc j), hzs, ← mul_assoc, ← pow_succ]
  have h2 := hpow m
  rw [hBm, map_one, MulAut.one_apply] at h2
  have hzm : z ^ m = 1 := by
    have := congrArg (· * s⁻¹) h2
    simpa using this.symm
  rw [hzs, eq_one_of_mul_self (center_mul_self hk hzc) hm hzm, one_mul]

theorem exists_odd_lift (hk : Nat.card k = 3) (hn : 0 < n) {Ψ : SL(n, k) →* X}
    (hker : Ψ.ker ≤ center SL(n, k)) {r : X} {B₁ : GL (Fin n) k}
    (hB₁ : ∀ y, r * Ψ y * r⁻¹ = Ψ (slConjugation n k B₁ y)) {m : ℕ} (hm : Odd m)
    (hrm : r ^ m = 1) :
    ∃ B : GL (Fin n) k, (∀ y, r * Ψ y * r⁻¹ = Ψ (slConjugation n k B y)) ∧ B ^ m = 1 := by
  have hpow : ∀ j : ℕ, ∀ y, r ^ j * Ψ y * (r ^ j)⁻¹ = Ψ (slConjugation n k (B₁ ^ j) y) := by
    intro j
    induction j with
    | zero => intro y; simp
    | succ j ih =>
      intro y
      calc r ^ (j + 1) * Ψ y * (r ^ (j + 1))⁻¹ = r ^ j * (r * Ψ y * r⁻¹) * (r ^ j)⁻¹ := by
            rw [pow_succ]
            group
        _ = Ψ (slConjugation n k (B₁ ^ j) (slConjugation n k B₁ y)) := by rw [hB₁, ih]
        _ = Ψ (slConjugation n k (B₁ ^ (j + 1)) y) := by rw [pow_succ, map_mul, MulAut.mul_apply]
  have htriv : ∀ y, Ψ (slConjugation n k (B₁ ^ m) y) = Ψ y := by
    intro y
    rw [← hpow m y, hrm]
    group
  obtain ⟨c, hc⟩ := exists_scalar_of_trivial hk hn hker htriv
  refine ⟨GeneralLinearGroup.scalar (Fin n) c * B₁, fun y => by rw [hB₁, slConjugation_smul], ?_⟩
  have hcomm : Commute (GeneralLinearGroup.scalar (Fin n) c) B₁ := by
    have h := Subgroup.mem_center_iff.mp (by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩ : GeneralLinearGroup.scalar (Fin n) c ∈ center (GL (Fin n) k)) B₁
    exact h.symm
  rw [hcomm.mul_pow, hc, ← map_pow, ← map_mul]
  obtain ⟨t, rfl⟩ := hm
  rw [← pow_succ, show 2 * t + 1 + 1 = 2 * (t + 1) by ring, pow_mul, sq, unit_mul_self hk,
    one_pow, map_one]

theorem commute_three (hk : Nat.card k = 3) (hn : 3 ≤ n)
    (hZ : center (ProjectiveSpecialLinearGroup (Fin n) k) = ⊥)
    (A : GL (Fin n) k) (μ : kˣ) (hA : A * A = GeneralLinearGroup.scalar (Fin n) (μ * μ))
    {R : Subgroup (MulAut (ProjectiveSpecialLinearGroup (Fin n) k))} (hRodd : Odd (Nat.card R))
    (hRi : ∀ r ∈ R, r * innerDiagonalAction n k A = innerDiagonalAction n k A * r)
    (hRc : ∀ s, innerDiagonalAction n k A s = s → Odd (orderOf s) → ∀ r ∈ R,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁ := by
  have h2 := two_ne_zero_of_card hk
  set x₁ : GL (Fin n) k := GeneralLinearGroup.scalar (Fin n) μ⁻¹ * A with hx₁
  have hsc : ∀ c d : kˣ, GeneralLinearGroup.scalar (Fin n) c *
      GeneralLinearGroup.scalar (Fin n) d = GeneralLinearGroup.scalar (Fin n) (c * d) :=
    fun c d => (map_mul _ c d).symm
  have hcomm : ∀ (c : kˣ) (B : GL (Fin n) k), GeneralLinearGroup.scalar (Fin n) c * B =
      B * GeneralLinearGroup.scalar (Fin n) c := fun c B => by
    have := (Subgroup.mem_center_iff.mp (by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩ : GeneralLinearGroup.scalar (Fin n) c ∈ center (GL (Fin n) k))) B
    exact this.symm
  have hx₁sq : x₁ * x₁ = 1 := by
    rw [hx₁, mul_assoc, ← mul_assoc A, ← hcomm, mul_assoc, hA, ← mul_assoc, hsc, hsc,
      show μ⁻¹ * μ⁻¹ * (μ * μ) = 1 by group, map_one]
  have hx₁act : ∀ y, innerDiagonalAction n k A * psi n k y * (innerDiagonalAction n k A)⁻¹ =
      psi n k (slConjugation n k x₁ y) := by
    intro y
    rw [innerDiagonalAction_conj, hx₁, slConjugation_smul]
  obtain ⟨P₀, σ₁, -, hP₀, -⟩ := exists_chart_gl (n := n) (by omega) h2 (psi n k)
    (f := innerDiagonalAction n k A) (g := 1) (x₁ := x₁) (x₂ := 1) hx₁act
    (fun y => by simp [map_one]) hx₁sq (mul_one 1) (by rw [one_mul, mul_one])
  set i := innerDiagonalAction n k A with hi
  set Ψ := (psi n k).comp (MulAut.conj P₀).toMonoidHom with hΨ
  have hΨapply : ∀ y, Ψ y = psi n k (P₀ * y * P₀⁻¹) := fun y => rfl
  have hf : ∀ y, i * Ψ y * i⁻¹ = Ψ (slConjugation n k (signGL k σ₁) y) := by
    intro y
    rw [hΨapply, hΨapply, hP₀]
  have hkerΨ : Ψ.ker ≤ center SL(n, k) := by
    intro y hy
    rw [MonoidHom.mem_ker, hΨapply] at hy
    have h1 := psi_ker hZ (MonoidHom.mem_ker.mpr hy)
    rw [mem_center_iff]
    intro g
    have h3 := mem_center_iff.mp h1 (P₀ * g * P₀⁻¹)
    have h4 : P₀ * (g * y) * P₀⁻¹ = P₀ * (y * g) * P₀⁻¹ := by
      calc P₀ * (g * y) * P₀⁻¹ = P₀ * g * P₀⁻¹ * (P₀ * y * P₀⁻¹) := by group
        _ = P₀ * y * P₀⁻¹ * (P₀ * g * P₀⁻¹) := h3
        _ = P₀ * (y * g) * P₀⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h4)
  have hrange : Ψ.range = (psi n k).range := by
    rw [hΨ, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (show Function.Surjective (MulAut.conj P₀).toMonoidHom from
        (MulAut.conj P₀).surjective), ← MonoidHom.range_eq_map]
  have hnormΨ : Ψ.range.Normal := by rw [hrange]; exact psi_range_normal
  have hfaithΨ : ∀ x, (∀ y, x * Ψ y * x⁻¹ = Ψ y) → x = 1 := by
    intro x hx
    refine psi_faith hZ x fun z => ?_
    have := hx (P₀⁻¹ * z * P₀)
    rwa [hΨapply, show P₀ * (P₀⁻¹ * z * P₀) * P₀⁻¹ = z by group] at this
  have hRconjΨ : ∀ s ∈ Ψ.range ⊓ centralizer ({i} : Set _), Odd (orderOf s) → ∀ r ∈ R,
      s * r * s⁻¹ ∈ R := by
    intro s hs hso r hr
    rw [hrange, psi_surjective_range] at hs
    exact conj_mem_of_mem_range hZ hRc hs hso hr
  have := hnormΨ
  have hdiag : ∀ r ∈ R, ∃ B : GL (Fin n) k,
      (∀ y, r * Ψ y * r⁻¹ = Ψ (slConjugation n k B y)) ∧ ∃ u : Fin n → k, B.val = diagonal u := by
    intro r hr
    have hodd : Odd (orderOf r) := by
      have h := orderOf_dvd_natCard (⟨r, hr⟩ : R)
      rw [Subgroup.orderOf_mk] at h
      exact Odd.of_dvd_nat hRodd h
    obtain ⟨B₀, ρ, hrB⟩ := exists_semilinear_of_odd hn hodd
    rw [ringEquiv_eq_one hk ρ, semilinearAction, map_one, mul_one] at hrB
    set B₁ : GL (Fin n) k := (SpecialLinearGroup.toGL P₀)⁻¹ * B₀ * SpecialLinearGroup.toGL P₀
      with hB₁
    have hB₁act : ∀ y, r * Ψ y * r⁻¹ = Ψ (slConjugation n k B₁ y) := by
      intro y
      rw [hrB, hΨapply, hΨapply, innerDiagonalAction_conj]
      congr 1
      apply SpecialLinearGroup.toGL_injective
      rw [toGL_slConjugation]
      simp only [map_mul, map_inv]
      rw [toGL_slConjugation, hB₁]
      group
    obtain ⟨B, hBact, hBm⟩ := exists_odd_lift hk (by omega) hkerΨ hB₁act hodd
      (pow_orderOf_eq_one r)
    refine ⟨B, hBact, ?_⟩
    have hfixB : ∀ s, r * Ψ s = Ψ s * r →
        B.val * (s : Matrix (Fin n) (Fin n) k) = (s : Matrix (Fin n) (Fin n) k) * B.val := by
      intro s hs
      have h1 := slConjugation_eq_of_commute hk hkerΨ hBact hodd hBm hs
      have h2 := congrArg (fun y : SL(n, k) => (y : Matrix (Fin n) (Fin n) k)) h1
      simp only [slConjugation_matrix] at h2
      calc B.val * (s : Matrix (Fin n) (Fin n) k) =
          B.val * (s : Matrix (Fin n) (Fin n) k) * ((B⁻¹).val * B.val) := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
        _ = (s : Matrix (Fin n) (Fin n) k) * B.val := by rw [← Matrix.mul_assoc, h2]
    have hblocks : ∀ b, 2 ≤ (coordSet σ₁ b).card → ∃ c : k, ∀ a a',
        (a ∈ coordSet σ₁ b ∨ a' ∈ coordSet σ₁ b) → B.val a a' = if a = a' then c else 0 := by
      intro b hb
      by_cases hb3 : 3 ≤ (coordSet σ₁ b).card
      ·
        have hQ := isComponentOf_block_centralizer_three h2 Ψ hkerΨ i σ₁ hf b hb3
        refine block_scalar_of_transvections hb fun i' hi' j' hj' hij => ?_
        exact hfixB _ (commute_of_isComponentOf (L := Ψ.range) hRodd hRi hRconjΨ hQ hr
          ⟨_, transvection_mem_coordBlockSL hi' hj' hij 1, rfl⟩)
      ·
        have hJ : (coordSet σ₁ b).card = 2 := by omega
        obtain ⟨c, hc⟩ : ∃ c, c ∉ coordSet σ₁ b := by
          by_contra hall
          push Not at hall
          have : coordSet σ₁ b = Finset.univ := Finset.eq_univ_of_forall hall
          rw [this, Finset.card_univ, Fintype.card_fin] at hJ
          omega
        obtain ⟨e⟩ := nonempty_blockTwo_equiv hkerΨ hJ hc
        have hHT := blockTwo_le_oddClosure hk hf hJ
        have hHn := conj_mem_blockTwo (b := b) hk hkerΨ hf
        have hq : ∀ q : SL(2, k), q ^ 4 = 1 →
            r * Ψ (blockTwo _ hJ q) = Ψ (blockTwo _ hJ q) * r := by
          intro q hq4
          refine commute_of_sl23 (L := Ψ.range) hRodd hRi hRconjΨ hHT hHn hk e hr ?_ (a := 2) ?_
          · refine ⟨blockTwo _ hJ q, ?_, rfl⟩
            rw [← range_blockTwo _ hJ]
            exact ⟨q, rfl⟩
          · rw [← map_pow, ← map_pow, show 2 ^ 2 = 4 by rfl, hq4, map_one, map_one]
        exact block_scalar_of_two hJ h2 (hfixB _ (hq _ qOne_pow_four))
          (hfixB _ (hq _ (qTwo_pow_four hk)))
    obtain ⟨u, -, hu⟩ := eq_diagonal_of_blocks σ₁ hn hblocks
    exact ⟨u, hu⟩
  intro r₁ h₁ r₂ h₂
  obtain ⟨B₁, hB₁, u₁, hu₁⟩ := hdiag r₁ h₁
  obtain ⟨B₂, hB₂, u₂, hu₂⟩ := hdiag r₂ h₂
  have hBB : B₁ * B₂ = B₂ * B₁ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hu₁, hu₂, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    ext a
    exact mul_comm _ _
  have hx : ∀ y, ((r₂ * r₁)⁻¹ * (r₁ * r₂)) * Ψ y * ((r₂ * r₁)⁻¹ * (r₁ * r₂))⁻¹ = Ψ y := by
    intro y
    have e1 : (r₁ * r₂) * Ψ y * (r₁ * r₂)⁻¹ = Ψ (slConjugation n k (B₁ * B₂) y) := by
      rw [map_mul, MulAut.mul_apply, ← hB₁, ← hB₂]
      group
    have e2 : (r₂ * r₁) * Ψ y * (r₂ * r₁)⁻¹ = Ψ (slConjugation n k (B₂ * B₁) y) := by
      rw [map_mul, MulAut.mul_apply, ← hB₂, ← hB₁]
      group
    rw [hBB] at e1
    calc ((r₂ * r₁)⁻¹ * (r₁ * r₂)) * Ψ y * ((r₂ * r₁)⁻¹ * (r₁ * r₂))⁻¹ =
        (r₂ * r₁)⁻¹ * ((r₁ * r₂) * Ψ y * (r₁ * r₂)⁻¹) * (r₂ * r₁) := by group
      _ = (r₂ * r₁)⁻¹ * ((r₂ * r₁) * Ψ y * (r₂ * r₁)⁻¹) * (r₂ * r₁) := by rw [e1, e2]
      _ = Ψ y := by group
  have h1 := hfaithΨ _ hx
  rw [inv_mul_eq_one] at h1
  exact h1.symm

theorem commute_inner_three {p f : ℕ} [Fact p.Prime] (hq : p ^ f = 3) {n : ℕ} (hn : 3 ≤ n)
    (hZ : center (ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f)) = ⊥)
    (A : GL (Fin n) (GaloisField p f)) (μ : (GaloisField p f)ˣ)
    (hA : A * A = GeneralLinearGroup.scalar (Fin n) (μ * μ))
    (R : Subgroup (MulAut (ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f))))
    (hRodd : Odd (Nat.card R))
    (hRi : ∀ r ∈ R, r * innerDiagonalAction n _ A = innerDiagonalAction n _ A * r)
    (hRc : ∀ s, innerDiagonalAction n _ A s = s → Odd (orderOf s) → ∀ r ∈ R,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁ := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hk : Nat.card (GaloisField p f) = 3 := by rw [GaloisField.card p f hf, hq]
  exact commute_three hk hn hZ A μ hA hRodd hRi hRc

end CFSG.ComponentClassification.Foote5.OddLieCore
