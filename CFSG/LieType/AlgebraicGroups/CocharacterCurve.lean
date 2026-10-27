module

public import CFSG.LieType.AlgebraicGroups.IdentityComponentLang

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

variable {τ : Tag} {L : Type} [Field L]

theorem isPolynomialCurve_const (Q : ModGL τ L) : IsPolynomialCurve fun _ : L => Q :=
  ⟨fun a b => Polynomial.C (endMatrix τ (Q : Module.End L (RootModule τ L)) a b),
    fun _ _ _ => Polynomial.eval_C.symm⟩

theorem IsPolynomialCurve.conj {c : L → ModGL τ L} (hc : IsPolynomialCurve c) (Q : ModGL τ L) :
    IsPolynomialCurve fun t => Q * c t * Q⁻¹ :=
  ((isPolynomialCurve_const Q).mul hc).mul (isPolynomialCurve_const Q⁻¹)

theorem rootChar_cochar (l : Fin τ.rank → ℤ) (t : Lˣ) (v : Fin τ.rank → ℤ) :
    rootChar (fun i => t ^ l i) v = t ^ ∑ i, l i * v i := by
  simp only [rootChar, ← zpow_mul]
  exact Finset.prod_zpow_eq_zpow_sum _ _ _

theorem exists_isPolynomialCurve_cochar_pinnedX {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (l : Fin τ.rank → ℤ) (hl : 0 < ∑ i, l i * α i) (c : L) :
    ∃ γ : L → ModGL τ L, IsPolynomialCurve γ ∧ γ 0 = 1 ∧ γ 1 = pinnedX τ L α c ∧ ∀ t : Lˣ,
      γ t = rootDiagUnit τ (fun i => t ^ l i) * pinnedX τ L α c *
        (rootDiagUnit τ fun i => t ^ l i)⁻¹ := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = ∑ i, l i * α i := ⟨_, Int.toNat_of_nonneg hl.le⟩
  have hN0 : N ≠ 0 := fun h => by
    rw [h, Nat.cast_zero] at hN
    exact hl.ne hN
  have hγ := isPolynomialCurve_pinnedX (τ := τ) α (Polynomial.C c * Polynomial.X ^ N)
  refine ⟨_, hγ, ?_, ?_, fun t => ?_⟩
  · simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      zero_pow hN0, mul_zero, pinnedX_zero]
  · simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      one_pow, mul_one]
  · rw [rootDiagUnit_conj_pinnedX _ hα, rootChar_cochar, ← hN, zpow_natCast,
      Units.val_pow_eq_pow_val]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [mul_comm c]

theorem exists_isPolynomialCurve_cochar {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α)
    (l : Fin τ.rank → ℤ) (hl : ∀ α ∈ S, 0 < ∑ i, l i * α i) {u : ModGL τ L}
    (hu : u ∈ rootSpan τ L S) :
    ∃ γ : L → ModGL τ L, IsPolynomialCurve γ ∧ γ 0 = 1 ∧ γ 1 = u ∧ ∀ t : Lˣ,
      γ t = rootDiagUnit τ (fun i => t ^ l i) * u * (rootDiagUnit τ fun i => t ^ l i)⁻¹ := by
  have hu' : u ∈ ⨆ α : S, rootSubgroup τ L α.1 := by
    rwa [rootSpan, iSup_subtype'] at hu
  refine Subgroup.iSup_induction (fun α : S => rootSubgroup τ L α.1) (C := fun u =>
    ∃ γ : L → ModGL τ L, IsPolynomialCurve γ ∧ γ 0 = 1 ∧ γ 1 = u ∧ ∀ t : Lˣ,
      γ t = rootDiagUnit τ (fun i => t ^ l i) * u * (rootDiagUnit τ fun i => t ^ l i)⁻¹) hu'
    (fun α x hx => ?_) ?_ fun x y hx hy => ?_
  · obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
    exact exists_isPolynomialCurve_cochar_pinnedX (hS _ α.2) l (hl _ α.2) c
  · exact ⟨fun _ => 1, isPolynomialCurve_const 1, rfl, rfl, fun t => by
      rw [mul_one, mul_inv_cancel]⟩
  · obtain ⟨γx, hγx, hx0, hx1, hxt⟩ := hx
    obtain ⟨γy, hγy, hy0, hy1, hyt⟩ := hy
    refine ⟨fun t => γx t * γy t, hγx.mul hγy, ?_, ?_, fun t => ?_⟩
    · show γx 0 * γy 0 = 1
      rw [hx0, hy0, mul_one]
    · show γx 1 * γy 1 = x * y
      rw [hx1, hy1]
    · show γx t * γy t = _
      rw [hxt, hyt]
      group

theorem conj_mem_closedIdentityComponent_of_cochar [IsAlgClosed L] {Z : Subgroup (ModGL τ L)}
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) (l : Fin τ.rank → ℤ)
    (hl : ∀ α ∈ S, 0 < ∑ i, l i * α i) {u : ModGL τ L} (hu : u ∈ rootSpan τ L S)
    (Q : ModGL τ L)
    (hZ : ∀ t : Lˣ, Q * (rootDiagUnit τ (fun i => t ^ l i) * u *
      (rootDiagUnit τ fun i => t ^ l i)⁻¹) * Q⁻¹ ∈ Z) :
    Q * u * Q⁻¹ ∈ closedIdentityComponent Z := by
  obtain ⟨γ, hγ, h0, h1, hγt⟩ := exists_isPolynomialCurve_cochar hS l hl hu
  have hmem : ∀ t : L, Q * γ t * Q⁻¹ ∈ Z := by
    intro t
    rcases eq_or_ne t 0 with rfl | ht
    · rw [h0, mul_one, mul_inv_cancel]
      exact one_mem Z
    · have e := hγt (Units.mk0 t ht)
      rw [Units.val_mk0] at e
      rw [e]
      exact hZ _
  have h := mem_closedIdentityComponent_of_isPolynomialCurve (hγ.conj Q) hmem (t₀ := 0)
    (by simp only [h0, mul_one, mul_inv_cancel]) 1
  simpa only [h1] using h

theorem conj_mem_closedIdentityComponent_of_contract [IsAlgClosed L] {Z : Subgroup (ModGL τ L)}
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) (f : Fin τ.rank → ℤ)
    (hf : ∀ α ∈ S, 0 < ∑ i, f i * α i) {g v : ModGL τ L} (hv : v ∈ rootSpan τ L S)
    (hT : ∀ s : Lˣ, g * rootDiagUnit τ (fun i => s ^ f i) * g⁻¹ ∈ Z) (hgv : g * v * g⁻¹ ∈ Z) :
    g * v * g⁻¹ ∈ closedIdentityComponent Z := by
  refine conj_mem_closedIdentityComponent_of_cochar hS f hf hv g fun s => ?_
  have e : g * (rootDiagUnit τ (fun i => s ^ f i) * v * (rootDiagUnit τ fun i => s ^ f i)⁻¹) *
      g⁻¹ = g * rootDiagUnit τ (fun i => s ^ f i) * g⁻¹ * (g * v * g⁻¹) *
        (g * rootDiagUnit τ (fun i => s ^ f i) * g⁻¹)⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem (hT s) hgv) (inv_mem (hT s))

theorem mem_rootCharStabilizer_cochar {σ : WeylGroup τ} {l : Fin τ.rank → ℤ}
    (hl : ∀ μ : Fin τ.rank → ℤ, ∑ i, l i * (σ • μ) i = ∑ i, l i * μ i) (t : Lˣ) :
    σ ∈ rootCharStabilizer fun i => t ^ l i := by
  show ∀ v : Fin τ.rank → ℤ, rootChar (fun i => t ^ l i) (σ • v) = rootChar (fun i => t ^ l i) v
  intro v
  rw [rootChar_cochar, rootChar_cochar, hl]

theorem commute_rootDiagUnit_torus_mul_canonicalRep {a : Fin τ.rank → Lˣ} {σ : WeylGroup τ}
    (hσ : σ ∈ rootCharStabilizer a) {h : ModGL τ L} (hh : h ∈ torusGroup τ L) :
    Commute (rootDiagUnit τ a) (h * canonicalRep (coxeterSystem τ) L σ) := by
  have hc := (conj_canonicalRep_eq_iff (K := L) a σ).2 hσ
  rw [mul_inv_eq_iff_eq_mul] at hc
  show rootDiagUnit τ a * (h * canonicalRep (coxeterSystem τ) L σ) =
    h * canonicalRep (coxeterSystem τ) L σ * rootDiagUnit τ a
  rw [← mul_assoc, rootDiagUnit_mul_comm_of_mem_torusGroup a hh, mul_assoc, hc, mul_assoc]

theorem commute_rootDiagUnit_monomial {t₁ : ModGL τ L} {w : WeylGroup τ}
    (ht₁ : t₁ ∈ torusGroup τ L) (f : Fin τ.rank → ℤ)
    (hf : ∀ μ : Fin τ.rank → ℤ, ∑ i, f i * (w • μ) i = ∑ i, f i * μ i) (s : Lˣ) :
    Commute (rootDiagUnit τ (fun i => s ^ f i)) (t₁ * canonicalRep (coxeterSystem τ) L w) :=
  commute_rootDiagUnit_torus_mul_canonicalRep (mem_rootCharStabilizer_cochar hf s) ht₁

@[expose] def weylCochar (σ : WeylGroup τ) (N : ℕ) : Fin τ.rank → ℤ :=
  fun i => ∑ j ∈ Finset.range N, height (σ ^ j • (Pi.single i 1 : Fin τ.rank → ℤ))

theorem sum_weylCochar_mul (σ : WeylGroup τ) (N : ℕ) (v : Fin τ.rank → ℤ) :
    ∑ i, weylCochar σ N i * v i = ∑ j ∈ Finset.range N, height (σ ^ j • v) := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    ext m
    simp [Finset.sum_apply, Pi.single_apply]
  have hw : ∀ j : ℕ, height (σ ^ j • v) =
      ∑ i, v i * height (σ ^ j • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
    intro j
    conv_lhs => rw [hv]
    rw [Finset.smul_sum, height_finset_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_comm, height_zsmul]
  simp only [hw, weylCochar, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem sum_weylCochar_mul_smul {σ : WeylGroup τ} {N : ℕ} (hN : σ ^ N = 1)
    (μ : Fin τ.rank → ℤ) :
    ∑ i, weylCochar σ N i * (σ • μ) i = ∑ i, weylCochar σ N i * μ i := by
  rw [sum_weylCochar_mul, sum_weylCochar_mul]
  have e : ∀ j : ℕ, σ ^ j • σ • μ = σ ^ (j + 1) • μ := fun j => by rw [pow_succ, mul_smul]
  simp only [e]
  have h1 := Finset.sum_range_succ' (fun j => height (σ ^ j • μ)) N
  have h2 := Finset.sum_range_succ (fun j => height (σ ^ j • μ)) N
  simp only [hN, pow_zero] at h1 h2
  linarith

theorem sum_weylCochar_mul_pos {σ : WeylGroup τ} {N : ℕ} (hN : 1 ≤ N)
    {T : Set (Fin τ.rank → ℤ)} (hT : ∀ α ∈ T, 0 < height α) (hσT : ∀ α ∈ T, σ • α ∈ T)
    {α : Fin τ.rank → ℤ} (hα : α ∈ T) : 0 < ∑ i, weylCochar σ N i * α i := by
  have hpow : ∀ j : ℕ, σ ^ j • α ∈ T := by
    intro j
    induction j with
    | zero => simpa using hα
    | succ j ih => rw [pow_succ', mul_smul]; exact hσT _ ih
  rw [sum_weylCochar_mul]
  exact Finset.sum_pos (fun j _ => hT _ (hpow j)) ⟨0, Finset.mem_range.2 hN⟩

theorem exists_pos_smul_invariant_functional {σ : WeylGroup τ} {N : ℕ} (hN : 1 ≤ N)
    (hσN : σ ^ N = 1) {T : Set (Fin τ.rank → ℤ)} (hT : ∀ α ∈ T, 0 < height α)
    (hσT : ∀ α ∈ T, σ • α ∈ T) :
    ∃ f : Fin τ.rank → ℤ, (∀ α ∈ T, 0 < ∑ i, f i * α i) ∧
      ∀ μ : Fin τ.rank → ℤ, ∑ i, f i * (σ • μ) i = ∑ i, f i * μ i :=
  ⟨weylCochar σ N, fun _ hα => sum_weylCochar_mul_pos hN hT hσT hα, sum_weylCochar_mul_smul hσN⟩

end CFSG.LieType.AlgebraicGroups

end
