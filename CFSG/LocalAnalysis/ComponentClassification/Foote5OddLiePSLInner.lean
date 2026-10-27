module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLSplit
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagLinear
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieCore

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open CFSG Subgroup Matrix
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
open CFSG.ClassicalInvolution.RouteD.Gaps (LinearAutClassification diagGL coe_diagGL)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open scoped MatrixGroups

variable {n : ℕ} {k : Type} [Field k]

@[expose] noncomputable def psi (n : ℕ) (k : Type) [Field k] :
    SL(n, k) →* MulAut (ProjectiveSpecialLinearGroup (Fin n) k) :=
  MulAut.conj.comp (QuotientGroup.mk' (center SL(n, k)))

theorem psi_apply (y : SL(n, k)) :
    psi n k y = MulAut.conj (QuotientGroup.mk' (center SL(n, k)) y) := rfl

theorem psi_surjective_range :
    (psi n k).range = (MulAut.conj : ProjectiveSpecialLinearGroup (Fin n) k →* _).range := by
  rw [psi, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
    ← MonoidHom.range_eq_map]

theorem psi_ker (hZ : center (ProjectiveSpecialLinearGroup (Fin n) k) = ⊥) :
    (psi n k).ker ≤ center SL(n, k) := by
  intro y hy
  rw [MonoidHom.mem_ker, psi_apply] at hy
  have h1 := conj_injective hZ (hy.trans (map_one _).symm)
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1

theorem psi_range_normal : (psi n k).range.Normal := by
  rw [psi_surjective_range]
  constructor
  rintro _ ⟨x, rfl⟩ φ
  exact ⟨φ x, (conj_apply_eq φ x)⟩

theorem psi_faith (hZ : center (ProjectiveSpecialLinearGroup (Fin n) k) = ⊥)
    (x : MulAut (ProjectiveSpecialLinearGroup (Fin n) k))
    (hx : ∀ y, x * psi n k y * x⁻¹ = psi n k y) : x = 1 := by
  ext z
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center SL(n, k)) z
  have h := hx y
  rw [psi_apply, ← conj_apply_eq] at h
  exact conj_injective hZ h

theorem innerDiagonalAction_conj (A : GL (Fin n) k) (y : SL(n, k)) :
    innerDiagonalAction n k A * psi n k y * (innerDiagonalAction n k A)⁻¹ =
      psi n k (slConjugation n k A y) := by
  rw [psi_apply, psi_apply, ← conj_apply_eq, innerDiagonalAction_mk]

theorem slConjugation_smul (A : GL (Fin n) k) (c : kˣ) :
    slConjugation n k (GeneralLinearGroup.scalar (Fin n) c * A) = slConjugation n k A := by
  ext y : 1
  apply SpecialLinearGroup.toGL_injective
  have hc : ∀ B : GL (Fin n) k, GeneralLinearGroup.scalar (Fin n) c * B =
      B * GeneralLinearGroup.scalar (Fin n) c := fun B => by
    have := (Subgroup.mem_center_iff.mp (by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩ : GeneralLinearGroup.scalar (Fin n) c ∈ center (GL (Fin n) k))) B
    exact this.symm
  have hc' := hc (A * SpecialLinearGroup.toGL y * A⁻¹)
  rw [toGL_slConjugation, toGL_slConjugation, _root_.mul_inv_rev]
  calc GeneralLinearGroup.scalar (Fin n) c * A * SpecialLinearGroup.toGL y *
      (A⁻¹ * (GeneralLinearGroup.scalar (Fin n) c)⁻¹) =
        (GeneralLinearGroup.scalar (Fin n) c * (A * SpecialLinearGroup.toGL y * A⁻¹)) *
          (GeneralLinearGroup.scalar (Fin n) c)⁻¹ := by group
    _ = (A * SpecialLinearGroup.toGL y * A⁻¹ * GeneralLinearGroup.scalar (Fin n) c) *
          (GeneralLinearGroup.scalar (Fin n) c)⁻¹ := by rw [hc']
    _ = A * SpecialLinearGroup.toGL y * A⁻¹ := by group

theorem conj_mem_of_mem_range {P : Type} [Group P] [Finite P] (hZ : center P = ⊥)
    {i : MulAut P} {R : Subgroup (MulAut P)}
    (hRc : ∀ s : P, i s = s → Odd (orderOf s) → ∀ r ∈ R,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R)
    {s : MulAut P} (hs : s ∈ (MulAut.conj : P →* MulAut P).range ⊓ centralizer ({i} : Set _))
    (hso : Odd (orderOf s)) {r : MulAut P} (hr : r ∈ R) : s * r * s⁻¹ ∈ R := by
  obtain ⟨⟨t, rfl⟩, hti⟩ := mem_inf.mp hs
  rw [mem_centralizer_singleton_iff] at hti
  have hit : i t = t := by
    apply conj_injective hZ
    rw [conj_apply_eq]
    calc i * MulAut.conj t * i⁻¹ = MulAut.conj t * i * i⁻¹ := by rw [hti]
      _ = MulAut.conj t := by group
  refine hRc t hit ?_ r hr
  rwa [orderOf_injective _ (conj_injective hZ)] at hso

theorem commute_inner_split
    {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hn : 3 ≤ n) (hZ : center (ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f)) = ⊥)
    (A : GL (Fin n) (GaloisField p f)) (μ : (GaloisField p f)ˣ)
    (hA : A * A = GeneralLinearGroup.scalar (Fin n) (μ * μ))
    {R : Subgroup (MulAut (ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f)))}
    (hRodd : Odd (Nat.card R))
    (hRi : ∀ r ∈ R, r * innerDiagonalAction n _ A = innerDiagonalAction n _ A * r)
    (hRc : ∀ s, innerDiagonalAction n _ A s = s → Odd (orderOf s) → ∀ r ∈ R,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁ := by
  set k := GaloisField p f
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card k = p ^ f := GaloisField.card p f hf
  have h2 : (2 : k) ≠ 0 := by
    intro h
    have hc : ringChar k = p := ringChar.eq k p
    have := (ringChar.spec k 2).mp (by exact_mod_cast h)
    rw [hc] at this
    have := Nat.le_of_dvd (by norm_num) this
    have hp := (Fact.out : p.Prime).two_le
    have : p = 2 := by omega
    exact hp2 this
  have h4 : 4 ≤ Nat.card k := by rw [hcard]; omega
  have hcl := CFSG.ClassicalInvolution.ModelFacts.LinearAut.linearAutClassification hp2 hq hn
  set x₁ : GL (Fin n) k := GeneralLinearGroup.scalar (Fin n) μ⁻¹ * A with hx₁
  have hsc : ∀ c d : kˣ, GeneralLinearGroup.scalar (Fin n) c * GeneralLinearGroup.scalar (Fin n) d =
      GeneralLinearGroup.scalar (Fin n) (c * d) := fun c d => (map_mul _ c d).symm
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
  exact commute_of_split hn h2 h4 hcl Ψ hkerΨ hnormΨ hfaithΨ i σ₁ hf hRodd hRi hRconjΨ

end CFSG.ComponentClassification.Foote5.OddLieCore
