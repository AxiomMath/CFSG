module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLNsX
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLInner
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLTools

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open CFSG Subgroup Matrix
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.CatalogueBLinearSemilinear
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem commute_nonsplit (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n)
    (hZ : center (ProjectiveSpecialLinearGroup (Fin n) K) = ⊥)
    (A : GL (Fin n) K) (c : Kˣ) (hA : A * A = GeneralLinearGroup.scalar (Fin n) c)
    (hc : ¬ IsSquare (c : K))
    {R : Subgroup (MulAut (ProjectiveSpecialLinearGroup (Fin n) K))} (hRodd : Odd (Nat.card R))
    (hRi : ∀ r ∈ R, r * innerDiagonalAction n K A = innerDiagonalAction n K A * r)
    (hRc : ∀ s, innerDiagonalAction n K A s = s → Odd (orderOf s) → ∀ r ∈ R,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁ := by
  have hsq : A ^ 2 = GeneralLinearGroup.scalar (Fin n) c := by rw [sq]; exact hA
  obtain ⟨X, hX, hβ⟩ := exists_nonsplit_component h2 hn A c hsq hc
  have := psi_range_normal (n := n) (k := K)
  set i := innerDiagonalAction n K A with hi
  set Z := center SL(n, K) with hZdef
  have hQ := CFSG.ClassicalInvolution.Balance.isComponentOf_map_centralizer (psi_ker hZ) 1 i
    (slConjugation n K A) (fun y => by simpa using innerDiagonalAction_conj A y) hX
  have e : (MulAut.conj (1 : SL(n, K))).toMonoidHom = MonoidHom.id _ := by
    ext
    simp
  rw [e, MonoidHom.comp_id] at hQ
  have hRconj : ∀ s ∈ (psi n K).range ⊓ centralizer ({i} : Set _), Odd (orderOf s) →
      ∀ r ∈ R, s * r * s⁻¹ ∈ R := by
    intro s hs hso r hr
    rw [psi_surjective_range] at hs
    exact conj_mem_of_mem_range hZ hRc hs hso hr
  have hform : ∀ r ∈ R, ∃ B : GL (Fin n) K, r = innerDiagonalAction n K B ∧
      ∀ x ∈ X, ∀ v, B.val *ᵥ ((x : Matrix (Fin n) (Fin n) K) *ᵥ v) =
        (x : Matrix (Fin n) (Fin n) K) *ᵥ (B.val *ᵥ v) := by
    intro r hr
    have hfix : ∀ x ∈ X, r (QuotientGroup.mk' Z x) = QuotientGroup.mk' Z x := by
      intro x hx
      have h1 := commute_of_isComponentOf (L := (psi n K).range) hRodd hRi hRconj hQ hr
        ⟨x, hx, rfl⟩
      apply conj_injective hZ
      rw [conj_apply_eq, ← psi_apply]
      calc r * psi n K x * r⁻¹ = psi n K x * r * r⁻¹ := by rw [h1]
        _ = psi n K x := by group
    have hodd : Odd (orderOf r) := by
      have h := orderOf_dvd_natCard (⟨r, hr⟩ : R)
      rw [Subgroup.orderOf_mk] at h
      exact Odd.of_dvd_nat hRodd h
    obtain ⟨B, ρ, rfl⟩ := exists_semilinear_of_odd hn hodd
    have hsl := fun x hx => eq_of_fix_perfect hX.2.2.1 hfix (x := x) hx
    have hBx : ∀ x ∈ X, B.val * ρ.toRingHom.mapMatrix (x : Matrix (Fin n) (Fin n) K) =
        (x : Matrix (Fin n) (Fin n) K) * B.val := by
      intro x hx
      have h1 := congrArg (fun y : SL(n, K) => (y : Matrix (Fin n) (Fin n) K)) (hsl x hx)
      simp only [slSemilinearAction_matrix] at h1
      calc B.val * ρ.toRingHom.mapMatrix (x : Matrix (Fin n) (Fin n) K) =
          B.val * ρ.toRingHom.mapMatrix (x : Matrix (Fin n) (Fin n) K) * ((B⁻¹).val * B.val) := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
        _ = (x : Matrix (Fin n) (Fin n) K) * B.val := by rw [← Matrix.mul_assoc, h1]
    let β : (Fin n → K) →+ (Fin n → K) :=
      { toFun := fun v => B.val *ᵥ (fun k => ρ (v k))
        map_zero' := by
          simp only [Pi.zero_apply, map_zero]
          exact Matrix.mulVec_zero _
        map_add' := fun v w => by
          simp only [Pi.add_apply, map_add]
          exact Matrix.mulVec_add _ _ _ }
    have hβapp : ∀ v, β v = B.val *ᵥ (fun k => ρ (v k)) := fun v => rfl
    have hρmv : ∀ (x : Matrix (Fin n) (Fin n) K) v,
        (fun k => ρ ((x *ᵥ v) k)) = ρ.toRingHom.mapMatrix x *ᵥ (fun k => ρ (v k)) := by
      intro x v
      ext k
      exact RingHom.map_mulVec ρ.toRingHom x v k
    have hβX : ∀ x ∈ X, ∀ v, β ((x : Matrix (Fin n) (Fin n) K) *ᵥ v) =
        (x : Matrix (Fin n) (Fin n) K) *ᵥ β v := by
      intro x hx v
      rw [hβapp, hβapp, hρmv, Matrix.mulVec_mulVec, hBx x hx, ← Matrix.mulVec_mulVec]
    obtain ⟨hlin, -⟩ := hβ β β hβX hβX
    have hρ : ρ = 1 := by
      refine RingEquiv.ext fun k => ?_
      have hn0 : 0 < n := by omega
      set v : Fin n → K := Pi.single ⟨0, hn0⟩ 1 with hv
      have hρv : (fun l => ρ (v l)) = v := by
        ext l
        rw [hv]
        by_cases hl : l = ⟨0, hn0⟩
        · subst hl
          simp
        · simp [hl]
      have hβv : β v ≠ 0 := by
        rw [hβapp, hρv]
        intro h0
        have h1 := congrArg (fun w => (B⁻¹).val *ᵥ w) h0
        simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec, Matrix.mulVec_zero] at h1
        have h2 := congrFun h1 ⟨0, hn0⟩
        simp [hv] at h2
      have h1 := hlin k v
      have h2 : β (k • v) = ρ k • β v := by
        rw [hβapp, hβapp]
        have : (fun l => ρ ((k • v) l)) = ρ k • (fun l => ρ (v l)) := by
          ext l
          simp
        rw [this, Matrix.mulVec_smul]
      rw [h2] at h1
      exact smul_left_injective K hβv h1
    subst hρ
    refine ⟨B, by rw [semilinearAction, map_one, mul_one], fun x hx v => ?_⟩
    have := hβX x hx v
    rw [hβapp, hβapp] at this
    exact this
  intro r₁ h₁ r₂ h₂
  obtain ⟨B₁, rfl, hB₁⟩ := hform r₁ h₁
  obtain ⟨B₂, rfl, hB₂⟩ := hform r₂ h₂
  let β₁ : (Fin n → K) →+ (Fin n → K) := (Matrix.mulVecLin B₁.val).toAddMonoidHom
  let β₂ : (Fin n → K) →+ (Fin n → K) := (Matrix.mulVecLin B₂.val).toAddMonoidHom
  obtain ⟨-, hcomm⟩ := hβ β₁ β₂ hB₁ hB₂
  apply commute_of_mem
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  refine CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspace.matrix_eq_of_mulVec_eq
    fun v => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact hcomm v

theorem commute_inner_nonsplit {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) {n : ℕ}
    (hn : 3 ≤ n) (hZ : center (ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f)) = ⊥)
    (A : GL (Fin n) (GaloisField p f)) (c : (GaloisField p f)ˣ)
    (hA : A * A = GeneralLinearGroup.scalar (Fin n) c) (hc : ¬ IsSquare (c : GaloisField p f))
    (R : Subgroup (MulAut (ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f))))
    (hRodd : Odd (Nat.card R))
    (hRi : ∀ r ∈ R, r * innerDiagonalAction n _ A = innerDiagonalAction n _ A * r)
    (hRc : ∀ s, innerDiagonalAction n _ A s = s → Odd (orderOf s) → ∀ r ∈ R,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁ := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have hoddK : Odd (Nat.card (GaloisField p f)) := by rw [hcard]; exact hpodd.pow
  have h2 : (2 : GaloisField p f) ≠ 0 := Ring.two_ne_zero
    (CatalogueBHigherLinearInner.ringChar_ne_two_of_odd_card _ hoddK)
  exact commute_nonsplit h2 hn hZ A c hA hc hRodd hRi hRc

end CFSG.ComponentClassification.Foote5.OddLieCore
