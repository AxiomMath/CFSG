module

public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryField
public import CFSG.LieType.BorelTits.UnitaryForm

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LieType.BorelTits CFSG.StandardType.TableBUF

section Restrict

variable {F : Type} [Field F]

@[expose] def restrictSub (σ : F ≃+* F) (S : Subfield F) (h : ∀ x, x ∈ S ↔ σ x ∈ S) :
    S ≃+* S where
  toFun x := ⟨σ x, (h x).1 x.2⟩
  invFun x := ⟨σ.symm x, (h _).2 (by simp)⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply (x : F))
  right_inv x := Subtype.ext (σ.apply_symm_apply (x : F))
  map_mul' x y := Subtype.ext (map_mul σ (x : F) y)
  map_add' x y := Subtype.ext (map_add σ (x : F) y)

theorem coe_restrictSub_pow (σ : F ≃+* F) (S : Subfield F) (h : ∀ x, x ∈ S ↔ σ x ∈ S) (n : ℕ)
    (x : S) : (((restrictSub σ S h) ^ n) x : F) = (σ ^ n) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, RingAut.mul_apply, RingAut.mul_apply, ih]
    rfl

theorem iter_three (σ : F ≃+* F) (x : F) : (σ ^ 3) x = σ (σ (σ x)) := by
  simp [pow_succ, RingAut.mul_apply]

end Restrict

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem sigma_comm_bar (σ : F ≃+* F) (x : F) :
    σ (unitaryInvolution F p f x) = unitaryInvolution F p f (σ x) := by
  rw [unitaryInvolution_apply, unitaryInvolution_apply, map_pow]

theorem exists_bar_fixed_not_sigma_fixed (hF : Nat.card F = (p ^ f) ^ 2) {σ : F ≃+* F}
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) :
    ∃ y : F, unitaryInvolution F p f y = y ∧ σ y ≠ y := by
  by_contra h
  push Not at h
  apply hσ1
  refine RingEquiv.ext fun x => ?_
  have hinv := unitaryInvolution_involutive hF
  have ht : unitaryInvolution F p f (x + unitaryInvolution F p f x) = x + unitaryInvolution F p f x := by
    rw [map_add, hinv, add_comm]
  have hn : unitaryInvolution F p f (x * unitaryInvolution F p f x) = x * unitaryInvolution F p f x := by
    rw [map_mul, hinv, mul_comm]
  have h1 := h _ ht
  have h2 := h _ hn
  obtain ⟨t, htd⟩ : ∃ t, t = x + unitaryInvolution F p f x := ⟨_, rfl⟩
  obtain ⟨n, hnd⟩ : ∃ n, n = x * unitaryInvolution F p f x := ⟨_, rfl⟩
  rw [← htd] at h1
  rw [← hnd] at h2
  have e : σ x ^ 2 - t * σ x + n = 0 := by
    have := congrArg σ (show x ^ 2 - t * x + n = 0 by rw [htd, hnd]; ring)
    simp only [map_sub, map_add, map_mul, map_pow, map_zero, h1, h2] at this
    exact this
  have e2 : (σ x - x) * (σ x - unitaryInvolution F p f x) = 0 := by
    rw [htd] at e
    rw [hnd] at e
    linear_combination e
  rcases mul_eq_zero.1 e2 with h3 | h3
  · exact sub_eq_zero.1 h3
  · have h4 : σ x = unitaryInvolution F p f x := sub_eq_zero.1 h3
    have h5 : σ (unitaryInvolution F p f x) = x := by
      rw [sigma_comm_bar, h4, hinv]
    have h6 : (σ ^ 3) x = x := by rw [hσ3]; rfl
    rw [iter_three, h4, h5] at h6
    exact h6

theorem exists_bar_fixed_hilbert90 (hF : Nat.card F = (p ^ f) ^ 2) {σ : F ≃+* F}
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) {lam : F} (hl : unitaryInvolution F p f lam = lam)
    (hN : lam * σ lam * σ (σ lam) = 1) :
    ∃ ν : F, ν ≠ 0 ∧ unitaryInvolution F p f ν = ν ∧ σ ν = lam * ν := by
  set S : Subfield F := RingHom.eqLocusField
    ((unitaryInvolution F p f : F ≃+* F) : F →+* F) (RingHom.id F) with hSdef
  have hS : ∀ x, x ∈ S ↔ unitaryInvolution F p f x = x := fun x => Iff.rfl
  have hSσ : ∀ x, x ∈ S ↔ σ x ∈ S := fun x => by
    rw [hS, hS, ← sigma_comm_bar (p := p) (f := f)]
    exact ⟨fun h => by rw [h], fun h => σ.injective h⟩
  set φ := restrictSub σ S hSσ with hφdef
  have hφ3 : φ ^ 3 = 1 := RingEquiv.ext fun x => Subtype.ext (by
    rw [coe_restrictSub_pow, hσ3]; rfl)
  obtain ⟨y, hy, hy'⟩ := exists_bar_fixed_not_sigma_fixed hF hσ3 hσ1
  have hφ1 : φ ≠ 1 := fun h => hy' (by
    have := congrArg (fun e : S ≃+* S => ((e ⟨y, (hS y).2 hy⟩ : S) : F)) h
    exact this)
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    simp at hN
  have hlinv : unitaryInvolution F p f lam⁻¹ = lam⁻¹ := by rw [map_inv₀, hl]
  set δ : S := ⟨lam⁻¹, (hS _).2 hlinv⟩ with hδ
  have hδ0 : δ ≠ 0 := fun h => hlam0 (inv_eq_zero.1 (congrArg Subtype.val h))
  have hnorm : partNorm φ δ 3 = 1 := by
    apply Subtype.ext
    have hφc : ∀ x : S, ((φ x : S) : F) = σ x := fun x => rfl
    have h0 : partNorm φ δ 0 = 1 := by simp [partNorm]
    have h1' : σ lam ≠ 0 := fun h => hlam0 (σ.injective (by rw [h, map_zero]))
    have h2' : σ (σ lam) ≠ 0 := fun h => h1' (σ.injective (by rw [h, map_zero]))
    rw [partNorm_succ', partNorm_succ', partNorm_succ', h0]
    simp only [Subfield.coe_mul, hφc, map_one, mul_one, Subfield.coe_one, hδ, map_mul, map_inv₀]
    calc lam⁻¹ * ((σ lam)⁻¹ * (σ (σ lam))⁻¹) = (lam * σ lam * σ (σ lam))⁻¹ := by
          simp only [mul_inv, mul_assoc]
      _ = 1 := by rw [hN, inv_one]
  obtain ⟨b, hb0, hb⟩ := exists_hilbert90 Nat.prime_three hφ3 hφ1 hδ0 hnorm
  refine ⟨b, fun h => hb0 (Subtype.ext h), (hS _).1 b.2, ?_⟩
  have := congrArg Subtype.val hb
  have e : ((φ b : S) : F) = σ b := rfl
  rw [e] at this
  rw [this]
  simp [hδ]

end CFSG.HardMathSupport.Solomon.Coordinator
