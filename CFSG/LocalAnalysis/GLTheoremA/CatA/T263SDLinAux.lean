module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDLinOrder

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.RankThree.CALinearPrimary

variable {K : Type} [Field K] {n : ℕ}

theorem slGL_slConjugation (B : GL (Fin n) K) (g : Matrix.SpecialLinearGroup (Fin n) K) :
    slGL n K (CatalogueBHigherLinearAction.slConjugation n K B g) =
      glA B * slGL n K g * (glA B)⁻¹ := by
  have h1 : Matrix.SpecialLinearGroup.toGL
      (CatalogueBHigherLinearAction.slConjugation n K B g) =
        B * Matrix.SpecialLinearGroup.toGL g * B⁻¹ := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul]
    exact coe_slConjugation B g
  change Matrix.GeneralLinearGroup.toLin (Matrix.SpecialLinearGroup.toGL
    (CatalogueBHigherLinearAction.slConjugation n K B g)) = _
  rw [h1, map_mul, map_mul, map_inv]
  rfl

theorem slGL_scalar_apply {s : Matrix.SpecialLinearGroup (Fin n) K} (hs : s ∈ scalars n K) :
    ∃ l : K, ∀ v : Fin n → K, ((slGL n K s : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) v = l • v := by
  obtain ⟨c, -, hc⟩ := mem_scalars.1 hs
  refine ⟨(c : K), fun v => ?_⟩
  rw [coe_slGL, hc]
  ext i
  simp [Matrix.toLin'_apply, Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem scalars_eq_one_of_units_subsingleton (hK : ∀ c : Kˣ, c = 1)
    {s : Matrix.SpecialLinearGroup (Fin n) K} (hs : s ∈ scalars n K) : s = 1 := by
  obtain ⟨c, -, hc⟩ := mem_scalars.1 hs
  apply Subtype.ext
  rw [hc, hK c, Units.val_one, map_one]
  rfl

theorem units_eq_one_of_card_le_three [Finite K] (h2 : (2 : K) = 0) {E : Type*} [Field E] [Algebra K E]
    [Finite E] (hE : Nat.card E ≤ 3) : Nat.card K = 2 ∧ ∀ c : Kˣ, c = 1 := by
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  haveI := Fintype.ofFinite K
  have hle : Nat.card K ≤ Nat.card E :=
    Nat.card_le_card_of_injective (algebraMap K E) (algebraMap K E).injective
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have hK2 : Nat.card K = 2 := by
    rw [Nat.card_eq_fintype_card, hm] at hle ⊢
    have hm1 : (m : ℕ) = 1 := by
      by_contra hne
      have h2m : 2 ≤ (m : ℕ) := by
        have := m.pos
        omega
      have : 2 ^ 2 ≤ 2 ^ (m : ℕ) := Nat.pow_le_pow_right (by norm_num) h2m
      omega
    rw [hm1]
    norm_num
  refine ⟨hK2, fun c => ?_⟩
  have hcard : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK2]
  obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.1 hcard
  exact Subsingleton.elim _ _

theorem units_pow_eq_one_of_not_dvd {E : Type*} [Field E] [Algebra K E] [Finite E] {p : ℕ}
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card E - 1) {ζ : Kˣ} (hζ : ζ ^ p = 1) : ζ = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hne
  have hord : orderOf ζ = p := orderOf_eq_prime hζ hne
  have hinj : Function.Injective (Units.map (algebraMap K E : K →* E)) :=
    Units.map_injective (algebraMap K E).injective
  have h1 : orderOf (Units.map (algebraMap K E : K →* E) ζ) = p := by
    rw [orderOf_injective _ hinj, hord]
  apply hpq
  rw [← Nat.card_units]
  rw [← h1]
  exact orderOf_dvd_natCard _

theorem scalar_commute (c : Kˣ) (X : GL (Fin n) K) :
    Matrix.GeneralLinearGroup.scalar (Fin n) c * X = X * Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  exact Matrix.scalar_commute _ (fun _ => Commute.all _ _) _

theorem scalar_eq_one_iff (hn : 0 < n) {c : Kˣ} :
    Matrix.GeneralLinearGroup.scalar (Fin n) c = 1 ↔ c = 1 := by
  constructor
  · intro h
    have h1 := congrArg (fun X : GL (Fin n) K => (X : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) h
    simp only [Matrix.GeneralLinearGroup.scalar, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_one,
      Matrix.one_apply_eq] at h1
    refine Units.ext ?_
    simpa [Matrix.scalar_apply, Matrix.diagonal_apply_eq] using h1
  · rintro rfl
    exact map_one _

theorem commutator_scalar_pow_eq_one (hn : 0 < n) {A B : GL (Fin n) K} {p : ℕ} {c : Kˣ}
    (hA : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c) {ζ : Kˣ}
    (hζ : B * A * B⁻¹ * A⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin n) ζ) : ζ ^ p = 1 := by
  have h1 : B * A * B⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin n) ζ * A := by
    rw [← hζ, inv_mul_cancel_right]
  have h2 : (B * A * B⁻¹) ^ p = B * A ^ p * B⁻¹ := conj_pow
  rw [h1, (Commute.mul_pow (scalar_commute ζ A)), hA] at h2
  have h3 : B * Matrix.GeneralLinearGroup.scalar (Fin n) c * B⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin n) c := by
    rw [← scalar_commute c B, mul_assoc, mul_inv_cancel, mul_one]
  rw [h3] at h2
  have h5 : Matrix.GeneralLinearGroup.scalar (Fin n) (ζ ^ p) * Matrix.GeneralLinearGroup.scalar (Fin n) c =
      1 * Matrix.GeneralLinearGroup.scalar (Fin n) c := by
    rw [one_mul, map_pow]
    exact h2
  exact (scalar_eq_one_iff hn).1 (mul_right_cancel h5)

end CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin

end
