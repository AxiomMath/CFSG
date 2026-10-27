module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L3U3

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5GL2 Matrix
open scoped commutatorElement MatrixGroups

namespace MF163

variable {X : Type} [Group X]

section Frame

variable {R : Subgroup X} {S : Sylow 2 R} {z : X} {N : Subgroup X} [N.Normal]
  {F : Type} [Field F] {H : Subgroup (GL (Fin 2) F)} {π : H →* X}

theorem exists_scalar_of_mem [Finite X] (hD : TightDatum R S z)
    (hrange : π.range = N ⊓ Subgroup.centralizer ({z} : Set X)) (hk : CubeKer π)
    (hc : SLCentScalar H) {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : Odd (Nat.card F₀))
    (h4 : 4 ≤ Nat.card F₀) (eJ : slPart H ≃* SL(2, F₀)) {r : X} (hrR : r ∈ R) (hrN : r ∈ N) :
    ∃ A : H, π A = r ∧ ∃ c : Fˣ, (A : GL (Fin 2) F) = GeneralLinearGroup.scalar (Fin 2) c := by
  have hRJ := TA3.TightDatum.le_centralizer_of_gl2 hD hrange hk hF₀ h4 eJ
  have hr : r ∈ π.range := hrange ▸ Subgroup.mem_inf.2 ⟨hrN, hD.cent hrR⟩
  obtain ⟨A, rfl⟩ := hr
  refine ⟨A, rfl, exists_scalar_of_commute hk hc fun B hB => ?_⟩
  exact (Subgroup.mem_centralizer_iff.mp (hRJ hrR) (π B) ⟨B, hB, rfl⟩).symm

theorem exists_quat_not_mem [Finite X] (hD : TightDatum R S z)
    (hrange : π.range = N ⊓ Subgroup.centralizer ({z} : Set X)) (hk : CubeKer π)
    (hc : SLCentScalar H) {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : Odd (Nat.card F₀))
    (h4 : 4 ≤ Nat.card F₀) (eJ : slPart H ≃* SL(2, F₀)) (ι : QuaternionGroup 2 →* X)
    (hι : Function.Injective ι) (hιR : ∀ q, ι q ∈ R) (hιN : ι (QuaternionGroup.a 2) ∈ N) :
    ∃ q : QuaternionGroup 2, ι q ∉ N ∧ q * q = QuaternionGroup.a 2 := by
  have key : ∃ q : QuaternionGroup 2, ι q ∉ N := by
    by_contra hall
    have hmem : ∀ q, ι q ∈ N := fun q => by_contra fun h => hall ⟨q, h⟩
    obtain ⟨A₁, hA₁, c₁, hc₁⟩ :=
      exists_scalar_of_mem hD hrange hk hc hF₀ h4 eJ (hιR (QuaternionGroup.a 1)) (hmem _)
    obtain ⟨A₂, hA₂, c₂, hc₂⟩ :=
      exists_scalar_of_mem hD hrange hk hc hF₀ h4 eJ (hιR (QuaternionGroup.xa 0)) (hmem _)
    have hcomm : A₁ * A₂ = A₂ * A₁ := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hc₁, hc₂, scalar_mul_comm])
    have h1 : ι (QuaternionGroup.a 1 * QuaternionGroup.xa 0) =
        ι (QuaternionGroup.xa 0 * QuaternionGroup.a 1) := by
      rw [map_mul, map_mul, ← hA₁, ← hA₂, ← map_mul, ← map_mul, hcomm]
    exact absurd (hι h1) (by decide)
  obtain ⟨q, hq⟩ := key
  refine ⟨q, hq, ?_⟩
  have hq1 : q ≠ 1 := fun h => hq (by rw [h, map_one]; exact one_mem N)
  have hq2 : q ≠ QuaternionGroup.a 2 := fun h => hq (h ▸ hιN)
  have hQ : ∀ q : QuaternionGroup 2, q ≠ 1 → q ≠ QuaternionGroup.a 2 →
      q * q = QuaternionGroup.a 2 := by decide
  exact hQ q hq1 hq2

theorem commutator_mem_tightCore (hD : TightDatum R S z) {ℓ k : X}
    (hℓ : ℓ ∈ Subgroup.centralizer ({z} : Set X)) (hk : k ∈ tightCore R) :
    ⁅ℓ, k⁆ ∈ tightCore R := by
  have h1 : ℓ * k * ℓ⁻¹ ∈ tightCore R :=
    (Subgroup.mem_normalizer_iff.mp (hD.le_normalizer_core hℓ) k).mp hk
  rw [commutatorElement_def]
  exact mul_mem h1 (inv_mem hk)

theorem exists_scalar_of_mul_self (h2 : (2 : F) ≠ 0) {B : GL (Fin 2) F}
    (hdet : GeneralLinearGroup.det B = 1) (hB : B * B = 1) :
    ∃ c : Fˣ, B = GeneralLinearGroup.scalar (Fin 2) c := by
  have hd : (B : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    simpa using congrArg Units.val hdet
  have e : ∀ i j, ((B * B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j =
      ((1 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j := fun i j => by rw [hB]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Units.val_mul, Units.val_one, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hd
  set a := (B : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set b := (B : Matrix (Fin 2) (Fin 2) F) 0 1 with hb
  set c := (B : Matrix (Fin 2) (Fin 2) F) 1 0 with hc
  set d := (B : Matrix (Fin 2) (Fin 2) F) 1 1 with hdd
  have hs : a + d ≠ 0 := fun hs => h2 (by linear_combination -e00 - hd + a * hs)
  have hb0 : b = 0 := by
    have h : b * (a + d) = 0 := by linear_combination e01
    exact (mul_eq_zero.1 h).resolve_right hs
  have hc0 : c = 0 := by
    have h : c * (a + d) = 0 := by linear_combination e10
    exact (mul_eq_zero.1 h).resolve_right hs
  rw [hb0] at e00 hd
  have had : a = d := by linear_combination -a * hd + d * e00
  have ha0 : a ≠ 0 := fun h => by simp [h] at e00
  refine ⟨Units.mk0 a ha0, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [← ha]
  · simp [← hb, hb0]
  · simp [← hc, hc0]
  · simp [← hdd, ← had]

omit [N.Normal] in
theorem eq_of_mul_self_eq_one_of_mem (hk : CubeKer π) (h2 : (2 : F) ≠ 0) {N1 : H}
    (hN1 : (N1 : GL (Fin 2) F) = -1) {j : X} (hj : j ∈ (slPart H).map π) (hj2 : j * j = 1) :
    j = 1 ∨ j = π N1 := by
  obtain ⟨B, hB, rfl⟩ := hj
  obtain ⟨ω, hω3, hω⟩ := hk (B * B) (by rw [map_mul, hj2])
  have hBB : ((B * B : H) : GL (Fin 2) F) = (B : GL (Fin 2) F) * B := rfl
  have hdet : GeneralLinearGroup.det ((B * B : H) : GL (Fin 2) F) = 1 := by
    rw [hBB, map_mul, mem_slPart.mp hB, one_mul]
  rw [hω, GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
  have hω1 := eq_one_of_sq_of_cube hdet hω3
  rw [hω1, map_one, hBB] at hω
  obtain ⟨c, hc⟩ := exists_scalar_of_mul_self h2 (mem_slPart.mp hB) hω
  exact eq_or_of_scalar_sq hk hN1 hc hj2

end Frame

end MF163

end CFSG.ClassicalInvolution.Q3.TL4
