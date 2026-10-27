module

public import CFSG.ClassicalInvolution.Phan.AutSU2
public import CFSG.ClassicalInvolution.Phan.Torus

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

@[expose] noncomputable def normOneMap (φ : K ≃+* K) (u : normOne (unitaryInvolution K p f)) :
    normOne (unitaryInvolution K p f) :=
  ⟨Units.map (φ : K →* K) (u : Kˣ), by
    have hu := (mem_normOne (unitaryInvolution K p f)).1 u.2
    rw [mem_normOne]
    show unitaryInvolution K p f (φ ((u : Kˣ) : K)) * φ ((u : Kˣ) : K) = 1
    rw [← map_unitaryInvolution, ← map_mul, hu, map_one]⟩

theorem coe_normOneMap (φ : K ≃+* K) (u : normOne (unitaryInvolution K p f)) :
    (((normOneMap φ u : normOne (unitaryInvolution K p f)) : Kˣ) : K) =
      φ (((u : normOne (unitaryInvolution K p f)) : Kˣ) : K) :=
  rfl

theorem fieldAutSU_torusTwo (φ : K ≃+* K) (u : normOne (unitaryInvolution K p f)) :
    fieldAutSU p f φ 2 (torusTwo (unitaryInvolution K p f) u) =
      torusTwo (unitaryInvolution K p f) (normOneMap φ u) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_coe_fieldAutSU, coe_torusTwo, coe_torusTwo,
    Matrix.diagonal_map (map_zero φ)]
  congr 1
  funext i
  fin_cases i
  · rfl
  · simp [coe_normOneMap]

theorem diagConj_torusTwo (hK : Nat.card K = (p ^ f) ^ 2)
    (t : Fin 2 → normOne (unitaryInvolution K p f)) (u : normOne (unitaryInvolution K p f)) :
    diagConj p f hK t (torusTwo (unitaryInvolution K p f) u) =
      torusTwo (unitaryInvolution K p f) u := by
  refine Subtype.ext ?_
  rw [coe_diagConj]
  refine Units.ext ?_
  simp only [Units.val_mul, coe_diagGL, coe_diagGL_inv, coe_torusTwo, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  have h1 : (((t i : normOne (unitaryInvolution K p f)) : Kˣ) : K) *
      ((((t i : normOne (unitaryInvolution K p f)) : Kˣ)⁻¹ : Kˣ) : K) = 1 := Units.mul_inv _
  linear_combination ((![(u : Kˣ), (u : Kˣ)⁻¹] i : Kˣ) : K) * h1

theorem autB_weylElt_zero_one :
    (((weylElt K p f : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 = 1 := by
  simp [weylElt]

theorem conjDiag_eq_left (hK : Nat.card K = (p ^ f) ^ 2) {c c' : normOne (unitaryInvolution K p f)}
    (h : ∀ A : Su K p f 2, conjDiag hK ![c, 1] A = conjDiag hK ![c', 1] A) : c = c' := by
  have h1 := congrArg (fun B : Su K p f 2 =>
    (((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1)) (h (weylElt K p f))
  simp only [coe_conjDiag_apply] at h1
  rw [autB_weylElt_zero_one] at h1
  exact Subtype.ext (Units.ext (by simpa using h1))

theorem conjDiag_eq_right (hK : Nat.card K = (p ^ f) ^ 2)
    {c c' : normOne (unitaryInvolution K p f)}
    (h : ∀ A : Su K p f 2, conjDiag hK ![1, c] A = conjDiag hK ![1, c'] A) : c = c' := by
  have h1 := congrArg (fun B : Su K p f 2 =>
    (((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1)) (h (weylElt K p f))
  simp only [coe_conjDiag_apply] at h1
  rw [autB_weylElt_zero_one] at h1
  have h2 : ((c : Kˣ)⁻¹ : Kˣ) = ((c' : Kˣ)⁻¹ : Kˣ) := Units.ext (by simpa using h1)
  exact Subtype.ext (inv_injective h2)

theorem autB_coe_apply (hK : Nat.card K = (p ^ f) ^ 2)
    (a b : normOne (unitaryInvolution K p f)) (φ : K ≃+* K) (A : Su K p f 2) (x y : Fin 2) :
    ((((diagConj p f hK ![a, b] * fieldAutSU p f φ 2) A : Su K p f 2) : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) x y =
      ((((![a, b] x : normOne (unitaryInvolution K p f)) : Kˣ)) : K) *
        φ (((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) x y) *
        (((((![a, b] y : normOne (unitaryInvolution K p f)) : Kˣ)⁻¹ : Kˣ)) : K) := by
  rw [MulAut.mul_apply, coe_diagConj, Units.val_mul, Units.val_mul, coe_diagGL, coe_diagGL_inv,
    Matrix.mul_diagonal, Matrix.diagonal_mul, coe_coe_fieldAutSU, Matrix.map_apply]

theorem aut_conjDiag_left (hK : Nat.card K = (p ^ f) ^ 2)
    (a b : normOne (unitaryInvolution K p f)) (φ : K ≃+* K) (c : normOne (unitaryInvolution K p f))
    (A : Su K p f 2) :
    (diagConj p f hK ![a, b] * fieldAutSU p f φ 2) (conjDiag hK ![c, 1] A) =
      conjDiag hK ![normOneMap φ c, 1] ((diagConj p f hK ![a, b] * fieldAutSU p f φ 2) A) := by
  refine Subtype.ext (Units.ext (Matrix.ext fun x y => ?_))
  have hv : ∀ z : Fin 2, ((((![normOneMap φ c, 1] z : normOne (unitaryInvolution K p f)) : Kˣ)) :
      K) = φ ((((![c, 1] z : normOne (unitaryInvolution K p f)) : Kˣ)) : K) := by
    intro z
    fin_cases z <;> simp [coe_normOneMap]
  have hv' : ∀ z : Fin 2, (((((![normOneMap φ c, 1] z : normOne (unitaryInvolution K p f)) : Kˣ)⁻¹ :
      Kˣ)) : K) = φ (((((![c, 1] z : normOne (unitaryInvolution K p f)) : Kˣ)⁻¹ : Kˣ)) : K) := by
    intro z
    fin_cases z <;> simp [coe_normOneMap]
  simp only [autB_coe_apply, coe_conjDiag_apply, hv, hv', map_mul]
  ring

theorem aut_conjDiag_right (hK : Nat.card K = (p ^ f) ^ 2)
    (a b : normOne (unitaryInvolution K p f)) (φ : K ≃+* K) (c : normOne (unitaryInvolution K p f))
    (A : Su K p f 2) :
    (diagConj p f hK ![a, b] * fieldAutSU p f φ 2) (conjDiag hK ![1, c] A) =
      conjDiag hK ![1, normOneMap φ c] ((diagConj p f hK ![a, b] * fieldAutSU p f φ 2) A) := by
  refine Subtype.ext (Units.ext (Matrix.ext fun x y => ?_))
  have hv : ∀ z : Fin 2, ((((![1, normOneMap φ c] z : normOne (unitaryInvolution K p f)) : Kˣ)) :
      K) = φ ((((![1, c] z : normOne (unitaryInvolution K p f)) : Kˣ)) : K) := by
    intro z
    fin_cases z <;> simp [coe_normOneMap]
  have hv' : ∀ z : Fin 2, (((((![1, normOneMap φ c] z : normOne (unitaryInvolution K p f)) : Kˣ)⁻¹ :
      Kˣ)) : K) = φ (((((![1, c] z : normOne (unitaryInvolution K p f)) : Kˣ)⁻¹ : Kˣ)) : K) := by
    intro z
    fin_cases z <;> simp [coe_normOneMap]
  simp only [autB_coe_apply, coe_conjDiag_apply, hv, hv', map_mul]
  ring

theorem ringEquiv_eq_of_eq_on_normOne (hK : Nat.card K = (p ^ f) ^ 2) (φ φ' : K ≃+* K)
    (h : ∀ u : normOne (unitaryInvolution K p f),
      φ (((u : normOne (unitaryInvolution K p f)) : Kˣ) : K) =
        φ' (((u : normOne (unitaryInvolution K p f)) : Kˣ) : K)) : φ = φ' := by
  let S : Subfield K := RingHom.eqLocusField (φ : K →+* K) (φ' : K →+* K)
  let ι : normOne (unitaryInvolution K p f) → S := fun u => ⟨((u : Kˣ) : K), h u⟩
  have hι : Function.Injective ι := fun u v huv =>
    Subtype.ext (Units.ext (congrArg Subtype.val huv))
  have hcard : p ^ f + 1 ≤ Nat.card S := by
    rw [← card_normOne hK]
    exact Nat.card_le_card_of_injective ι hι
  have hKS : Nat.card K = Nat.card S ^ Module.finrank S K := Module.natCard_eq_pow_finrank
  have hone : Module.finrank S K = 1 := by
    rcases Nat.lt_or_ge (Module.finrank S K) 2 with hlt | hge
    · rcases Nat.lt_or_ge (Module.finrank S K) 1 with hlt1 | hge1
      · have h0 : Module.finrank S K = 0 := by omega
        rw [h0, pow_zero] at hKS
        exact absurd hKS (Finite.one_lt_card (α := K)).ne'
      · omega
    · exfalso
      have h1 : (p ^ f + 1) ^ 2 ≤ Nat.card S ^ 2 := Nat.pow_le_pow_left hcard 2
      have h2 : Nat.card S ^ 2 ≤ Nat.card S ^ Module.finrank S K :=
        Nat.pow_le_pow_right (by omega) hge
      have h3 : (p ^ f) ^ 2 < (p ^ f + 1) ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
      omega
  rw [hone, pow_one] at hKS
  have hbij : Function.Bijective (Subtype.val : S → K) :=
    Subtype.val_injective.bijective_of_nat_card_le hKS.le
  refine RingEquiv.ext fun x => ?_
  obtain ⟨s, rfl⟩ := hbij.2 x
  exact s.2

end CFSG.ClassicalInvolution.Phan.Q3G
