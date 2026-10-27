module

public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.LieType.Steinberg.CentralExt.UnitaryField

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec5.Lem55

open Matrix CFSG.Assembly.LowTwoRank CFSG.SectionRank.ClassicalOdd CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary

section SU

variable {K : Type} [Field K] {σ : K ≃+* K}

def isoA : Fin 4 → K := ![1, 1, 0, 0]

def isoB : Fin 4 → K := ![0, 0, 1, 1]

theorem herm_isoA_isoA [CharP K 2] : herm σ (isoA (K := K)) isoA = 0 := by
  simp [herm_def, isoA, Fin.sum_univ_four, CharTwo.add_self_eq_zero]

theorem herm_isoB_isoB [CharP K 2] : herm σ (isoB (K := K)) isoB = 0 := by
  simp [herm_def, isoB, Fin.sum_univ_four, CharTwo.add_self_eq_zero]

theorem herm_isoA_isoB : herm σ (isoA (K := K)) isoB = 0 := by
  simp [herm_def, isoA, isoB, Fin.sum_univ_four]

theorem herm_isoB_isoA : herm σ (isoB (K := K)) isoA = 0 := by
  simp [herm_def, isoA, isoB, Fin.sum_univ_four]

theorem herm_isoA_e0 : herm σ (isoA (K := K)) (Pi.single 0 1) = 1 := by
  simp [herm_def, isoA, Pi.single_apply]

theorem herm_isoB_e0 : herm σ (isoB (K := K)) (Pi.single 0 1) = 0 := by
  simp [herm_def, isoB, Pi.single_apply]

theorem herm_isoA_e2 : herm σ (isoA (K := K)) (Pi.single 2 1) = 0 := by
  simp [herm_def, isoA, Pi.single_apply]

theorem herm_isoB_e2 : herm σ (isoB (K := K)) (Pi.single 2 1) = 1 := by
  simp [herm_def, isoB, Pi.single_apply]

theorem tv_comm (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {a b : Fin n → K} (ha : herm σ a a = 0)
    (hb : herm σ b b = 0) (hab : herm σ a b = 0) (hba : herm σ b a = 0) {c d : K}
    (hc : c + σ c = 0) (hd : d + σ d = 0) :
    tv hσ ha hc * tv hσ hb hd = tv hσ hb hd * tv hσ ha hc := by
  apply ext_smul
  intro v
  rw [mul_smul, mul_smul, tv_smul, tv_smul, tv_smul, tv_smul]
  simp only [herm_add_right, herm_smul_right, hab, hba, mul_zero, add_zero]
  module

variable [Finite K]

theorem two_mul_le_pRank_psu_even {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) :
    2 * f ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (StatedProj (StatedSU 4 (2 ^ f) K))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := charP_of_card_sq (p := 2) (f := f) hK
  set σ : K ≃+* K := CFSG.LieType.BorelTits.unitaryInvolution K 2 f with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution hK
  have hAA : herm σ (isoA (K := K)) isoA = 0 := herm_isoA_isoA
  have hBB : herm σ (isoB (K := K)) isoB = 0 := herm_isoB_isoB
  have hcomm : ∀ (x y : Multiplicative (traceZero σ)),
      Commute (tvHom hσ.invol hAA x) (tvHom hσ.invol hBB y) := fun x y =>
    tv_comm hσ.invol hAA hBB herm_isoA_isoB herm_isoB_isoA ((mem_traceZero σ).mp x.toAdd.2)
      ((mem_traceZero σ).mp y.toAdd.2)
  let φ' : Multiplicative (traceZero σ) × Multiplicative (traceZero σ) →* SUid σ 4 :=
    (tvHom hσ.invol hAA).noncommCoprod (tvHom hσ.invol hBB) hcomm
  let φ : Multiplicative (traceZero σ) × Multiplicative (traceZero σ) →* GL (Fin 4) K :=
    (SUid σ 4).subtype.comp φ'
  have hφ_apply : ∀ x y : Multiplicative (traceZero σ), φ' (x, y) =
      tvHom hσ.invol hAA x * tvHom hσ.invol hBB y := fun x y =>
    MonoidHom.noncommCoprod_apply _ _ _ (x, y)
  have hdouble : ∀ c : traceZero σ, c + c = 0 := fun c =>
    Subtype.ext (by simp [CharTwo.add_self_eq_zero])
  have hsq : ∀ x : Multiplicative (traceZero σ), x ^ 2 = 1 := fun x => by
    rw [pow_two]
    apply Multiplicative.toAdd.injective
    simp [hdouble]
  have hpow : ∀ a : Multiplicative (traceZero σ) × Multiplicative (traceZero σ), a ^ 2 = 1 :=
    fun a => Prod.ext (hsq a.1) (hsq a.2)
  have hcomm' : ∀ a b : Multiplicative (traceZero σ) × Multiplicative (traceZero σ),
      a * b = b * a := fun a b => Prod.ext (mul_comm _ _) (mul_comm _ _)
  have hcard1 : Nat.card (Multiplicative (traceZero σ)) = 2 ^ f := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (traceZero σ) ≃ _)]
    exact CFSG.LieType.Steinberg.card_traceZero hK
  have hcard : Nat.card (Multiplicative (traceZero σ) × Multiplicative (traceZero σ)) =
      2 ^ (f + f) := by
    rw [Nat.card_prod, hcard1, pow_add]
  have hA0 : (isoA (K := K)) ≠ 0 := fun h => by
    have := congrFun h 0
    simp [isoA] at this
  have hB : ∀ y : Multiplicative (traceZero σ), tvHom hσ.invol hBB y • isoA = isoA := fun y => by
    rw [tvHom_smul, herm_isoB_isoA, mul_zero, zero_smul, add_zero]
  have hA : ∀ x : Multiplicative (traceZero σ), tvHom hσ.invol hAA x • isoA = isoA := fun x => by
    rw [tvHom_smul, hAA, mul_zero, zero_smul, add_zero]
  have hfix : ∀ a : Multiplicative (traceZero σ) × Multiplicative (traceZero σ),
      ((φ a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ isoA = isoA := by
    rintro ⟨x, y⟩
    have h1 : ((φ (x, y) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ isoA =
        (φ' (x, y)) • isoA := rfl
    rw [h1, hφ_apply, mul_smul, hB, hA]
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ h
    have h' : φ' (x, y) = 1 := Subtype.ext (by simpa [φ] using h)
    have hx : (x.toAdd : K) = 0 := by
      have h2 := congrArg (fun g : SUid σ 4 => g • (Pi.single 0 1 : Fin 4 → K)) h'
      simp only [hφ_apply, mul_smul, one_smul] at h2
      rw [tvHom_smul hσ.invol hBB y, herm_isoB_e0, mul_zero, zero_smul, add_zero,
        tvHom_smul hσ.invol hAA, herm_isoA_e0, mul_one] at h2
      have h3 := congrFun h2 0
      simpa [isoA] using h3
    have hy : (y.toAdd : K) = 0 := by
      have h2 := congrArg (fun g : SUid σ 4 => g • (Pi.single 2 1 : Fin 4 → K)) h'
      simp only [hφ_apply, mul_smul, one_smul] at h2
      rw [tvHom_smul hσ.invol hBB y, herm_isoB_e2, mul_one, tvHom_smul hσ.invol hAA] at h2
      simp only [herm_add_right, herm_smul_right, herm_isoA_isoB, herm_isoA_e2, mul_zero, add_zero,
        zero_smul] at h2
      have h3 := congrFun h2 2
      simpa [isoB] using h3
    have hx' : x = 1 := Multiplicative.toAdd.injective (Subtype.ext hx)
    have hy' : y = 1 := Multiplicative.toAdd.injective (Subtype.ext hy)
    rw [hx', hy']
    rfl
  have := le_pRank_statedProj (H := SUid σ 4)
    (A := Multiplicative (traceZero σ) × Multiplicative (traceZero σ)) (p := 2) (k := f + f)
    one_lt_two hcomm' hpow hcard φ hinj (fun a => (φ' a).2) hA0 hfix
  rw [SUid_eq_statedSU hK 4] at this
  omega

end SU

end CFSG.GH74.GLS.Stage1.Thm3.Sec5.Lem55
