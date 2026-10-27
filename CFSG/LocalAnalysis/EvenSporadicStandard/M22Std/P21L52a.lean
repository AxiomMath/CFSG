module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21O10
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSporadicStandard.M22Std.P21L52

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] [Finite K]

theorem eq_zero_or_one (hK : Nat.card K = 2) (x : K) : x = 0 ∨ x = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have h2 : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have h := FiniteField.pow_card x
  rw [h2] at h
  have : x * (x - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.1 h1)

theorem units_eq_one (hK : Nat.card K = 2) (c : Kˣ) : c = 1 := by
  rcases eq_zero_or_one hK (c : K) with h | h
  · exact absurd h c.ne_zero
  · exact Units.ext h

theorem ringEquiv_apply (hK : Nat.card K = 2) (σ : K ≃+* K) (x : K) : σ x = x := by
  rcases eq_zero_or_one hK x with rfl | rfl
  · exact map_zero σ
  · exact map_one σ

theorem scalars_eq_bot (hK : Nat.card K = 2) (n : ℕ) : scalars n K = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨c, -, hA⟩
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [hA, units_eq_one hK c]
  simp

noncomputable def eSL (hK : Nat.card K = 2) (n : ℕ) :
    projectiveSL n K ≃* SpecialLinearGroup (Fin n) K :=
  (QuotientGroup.quotientMulEquivOfEq (scalars_eq_bot hK n)).trans QuotientGroup.quotientBot

theorem det_eq_one (hK : Nat.card K = 2) {n : ℕ} (A : GL (Fin n) K) :
    (A : Matrix (Fin n) (Fin n) K).det = 1 := by
  have := congrArg (fun u : Kˣ => (u : K)) (units_eq_one hK (Matrix.GeneralLinearGroup.det A))
  simpa using this

theorem charTwo (hK : Nat.card K = 2) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])

section Alg

variable [Algebra (ZMod 2) K]

theorem finrank_self_eq_one (hK : Nat.card K = 2) : Module.finrank (ZMod 2) K = 1 := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)
  rw [hK, Nat.card_zmod] at h
  have : (2 : ℕ) ^ 1 = 2 ^ Module.finrank (ZMod 2) K := by rw [pow_one]; exact h
  exact (Nat.pow_right_injective le_rfl this).symm

theorem finrank_pi_five (hK : Nat.card K = 2) : Module.finrank (ZMod 2) (Fin 5 → K) = 5 := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    finrank_self_eq_one hK, smul_eq_mul, mul_one]

noncomputable def rep : SpecialLinearGroup (Fin 5) K →* Module.End (ZMod 2) (Fin 5 → K) where
  toFun g := (Matrix.mulVecLin (g : Matrix (Fin 5) (Fin 5) K)).restrictScalars (ZMod 2)
  map_one' := by ext; simp
  map_mul' g h := by
    ext v
    simp

theorem rep_injective : Function.Injective (rep (K := K)) := by
  intro g h hgh
  apply Subtype.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  have := congrArg (fun T => T v) hgh
  simpa [rep] using this

theorem no_order_ten_of_equiv (hK : Nat.card K = 2) {E : Type} [Group E]
    (e : E ≃* projectiveSL 5 K) (g : E) : orderOf g ≠ 10 := by
  intro hg
  let ρ : E →* Module.End (ZMod 2) (Fin 5 → K) :=
    rep.comp ((eSL hK 5).toMonoidHom.comp e.toMonoidHom)
  have hρ : Function.Injective ρ :=
    rep_injective.comp ((eSL hK 5).injective.comp e.injective)
  set y := g ^ 2 with hy
  set u := g ^ 5 with hu
  have hy5 : orderOf y = 5 := by
    rw [hy, orderOf_pow_of_dvd (by norm_num) (by rw [hg]; norm_num), hg]
  have hu2 : orderOf u = 2 := by
    rw [hu, orderOf_pow_of_dvd (by norm_num) (by rw [hg]; norm_num), hg]
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy5; omega
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu2; omega
  have hcomm : u * y = y * u := by rw [hu, hy, ← pow_add, ← pow_add, add_comm]
  have hy5' : y ^ 5 = 1 := by rw [← hy5]; exact pow_orderOf_eq_one y
  have huu : u * u = 1 := by
    rw [← sq, ← hu2]; exact pow_orderOf_eq_one u
  have h1 := P21Field.eq_one_of_commute_five (le_of_eq (finrank_pi_five hK)) (ρ y) (ρ u)
    (by rw [← map_pow, hy5', map_one])
    (fun h => hy1 (hρ (by rw [h, map_one])))
    (by rw [← map_mul, huu, map_one]) (by rw [← map_mul, ← map_mul, hcomm])
  exact hu1 (hρ (by rw [h1, map_one]))

end Alg

end CFSG.EvenSporadicStandard.M22Std.P21L52
