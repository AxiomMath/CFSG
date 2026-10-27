module

public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeChar

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Steinberg

variable {τ : Tag} {L : Type} [Field L]

theorem forall_eq_one_or_exists_isPrimitiveRoot_pow {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    (h3 : ∀ s i, a s i ^ 3 = 1) :
    (∀ s i, a s i = 1) ∨ ∃ ω : Lˣ, IsPrimitiveRoot ω 3 ∧
      ∃ k : ι → Fin τ.rank → ZMod 3, ∀ s i, a s i = ω ^ (k s i).val := by
  by_cases hall : ∀ s i, a s i = 1
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨s₀, i₀, h₀⟩ := hall
  have hω : IsPrimitiveRoot (a s₀ i₀) 3 := by
    rw [IsPrimitiveRoot.iff_orderOf]
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one (h3 s₀ i₀)) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) h₀
    · exact h
  refine ⟨a s₀ i₀, hω, ?_⟩
  have hω' : IsPrimitiveRoot ((a s₀ i₀ : Lˣ) : L) 3 := IsPrimitiveRoot.coe_units_iff.2 hω
  have hex : ∀ s i, ∃ n < 3, a s₀ i₀ ^ n = a s i := by
    intro s i
    obtain ⟨n, hn, e⟩ := hω'.eq_pow_of_pow_eq_one (ξ := ((a s i : Lˣ) : L))
      (by rw [← Units.val_pow_eq_pow_val, h3 s i, Units.val_one])
    exact ⟨n, hn, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact e)⟩
  choose n hn e using hex
  refine ⟨fun s i => (n s i : ZMod 3), fun s i => ?_⟩
  rw [ZMod.val_cast_of_lt (hn s i), e s i]

theorem rootChar_eq_pow_triPairing {ω : Lˣ} (hω : ω ^ 3 = 1) {b : Fin τ.rank → Lˣ}
    {k : Fin τ.rank → ZMod 3} (hb : ∀ i, b i = ω ^ (k i).val) (v : Fin τ.rank → ℤ) :
    rootChar b v = ω ^ (triPairing k v).val := by
  classical
  have hsum : ∀ s : Finset (Fin τ.rank),
      ∏ i ∈ s, b i ^ v i = ω ^ (∑ i ∈ s, ((k i).val : ℤ) * v i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add, ih, hb i, ← zpow_natCast,
        ← zpow_mul]
  rw [rootChar, hsum, zpow_eq_zpow_emod' _ hω, ← ZMod.val_intCast, zpow_natCast]
  congr 2
  simp only [triPairing, Int.cast_sum, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem rootChar_pow_mul_pow (x y : Fin τ.rank → Lˣ) (m n : ℕ) (v : Fin τ.rank → ℤ) :
    rootChar (fun i => x i ^ m * y i ^ n) v = rootChar x v ^ m * rootChar y v ^ n := by
  simp only [rootChar, mul_zpow, Finset.prod_mul_distrib, ← Finset.prod_pow]
  congr 1 <;> refine Finset.prod_congr rfl fun i _ => ?_
  · rw [← zpow_natCast (x i), ← zpow_mul, ← zpow_natCast (x i ^ v i), ← zpow_mul, mul_comm]
  · rw [← zpow_natCast (y i), ← zpow_mul, ← zpow_natCast (y i ^ v i), ← zpow_mul, mul_comm]

theorem exists_triPairing_of_pow_three {τ : Tag} {L : Type} [Field L]
    (a : Fin 2 → Fin τ.rank → Lˣ) (h3 : ∀ s i, a s i ^ 3 = 1) :
    ∃ k : Fin 2 → Fin τ.rank → ZMod 3, ∀ (c : Fin 2 → ZMod 3) (v : Fin τ.rank → ℤ),
      rootChar (fun i => a 0 i ^ (c 0).val * a 1 i ^ (c 1).val) v = 1 ↔
        triPairing (c 0 • k 0 + c 1 • k 1) v = 0 := by
  rcases forall_eq_one_or_exists_isPrimitiveRoot_pow a h3 with h1 | ⟨ω, hω, k, hb⟩
  · refine ⟨0, fun c v => ?_⟩
    have ha : (fun i => a 0 i ^ (c 0).val * a 1 i ^ (c 1).val) = 1 :=
      funext fun i => by rw [h1 0 i, h1 1 i, one_pow, one_pow, mul_one, Pi.one_apply]
    rw [ha]
    simp [rootChar, triPairing]
  · refine ⟨k, fun c v => ?_⟩
    have hlin : triPairing (c 0 • k 0 + c 1 • k 1) v =
        c 0 * triPairing (k 0) v + c 1 * triPairing (k 1) v := by
      simp only [triPairing, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
        Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    rw [rootChar_pow_mul_pow, rootChar_eq_pow_triPairing hω.pow_eq_one (hb 0),
      rootChar_eq_pow_triPairing hω.pow_eq_one (hb 1), ← pow_mul, ← pow_mul, ← pow_add,
      hω.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val, mul_comm _ (c 0), mul_comm _ (c 1), hlin]

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore
