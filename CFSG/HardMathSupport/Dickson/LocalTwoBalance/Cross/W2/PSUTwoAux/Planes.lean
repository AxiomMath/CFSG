module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary2DMain
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisRed
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossUniPlane

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo

open Matrix CFSG.Open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

theorem mul_pow_three_of_comm_central {G : Type*} [Group G] {x y s : G}
    (hs : ∀ g : G, s * g = g * s) (hxy : x * y = y * x * s) (hs3 : s ^ 3 = 1) :
    (x * y) ^ 3 = x ^ 3 * y ^ 3 :=
  Heis.mul_pow_prime_central hs (by rw [hxy, hs (y * x)]) Nat.prime_three (by norm_num) hs3

theorem comm_central_sq {G : Type*} [Group G] {x y s : G} (hs : ∀ g : G, s * g = g * s)
    (hxy : x * y = y * x * s) : x * (y * y) = (y * y) * x * (s * s) := by
  calc x * (y * y) = (x * y) * y := by group
    _ = (y * x * s) * y := by rw [hxy]
    _ = y * x * (s * y) := by group
    _ = y * x * (y * s) := by rw [hs y]
    _ = y * (x * y) * s := by group
    _ = y * (y * x * s) * s := by rw [hxy]
    _ = (y * y) * x * (s * s) := by group

theorem mul_sq_pow_three_of_comm_central {G : Type*} [Group G] {x y s : G}
    (hs : ∀ g : G, s * g = g * s) (hxy : x * y = y * x * s) (hs3 : s ^ 3 = 1) :
    (x * (y * y)) ^ 3 = x ^ 3 * (y ^ 3 * y ^ 3) := by
  have h2 := comm_central_sq hs hxy
  have hss : ∀ g : G, (s * s) * g = g * (s * s) := fun g =>
    ((show Commute s g from hs g).mul_left (show Commute s g from hs g)).eq
  have hs33 : (s * s) ^ 3 = 1 := by
    calc (s * s) ^ 3 = (s ^ 3) ^ 2 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [hs3, one_pow]
  rw [mul_pow_three_of_comm_central hss h2 hs33]
  congr 1
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem exists_cube_relation (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2) (a b : Kˣ) :
    a = 1 ∨ b = 1 ∨ a * b = 1 ∨ a * (b * b) = 1 := by
  by_cases ha : a = 1
  · exact Or.inl ha
  by_cases hb : b = 1
  · exact Or.inr (Or.inl hb)
  obtain ⟨m, hm⟩ := exists_pow_eq_of_ne_one h hq ha b
  have h3 : a ^ 3 = 1 := unit_pow_three_eq_one h hq a
  have hmod : a ^ m = a ^ (m % 3) := by
    conv_lhs => rw [← Nat.mod_add_div m 3, pow_add, pow_mul, h3, one_pow, mul_one]
  rw [hmod] at hm
  rcases (by omega : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2) with h0 | h1 | h2
  · rw [h0, pow_zero] at hm
    exact absurd hm.symm hb
  · rw [h1, pow_one] at hm
    right; right; right
    rw [← hm]
    calc a * (a * a) = a ^ 3 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := h3
  · rw [h2] at hm
    right; right; left
    rw [← hm]
    calc a * a ^ 2 = a ^ 3 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := h3

theorem exists_split_lift (hn : 4 ≤ n) (hq : ℓ ^ f = 2)
    {D : Subgroup (MulAut (primeFormP h (idGram K n)))} (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 3 ^ 2) (hDl : D ≤ primeFormD h (idGram K n)) :
    ∃ S : primeFormUnitary h (idGram K n), S ^ 3 = 1 ∧
      primeFormConjHom h (idGram K n) S ∈ D ∧ primeFormConjHom h (idGram K n) S ≠ 1 := by
  classical
  have hfin := h.finite
  have hn3 : 3 ≤ n := by omega
  have hne : ¬(n = 3 ∧ ℓ ^ f = 2) := fun ⟨h1, _⟩ => by omega
  obtain ⟨A, B, c, hAD, hBD, hA1, hBA, hAB, hcp, -, -⟩ :=
    exists_plane_lifts_unitary hn3 hne Nat.prime_three hD hcard hDl
  have hA3 : primeFormConjHom h (idGram K n) (A ^ 3) = 1 := by
    rw [map_pow]; exact hD.2 _ hAD
  have hB3 : primeFormConjHom h (idGram K n) (B ^ 3) = 1 := by
    rw [map_pow]; exact hD.2 _ hBD
  obtain ⟨a, -, ha⟩ := (primeFormConjHom_eq_one_iff_of_ne hn3 hne _).mp hA3
  obtain ⟨b, -, hb⟩ := (primeFormConjHom_eq_one_iff_of_ne hn3 hne _).mp hB3
  rw [Subgroup.coe_pow] at ha hb
  have hρB3 : primeFormConjHom h (idGram K n) B ^ 3 = 1 := hD.2 _ hBD
  have hcen : ∀ g : GL (Fin n) K, GeneralLinearGroup.scalar (Fin n) c * g =
      g * GeneralLinearGroup.scalar (Fin n) c := fun g => GeneralLinearGroup.scalar_commute c g
  have hc3 : GeneralLinearGroup.scalar (Fin n) c ^ 3 = 1 := by rw [← map_pow, hcp, map_one]
  have key : ∀ S : primeFormUnitary h (idGram K n), (S : GL (Fin n) K) ^ 3 = 1 → S ^ 3 = 1 :=
    fun S hS => Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hS)
  rcases exists_cube_relation h hq a b with h1 | h1 | h1 | h1
  · refine ⟨A, key A ?_, hAD, hA1⟩
    rw [ha, h1, map_one]
  · refine ⟨B, key B ?_, hBD, fun h0 => hBA ?_⟩
    · rw [hb, h1, map_one]
    · rw [h0]; exact Subgroup.one_mem _
  · refine ⟨A * B, key _ ?_, ?_, ?_⟩
    · rw [Subgroup.coe_mul, mul_pow_three_of_comm_central hcen hAB hc3, ha, hb, ← map_mul, h1,
        map_one]
    · rw [map_mul]; exact D.mul_mem hAD hBD
    · intro h0
      rw [map_mul] at h0
      refine hBA ?_
      rw [eq_inv_of_mul_eq_one_right h0]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  · refine ⟨A * (B * B), key _ ?_, ?_, ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul,
        mul_sq_pow_three_of_comm_central hcen hAB hc3, ha, hb, ← map_mul, ← map_mul, h1, map_one]
    · rw [map_mul, map_mul]; exact D.mul_mem hAD (D.mul_mem hBD hBD)
    · intro h0
      rw [map_mul, map_mul] at h0
      have h2 : primeFormConjHom h (idGram K n) B * primeFormConjHom h (idGram K n) B =
          (primeFormConjHom h (idGram K n) A)⁻¹ := eq_inv_of_mul_eq_one_right h0
      have h3 : primeFormConjHom h (idGram K n) B =
          (primeFormConjHom h (idGram K n) B * primeFormConjHom h (idGram K n) B)⁻¹ :=
        eq_inv_of_mul_eq_one_left (by
          calc primeFormConjHom h (idGram K n) B * (primeFormConjHom h (idGram K n) B *
              primeFormConjHom h (idGram K n) B) = primeFormConjHom h (idGram K n) B ^ 3 := by
                simp only [pow_succ, pow_zero, one_mul, mul_assoc]
            _ = 1 := hρB3)
      refine hBA ?_
      rw [h3, h2, inv_inv]
      exact Subgroup.mem_zpowers _

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo
