module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.OddClassicalFusion
public import CFSG.CharacterTheory.PSL2Table
public import CFSG.CharacterTheory.Semidihedral.MatrixTorus

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.PSL2Table CFSG.QuasithinUnique
open scoped MatrixGroups

section PSL2

variable {F : Type} [Field F]

theorem nonsplitTorus_isCyclic [Finite F] {ν : F} (hν : ¬ IsSquare ν) :
    IsCyclic (nonsplitTorus ν) := by
  have hν0 : ν ≠ 0 := ne_zero_of_not_isSquare hν
  let a : Fˣ := Units.mk0 (-ν) (neg_ne_zero.mpr hν0)
  have hsq : ¬ IsSquare (-(a : F)) := by simpa [a] using hν
  have hcyc : IsCyclic (CFSG.Semidihedral.MatrixTorus.Torus F a) :=
    CFSG.Semidihedral.MatrixTorus.nonsplit_torus_cyclic F a hsq
  have heq : CFSG.Semidihedral.MatrixTorus.Torus F a = nonsplitSL ν := by
    ext X
    rw [CFSG.Semidihedral.MatrixTorus.mem_torus_iff, mem_nonsplitSL_iff]
    simp only [a, Units.val_mk0, neg_neg]
    exact and_comm
  rw [heq] at hcyc
  exact isCyclic_of_surjective ((mk : SL(2, F) →* PSL(2, F)).subgroupMap (nonsplitSL ν))
    (MonoidHom.subgroupMap_surjective _ _)

variable [Fintype F] [DecidableEq F]

theorem psl2_torus_data (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) :
    ∃ (T₀ : Subgroup PSL(2, F)) (w : PSL(2, F)), IsCyclic T₀ ∧ w ∉ T₀ ∧ w * w = 1 ∧
      (∀ x ∈ T₀, w * x * w⁻¹ = x⁻¹) ∧
      (∀ y : PSL(2, F), y * y = 1 → y ≠ 1 → ∃ x ∈ T₀, IsConj y x) ∧
      (∀ x ∈ T₀, x ≠ 1 → x * x = 1 →
        Nat.card (Subgroup.centralizer ({x} : Set PSL(2, F))) = 2 * Nat.card T₀) ∧
      Nat.card T₀ * 2 =
        (if Fintype.card F % 4 = 1 then Fintype.card F - 1 else Fintype.card F + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hF
  obtain ⟨-, -, hsplit, hnons, hcycs, -, -, -, -, -, -, -, -, -, hcsplit, hcnons, -, -, hinv⟩ :=
    psl2_conjugacy_classes hF hq hν
  have hord : ∀ y : PSL(2, F), y * y = 1 → y ≠ 1 → orderOf y = 2 := fun y hy hy1 =>
    orderOf_eq_prime (by rwa [sq]) hy1
  have h4 := card_mod_four hF
  by_cases h41 : Fintype.card F % 4 = 1
  · refine ⟨splitTorus F, splitWeyl F, hcycs, splitWeyl_not_mem, splitWeyl_mul_self,
      fun x hx => splitWeyl_conj hx, fun y hy hy1 => ?_, fun x hx hx1 hx2 => ?_, ?_⟩
    · exact (hinv y (hord y hy hy1)).1 h41
    · rw [hcsplit x hx hx1, ite_eq_left (by rw [sq]; exact hx2)]
    · rw [ite_eq_left h41]; exact hsplit
  · have h43 : Fintype.card F % 4 = 3 := by omega
    obtain ⟨w, hwT, hw2, hwinv, -⟩ := exists_nonsplitWeyl hF hν
    refine ⟨nonsplitTorus ν, w, nonsplitTorus_isCyclic hν, hwT, hw2, hwinv,
      fun y hy hy1 => ?_, fun x hx hx1 hx2 => ?_, ?_⟩
    · exact (hinv y (hord y hy hy1)).2 h43
    · rw [hcnons x hx hx1, ite_eq_left (by rw [sq]; exact hx2)]
    · rw [ite_eq_right h41]; exact hnons

theorem psl2_nasc (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F)
    (h8 : Fintype.card F % 8 = 1 ∨ Fintype.card F % 8 = 7) :
    NoStrongAb (⊤ : Subgroup PSL(2, F)) := by
  obtain ⟨T₀, w, hcyc, hw, hw2, hinv, hconj, -, hcard⟩ := psl2_torus_data hF hq
  refine nasc_of_torus hcyc hw2 hw hinv hconj ?_
  by_cases h4 : Fintype.card F % 4 = 1
  · rw [ite_eq_left h4] at hcard; omega
  · rw [ite_eq_right h4] at hcard; omega

theorem psl2_odd_torus (hF : ringChar F ≠ 2) (hq : 11 ≤ Fintype.card F)
    (h8 : Fintype.card F % 8 = 3 ∨ Fintype.card F % 8 = 5) :
    ∀ t : PSL(2, F), t * t = 1 → t ≠ 1 → ∃ T : Subgroup PSL(2, F),
      (∀ y ∈ T, y * t = t * y) ∧ (∀ c : PSL(2, F), c * t = t * c → ∀ y ∈ T, c * y * c⁻¹ ∈ T) ∧
      IsCyclic T ∧ ¬ 2 ∣ Nat.card T ∧ T ≠ ⊥ := by
  obtain ⟨T₀, w, hcyc, hw, hw2, hinv, hconj, hcent, hcard⟩ := psl2_torus_data hF (by omega)
  have hcard2 : Nat.card T₀ % 4 = 2 := by
    by_cases h4 : Fintype.card F % 4 = 1
    · rw [ite_eq_left h4] at hcard; omega
    · rw [ite_eq_right h4] at hcard; omega
  have hge : 5 ≤ Nat.card T₀ := by
    by_cases h4 : Fintype.card F % 4 = 1
    · rw [ite_eq_left h4] at hcard; omega
    · rw [ite_eq_right h4] at hcard; omega
  exact odd_torus_data hcyc hconj hcent (m := Nat.card T₀ / 2)
    (Nat.odd_iff.mpr (by omega)) (by omega) (by omega)

theorem psl2_card_mul_two (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) :
    Nat.card PSL(2, F) * 2 = Fintype.card F * (Fintype.card F ^ 2 - 1) := by
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hF
  exact (psl2_conjugacy_classes hF hq hν).1

theorem psl2_card_four (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F)
    (h8 : Fintype.card F % 8 = 3 ∨ Fintype.card F % 8 = 5) :
    ∃ k : ℕ, Odd k ∧ Nat.card PSL(2, F) = 2 ^ 2 * k := by
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hF
  obtain ⟨hN, -⟩ := psl2_conjugacy_classes hF hq hν
  set N := Nat.card PSL(2, F)
  set q := Fintype.card F
  have hq16 : q % 16 = 3 ∨ q % 16 = 5 ∨ q % 16 = 11 ∨ q % 16 = 13 := by omega
  have hsq : q ^ 2 % 16 = 9 := by
    rw [Nat.pow_mod]
    rcases hq16 with h | h | h | h <;> rw [h]
  have hq1 : 1 ≤ q ^ 2 := by
    have : 1 ≤ q := by omega
    nlinarith
  obtain ⟨s, hs⟩ : ∃ s, q ^ 2 - 1 = 16 * s + 8 := ⟨(q ^ 2 - 1) / 16, by omega⟩
  have h2 : N * 2 = (q * (8 * s + 4)) * 2 := by rw [hN, hs]; ring
  have hN' : N = q * (8 * s + 4) := Nat.eq_of_mul_eq_mul_right (by norm_num) h2
  refine ⟨q * (2 * s + 1), ?_, ?_⟩
  · have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
    exact hqodd.mul (odd_two_mul_add_one s)
  · rw [hN']; ring

theorem psl2_card_sylow_four (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F)
    (h8 : Fintype.card F % 8 = 3 ∨ Fintype.card F % 8 = 5) :
    ∀ Q : Subgroup PSL(2, F), IsSylowTwoOf Q ⊤ → Nat.card Q = 4 := by
  intro Q hQ
  obtain ⟨k, hk, hN⟩ := psl2_card_four hF hq h8
  exact card_sylow_eq hQ hk hN

theorem psl2_four_dvd_card (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) :
    4 ∣ Nat.card PSL(2, F) := by
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hF
  obtain ⟨hN, -⟩ := psl2_conjugacy_classes hF hq hν
  set N := Nat.card PSL(2, F)
  set q := Fintype.card F
  have hqodd : q % 2 = 1 := FiniteField.odd_card_of_char_ne_two hF
  have hq8 : q % 8 = 1 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7 := by omega
  have hsq : q ^ 2 % 8 = 1 := by
    rw [Nat.pow_mod]
    rcases hq8 with h | h | h | h <;> rw [h]
  have hq1 : 1 ≤ q ^ 2 := by
    have : 1 ≤ q := by omega
    nlinarith
  obtain ⟨s, hs⟩ : ∃ s, q ^ 2 - 1 = 8 * s := ⟨(q ^ 2 - 1) / 8, by omega⟩
  have h2 : N * 2 = (q * (4 * s)) * 2 := by rw [hN, hs]; ring
  have hN' : N = q * (4 * s) := Nat.eq_of_mul_eq_mul_right (by norm_num) h2
  rw [hN']
  exact Dvd.intro_left (q * s) (by ring)

end PSL2

end CFSG.QuasithinUnique.K1
