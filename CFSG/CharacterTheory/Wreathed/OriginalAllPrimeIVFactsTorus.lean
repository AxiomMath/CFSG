module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeIVFactsArith
public import CFSG.CharacterTheory.Wreathed.CyclicCentralSL2Extension
public import CFSG.CharacterTheory.Wreathed.OddFieldFixedTorusDerivedCentralizer

public section

namespace CFSG.Wreathed.OriginalAllPrime.IVFacts

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.OddFieldTorus

variable {F : Type} [Field F]

@[expose] def fixedW (W : Subgroup (SpecialLinearGroup (Fin 2) F)) (τ : F ≃+* F) :
    Subgroup (SpecialLinearGroup (Fin 2) F) :=
  W ⊓ (SpecialLinearGroup.map τ.toRingHom).eqLocus (MonoidHom.id _)

theorem mem_fixedW {W : Subgroup (SpecialLinearGroup (Fin 2) F)} {τ : F ≃+* F}
    {g : SpecialLinearGroup (Fin 2) F} : g ∈ fixedW W τ ↔ g ∈ W ∧ fieldSL F τ g = g :=
  Iff.rfl

theorem card_fixedW (W : Subgroup (SpecialLinearGroup (Fin 2) F)) (τ : F ≃+* F) :
    Nat.card (fixedW W τ) =
      Nat.card {g // g ∈ W ∧ SpecialLinearGroup.map τ.toRingHom g = g} :=
  rfl

theorem fieldSL_pow_eq {τ : F ≃+* F} {g : SpecialLinearGroup (Fin 2) F}
    (h : fieldSL F τ g = g) (k : ℕ) : fieldSL F (τ ^ k) g = g := by
  induction k with
  | zero => rw [pow_zero, fieldSL_one, MulAut.one_apply]
  | succ k ih => rw [pow_succ, fieldSL_mul, MulAut.mul_apply, h, ih]

theorem fieldSL_mem {W : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hW : ∀ g, g ∈ W ↔ g ∈ torus F ∧ Odd (orderOf g)) (τ : F ≃+* F)
    {g : SpecialLinearGroup (Fin 2) F} (hg : g ∈ W) : fieldSL F τ g ∈ W :=
  fieldAction_mem W hW τ hg

section Arith

variable [Fintype F] {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
  (hcard : Nat.card F = p ^ f) {m : ℕ}
  (hm2 : m = 2 ^ padicValInt 2 ((p ^ f : ℕ) - (if p ^ f % 4 = 1 then (1 : ℤ) else -1)))
  {Sigma : Subgroup (F ≃+* F)} (hd : Odd (Nat.card Sigma))
  {W : Subgroup (SpecialLinearGroup (Fin 2) F)}
  (hW : ∀ g, g ∈ W ↔ g ∈ torus F ∧ Odd (orderOf g))

include hp hpodd hf hcard hm2 hd hW

omit [Fintype F] in
theorem isCyclic_W : IsCyclic W := by
  have hp2 : p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hpodd)
  obtain ⟨-, -, -, -, hall⟩ := odd_field_fixed_torus_derived_centralizer hp hp2 hf hcard _ rfl m
    hm2 Sigma hd
  exact (hall W hW).1

theorem torus_arith (τ : F ≃+* F) (hτ : τ ∈ Sigma) :
    ∃ q₁ : ℕ, 3 ≤ q₁ ∧ p ^ f = q₁ ^ orderOf τ ∧
      (Nat.card W : ℤ) * m = (p ^ f : ℕ) - (if p ^ f % 4 = 1 then (1 : ℤ) else -1) ∧
      (Nat.card (fixedW W τ) : ℤ) * m = (q₁ : ℤ) - (if p ^ f % 4 = 1 then (1 : ℤ) else -1) := by
  have hp2 : p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hpodd)
  obtain ⟨-, -, -, -, hall⟩ := odd_field_fixed_torus_derived_centralizer hp hp2 hf hcard _ rfl m
    hm2 Sigma hd
  obtain ⟨-, hcardW, hfix, -⟩ := hall W hW
  obtain ⟨hq, -, hm1, hcardf, -⟩ := hfix τ hτ
  set q₁ := Nat.card {a : F // τ a = a} with hq₁
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmdvd : (m : ℤ) ∣ ((p ^ f : ℕ) : ℤ) - (if p ^ f % 4 = 1 then (1 : ℤ) else -1) := by
    rw [hm2]
    push_cast
    exact padicValInt_dvd _
  have hmdvd₁ : (m : ℤ) ∣ (q₁ : ℤ) - (if p ^ f % 4 = 1 then (1 : ℤ) else -1) := by
    rw [← hm1]
    push_cast
    exact padicValInt_dvd _
  refine ⟨q₁, ?_, hq, ?_, ?_⟩
  ·
    have h2 : 2 ≤ q₁ := by
      have hne : (⟨0, map_zero τ⟩ : {a : F // τ a = a}) ≠ ⟨1, map_one τ⟩ := by
        intro h
        exact zero_ne_one (congrArg Subtype.val h)
      have : Nontrivial {a : F // τ a = a} := ⟨⟨_, _, hne⟩⟩
      exact Finite.one_lt_card
    have hodd : Odd (q₁ ^ orderOf τ) := by
      rw [← hq]
      exact hpodd.pow
    have hord0 : orderOf τ ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hq
      have := Nat.one_lt_pow (by omega : f ≠ 0) hp.one_lt
      omega
    have hq₁odd : Odd q₁ := (Nat.odd_pow_iff hord0).mp hodd
    obtain ⟨k, hk⟩ := hq₁odd
    omega
  · rw [hcardW, Int.ediv_mul_cancel hmdvd]
  · rw [card_fixedW, hcardf, Int.ediv_mul_cancel hmdvd₁]

theorem pow_succ_dvd_card_W (τ : F ≃+* F) (hτ : τ ∈ Sigma) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hτr : orderOf τ = r) {v : ℕ} (hv1 : 1 ≤ v)
    (hv : r ^ v ∣ Nat.card (fixedW W τ)) : r ^ (v + 1) ∣ Nat.card W := by
  obtain ⟨q₁, -, hq, hA, hB⟩ := torus_arith hp hpodd hf hcard hm2 hd hW τ hτ
  rw [hτr] at hq
  have hrodd : Odd r := hr.eq_two_or_odd'.resolve_left hr2
  have hm0 : (m : ℤ) ≠ 0 := by
    rw [hm2]
    positivity
  have hA' : (Nat.card W : ℤ) * m = (q₁ : ℤ) ^ r - (if p ^ f % 4 = 1 then (1 : ℤ) else -1) := by
    rw [hA, hq]
    push_cast
    rfl
  have hε : (if p ^ f % 4 = 1 then (1 : ℤ) else -1) = 1 ∨
      (if p ^ f % 4 = 1 then (1 : ℤ) else -1) = -1 := by
    split_ifs <;> simp
  have hrB : (r : ℤ) ∣ Nat.card (fixedW W τ) :=
    Int.natCast_dvd_natCast.mpr ((dvd_pow_self r (by omega)).trans hv)
  have h := pow_succ_dvd_of_dvd hε hrodd hm0 hA' hB hrB (v := v)
    (by exact_mod_cast Int.natCast_dvd_natCast.mpr hv)
  exact_mod_cast Int.natCast_dvd_natCast.mp (by exact_mod_cast h)

theorem exists_fixedPointFree (τ : F ≃+* F) (hτ : τ ∈ Sigma) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hτr : orderOf τ = r) :
    ∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ s ≠ r ∧ ∃ w₀ ∈ W, orderOf w₀ = s ∧
      (∀ k ∈ Subgroup.zpowers w₀, fieldSL F τ k ∈ Subgroup.zpowers w₀) ∧
      ∀ k ∈ Subgroup.zpowers w₀, fieldSL F τ k = k → k = 1 := by
  obtain ⟨q₁, hq₁, hq, hA, hB⟩ := torus_arith hp hpodd hf hcard hm2 hd hW τ hτ
  rw [hτr] at hq
  have hrodd : Odd r := hr.eq_two_or_odd'.resolve_left hr2
  have hm0 : (m : ℤ) ≠ 0 := by
    rw [hm2]
    positivity
  have hA' : (Nat.card W : ℤ) * m = (q₁ : ℤ) ^ r - (if p ^ f % 4 = 1 then (1 : ℤ) else -1) := by
    rw [hA, hq]
    push_cast
    rfl
  have hε : (if p ^ f % 4 = 1 then (1 : ℤ) else -1) = 1 ∨
      (if p ^ f % 4 = 1 then (1 : ℤ) else -1) = -1 := by
    split_ifs <;> simp
  obtain ⟨s, hs, hsr, hsA, hsB⟩ :=
    exists_prime_dvd_not_dvd (by exact_mod_cast hq₁) hε hr hr2 hm0 hA' hB
  have hsA' : s ∣ Nat.card W := Int.natCast_dvd_natCast.mp hsA
  have hsB' : ¬ s ∣ Nat.card (fixedW W τ) := fun h => hsB (Int.natCast_dvd_natCast.mpr h)
  have : Fact s.Prime := ⟨hs⟩
  have : Fintype W := Fintype.ofFinite W
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := W) s
    (by rwa [← Nat.card_eq_fintype_card])
  set w₀ : SpecialLinearGroup (Fin 2) F := (x : SpecialLinearGroup (Fin 2) F) with hw₀
  have hw₀W : w₀ ∈ W := x.2
  have hord : orderOf w₀ = s := by rw [hw₀, Subgroup.orderOf_coe, hx]
  have hs2 : s ≠ 2 := by
    intro h2
    have := ((hW w₀).mp hw₀W).2
    rw [hord, h2] at this
    exact absurd this (by decide)
  have hcyc := isCyclic_W hp hpodd hf hcard hm2 hd hW
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := W)
  have hnorm : ∀ k ∈ Subgroup.zpowers w₀, fieldSL F τ k ∈ Subgroup.zpowers w₀ := by
    have hτg : fieldSL F τ (g₀ : SpecialLinearGroup (Fin 2) F) ∈ W := fieldSL_mem hW τ g₀.2
    obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ ⟨_, hτg⟩)
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ x)
    have hb' : fieldSL F τ (g₀ : SpecialLinearGroup (Fin 2) F) =
        (g₀ : SpecialLinearGroup (Fin 2) F) ^ b := by
      rw [← Subgroup.coe_zpow, hb]
    have ha' : w₀ = (g₀ : SpecialLinearGroup (Fin 2) F) ^ a := by
      rw [hw₀, ← ha, Subgroup.coe_zpow]
    have hτw : fieldSL F τ w₀ = w₀ ^ b := by
      rw [ha', map_zpow, hb', ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
    rintro k ⟨j, rfl⟩
    rw [map_zpow, hτw, ← _root_.zpow_mul]
    exact ⟨_, rfl⟩
  refine ⟨s, hs, hs2, hsr, w₀, hw₀W, hord, hnorm, ?_⟩
  intro k hk hτk
  by_contra hk1
  have hzk : Subgroup.zpowers k = Subgroup.zpowers w₀ := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hk)
    rw [Nat.card_zpowers, Nat.card_zpowers, hord]
    have h1 : orderOf k ∣ s := hord ▸ orderOf_dvd_of_mem_zpowers hk
    rcases (Nat.dvd_prime hs).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hk1
    · omega
  have hle : Subgroup.zpowers w₀ ≤ fixedW W τ := by
    rw [← hzk, Subgroup.zpowers_le]
    exact ⟨Subgroup.zpowers_le.mpr hw₀W hk, hτk⟩
  apply hsB'
  have h := Subgroup.card_dvd_of_le hle
  rwa [Nat.card_zpowers, hord] at h

end Arith

end CFSG.Wreathed.OriginalAllPrime.IVFacts
