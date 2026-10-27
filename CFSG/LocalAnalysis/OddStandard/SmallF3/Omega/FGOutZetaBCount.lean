module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaBDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

private def zetaBCountDiff (i i' : Fin 3) : Fin 3 :=
  ⟨(i.val + 3 - i'.val) % 3, Nat.mod_lt _ (by decide)⟩

private theorem zetaBCountDiff_eq_zero_iff (i i' : Fin 3) : zetaBCountDiff i i' = 0 ↔ i = i' := by
  revert i i'
  decide

private theorem zetaBCountDiff_modEq (i i' : Fin 3) :
    (i:ℕ) ≡ (zetaBCountDiff i i' + (i':ℕ)) [MOD 3] := by
  revert i i'
  decide

private theorem zetaBCount_pow_mul_inv {G : Type*} [CommGroup G] (x : G) (hx : x ^ 3 = 1)
    (i i' : Fin 3) :
    x ^ (i:ℕ) * (x ^ (i':ℕ))⁻¹ = x ^ (zetaBCountDiff i i' : ℕ) := by
  have hd : x ^ (i:ℕ) = x ^ (zetaBCountDiff i i' : ℕ) * x ^ (i':ℕ) := by
    rw [← pow_add, pow_eq_pow_iff_modEq]
    exact Nat.ModEq.of_dvd (orderOf_dvd_iff_pow_eq_one.mpr hx) (zetaBCountDiff_modEq i i')
  rw [hd, mul_assoc, mul_inv_cancel, mul_one]

private theorem zetaBCount_injective {G : Type*} [CommGroup G] (a b : G)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hind : ∀ i j : Fin 3, a ^ (i:ℕ) * b ^ (j:ℕ) = 1 → i = 0 ∧ j = 0) :
    Function.Injective (fun p : Fin 3 × Fin 3 => a ^ (p.1:ℕ) * b ^ (p.2:ℕ)) := by
  intro p q h
  obtain ⟨i, j⟩ := p
  obtain ⟨i', j'⟩ := q
  simp only [Prod.mk.injEq] at h ⊢
  have hd1 : a ^ (i:ℕ) * (a ^ (i':ℕ))⁻¹ = a ^ (zetaBCountDiff i i' : ℕ) :=
    zetaBCount_pow_mul_inv a ha i i'
  have hd2 : b ^ (j:ℕ) * (b ^ (j':ℕ))⁻¹ = b ^ (zetaBCountDiff j j' : ℕ) :=
    zetaBCount_pow_mul_inv b hb j j'
  have hkey : a ^ (i:ℕ) * (a ^ (i':ℕ))⁻¹ = b ^ (j':ℕ) * (b ^ (j:ℕ))⁻¹ := by
    have hdiv : a ^ (i:ℕ) / a ^ (i':ℕ) = b ^ (j':ℕ) / b ^ (j:ℕ) := by
      rw [div_eq_div_iff_mul_eq_mul]
      rw [mul_comm (b ^ (j':ℕ))]
      exact h
    simpa only [div_eq_mul_inv] using hdiv
  have hinv : b ^ (j':ℕ) * (b ^ (j:ℕ))⁻¹ = (b ^ (j:ℕ) * (b ^ (j':ℕ))⁻¹)⁻¹ := by
    rw [mul_inv_rev, inv_inv]
  have hrel : a ^ (zetaBCountDiff i i' : ℕ) * b ^ (zetaBCountDiff j j' : ℕ) = 1 := by
    rw [← hd1, ← hd2, hkey, hinv]
    exact inv_mul_cancel _
  obtain ⟨h1, h2⟩ := hind (zetaBCountDiff i i') (zetaBCountDiff j j') hrel
  exact ⟨(zetaBCountDiff_eq_zero_iff i i').mp h1, (zetaBCountDiff_eq_zero_iff j j').mp h2⟩

private theorem zetaBCount_pow3_mul {G : Type*} [Group G] (hcomm : ∀ x y : G, x * y = y * x)
    (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (i j : Fin 3) : (a ^ (i:ℕ) * b ^ (j:ℕ)) ^ 3 = 1 := by
  have h : Commute (a ^ (i:ℕ)) (b ^ (j:ℕ)) :=
    Commute.pow_pow (show Commute a b from hcomm a b) i j
  have hai : (a ^ (i:ℕ)) ^ 3 = 1 := by
    rw [← pow_mul, Nat.mul_comm (i:ℕ) 3, pow_mul, ha, one_pow]
  have hbj : (b ^ (j:ℕ)) ^ 3 = 1 := by
    rw [← pow_mul, Nat.mul_comm (j:ℕ) 3, pow_mul, hb, one_pow]
  rw [h.mul_pow 3, hai, hbj, mul_one]

theorem zetaCount_holds : ZetaCount := by
  intro M H _ _ e ρ c₀ c₁ h0 h1 hind m
  classical
  have hcomm : ∀ x y : M, x * y = y * x := fun x y => by
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  haveI : Fintype M :=
    Fintype.ofEquiv (Multiplicative (ZMod 4 × ZMod 3 × ZMod 3)) e.symm.toEquiv
  have hN12 : ∀ y : Multiplicative (ZMod 4 × ZMod 3 × ZMod 3), y ^ 12 = 1 := by decide
  have h12 : ∀ x : M, x ^ 12 = 1 := by
    intro x
    apply e.injective
    rw [map_pow, map_one]
    exact hN12 (e x)
  have ha : (c₀ ^ 4) ^ 3 = 1 := by
    rw [← pow_mul]
    exact h12 c₀
  have hb : (c₁ ^ 4) ^ 3 = 1 := by
    rw [← pow_mul]
    exact h12 c₁
  have hind' : ∀ i j : Fin 3, (c₀ ^ 4) ^ (i:ℕ) * (c₁ ^ 4) ^ (j:ℕ) = 1 → i = 0 ∧ j = 0 := by
    intro i j hij
    apply hind i j
    have hρc0 : ρ c₀ ^ 4 = ρ c₀ := by
      rw [show (4:ℕ) = 3 + 1 from rfl, pow_succ, h0, one_mul]
    have hρc1 : ρ c₁ ^ 4 = ρ c₁ := by
      rw [show (4:ℕ) = 3 + 1 from rfl, pow_succ, h1, one_mul]
    have hc := congrArg ρ hij
    simp only [map_mul, map_pow, map_one] at hc
    rwa [hρc0, hρc1] at hc
  have hindN : ∀ i j : Fin 3,
      (e (c₀ ^ 4)) ^ (i:ℕ) * (e (c₁ ^ 4)) ^ (j:ℕ) = 1 → i = 0 ∧ j = 0 := by
    intro i j hij
    apply hind' i j
    apply e.injective
    simpa only [map_mul, map_pow, map_one] using hij
  have hinjN : Function.Injective
      (fun p : Fin 3 × Fin 3 => (e (c₀ ^ 4)) ^ (p.1:ℕ) * (e (c₁ ^ 4)) ^ (p.2:ℕ)) :=
    zetaBCount_injective (e (c₀ ^ 4)) (e (c₁ ^ 4))
      (by rw [← map_pow, ha, map_one]) (by rw [← map_pow, hb, map_one]) hindN
  have hinjM : Function.Injective
      (fun p : Fin 3 × Fin 3 => (c₀ ^ 4) ^ (p.1:ℕ) * (c₁ ^ 4) ^ (p.2:ℕ)) := by
    intro p q hpq
    apply hinjN
    have hc := congrArg e hpq
    simpa only [map_mul, map_pow] using hc
  let t : Fin 3 × Fin 3 → {x : M // x ^ 3 = 1} := fun p =>
    ⟨(c₀ ^ 4) ^ (p.1:ℕ) * (c₁ ^ 4) ^ (p.2:ℕ),
      zetaBCount_pow3_mul hcomm (c₀ ^ 4) (c₁ ^ 4) ha hb p.1 p.2⟩
  have hinjT : Function.Injective t := by
    intro p q hpq
    apply hinjM
    exact congrArg Subtype.val hpq
  have hpred : ∀ x : M, x ^ 3 = 1 ↔ (e x) ^ 3 = 1 := by
    intro x
    constructor
    · intro hx; rw [← map_pow, hx, map_one]
    · intro hx; exact e.injective (by rw [map_pow, hx, map_one])
  have hcardT : Fintype.card {x : M // x ^ 3 = 1} = 9 := by
    have hNcard : Fintype.card {y : Multiplicative (ZMod 4 × ZMod 3 × ZMod 3) // y ^ 3 = 1} =
        9 := by decide
    rw [← hNcard]
    exact Fintype.card_congr (Equiv.subtypeEquiv e.toEquiv hpred)
  have hcarddom : Fintype.card (Fin 3 × Fin 3) = Fintype.card {x : M // x ^ 3 = 1} := by
    rw [hcardT]; decide
  have hsurj : Function.Surjective t :=
    ((Fintype.bijective_iff_injective_and_card t).mpr ⟨hinjT, hcarddom⟩).2
  have hmT : (m ^ 4) ^ 3 = 1 := by
    rw [← pow_mul]
    exact h12 m
  obtain ⟨p, hp⟩ := hsurj ⟨m ^ 4, hmT⟩
  refine ⟨p.1, p.2, ?_⟩
  have hpval : (c₀ ^ 4) ^ (p.1:ℕ) * (c₁ ^ 4) ^ (p.2:ℕ) = m ^ 4 := congrArg Subtype.val hp
  rw [← hpval, pow_mul, pow_mul]

end CFSG.OddStandard.SmallF3.Omega
