module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.CountingPairs
public import CFSG.LocalAnalysis.GLTheoremB.UniqDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal CFSG.Open
  CFSG.LocalAnalysis.GLTheoremB Matrix

section Free

variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def isoSubgroup (Q : (ι → ZMod 2) → ZMod 2) : Subgroup (GL ι (ZMod 2)) where
  carrier := {A | ∀ v, Q ((A : Matrix ι ι (ZMod 2)) *ᵥ v) = Q v}
  one_mem' := fun v => by simp
  mul_mem' := fun {A B} hA hB v => by
    simp only [Set.mem_ofPred_eq] at hA hB ⊢
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hA, hB]
  inv_mem' := fun {A} hA v => by
    simp only [Set.mem_ofPred_eq] at hA ⊢
    have h := hA ((A⁻¹ : GL ι (ZMod 2)) *ᵥ v)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h
    exact h.symm

lemma statedOmega_le_isoSubgroup (Q : (ι → ZMod 2) → ZMod 2) :
    StatedOmega Q ≤ isoSubgroup Q := by
  have hS : Subgroup.closure {A : GL ι (ZMod 2) |
      ∀ v, Q ((A : Matrix ι ι (ZMod 2)) *ᵥ v) = Q v} ≤ isoSubgroup Q :=
    Subgroup.closure_le _ |>.2 fun A hA => hA
  refine Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem (hS h₁) (hS h₂)) (inv_mem (hS h₁))) (inv_mem (hS h₂))

@[expose, instance_reducible] def isoAction (Q : (ι → ZMod 2) → ZMod 2) (H : Subgroup (GL ι (ZMod 2)))
    (hH : H ≤ isoSubgroup Q) (b : ZMod 2) : MulAction H {v : ι → ZMod 2 // Q v = b} where
  smul g v := ⟨(g : GL ι (ZMod 2)).val *ᵥ v.1, by rw [hH g.2 v.1]; exact v.2⟩
  one_smul v := Subtype.ext (by
    show ((1 : H) : GL ι (ZMod 2)).val *ᵥ v.1 = v.1
    simp)
  mul_smul g h v := Subtype.ext (by
    show ((g * h : H) : GL ι (ZMod 2)).val *ᵥ v.1 =
      (g : GL ι (ZMod 2)).val *ᵥ ((h : GL ι (ZMod 2)).val *ᵥ v.1)
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec])

lemma card_one_add_card_zero {α : Type*} [Fintype α] (f : α → ZMod 2) :
    Fintype.card {a // f a = 1} + Fintype.card {a // f a = 0} = Fintype.card α := by
  classical
  have h : Fintype.card {a // ¬ f a = 0} = Fintype.card α - Fintype.card {a // f a = 0} :=
    Fintype.card_subtype_compl _
  have h1 : Fintype.card {a // f a = 1} = Fintype.card {a // ¬ f a = 0} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun a => by
      constructor
      · intro h h0; rw [h0] at h; exact absurd h (by decide)
      · intro h; exact zmod2_eq_one_of_ne_zero h)
  have : Fintype.card {a // f a = 0} ≤ Fintype.card α := Fintype.card_subtype_le _
  omega

lemma dvd_card_one_of_free (Q : (ι → ZMod 2) → ZMod 2) (hQ0 : Q 0 = 0) {p : ℕ} [Fact p.Prime]
    {A : GL ι (ZMod 2)} (hA : A ∈ isoSubgroup Q) (hord : orderOf A = p)
    (hfree : ∀ v, (A : Matrix ι ι (ZMod 2)) *ᵥ v = v → v = 0) :
    p ∣ Fintype.card {v : ι → ZMod 2 // Q v = 1} := by
  let H := Subgroup.zpowers A
  have hH : H ≤ isoSubgroup Q := (Subgroup.zpowers_le).2 hA
  let _ := isoAction Q H hH 1
  have hpg : IsPGroup p H := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hord, pow_one])
  have hmod := hpg.card_modEq_card_fixedPoints {v : ι → ZMod 2 // Q v = 1}
  have hfix : MulAction.fixedPoints H {v : ι → ZMod 2 // Q v = 1} = ∅ := by
    ext v
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hv
    have h := MulAction.mem_fixedPoints.mp hv ⟨A, Subgroup.mem_zpowers A⟩
    have h2 := congrArg Subtype.val h
    have h3 : v.1 = 0 := hfree v.1 h2
    have := v.2
    rw [h3, hQ0] at this
    exact absurd this (by decide)
  rw [hfix] at hmod
  have h0 : Nat.card (↥(∅ : Set {v : ι → ZMod 2 // Q v = 1})) = 0 := by simp
  rw [h0, Nat.modEq_zero_iff_dvd, Nat.card_eq_fintype_card] at hmod
  exact hmod

lemma dvd_typeSign_aux {ε : Bool} {k p N Z : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hN : p ∣ N)
    (hsum : N + Z = 2 ^ (2 * (k + 1)))
    (hZ : (Z : ℤ) = 2 ^ (2 * (k + 1) - 1) + (if ε then 1 else -1) * 2 ^ (k + 1 - 1)) :
    p ∣ typeSign ε (k + 1) := by
  have h2 : (2 * (k + 1) - 1) = 2 * k + 1 := by omega
  rw [h2] at hZ
  simp only [Nat.add_sub_cancel] at hZ
  have hsum' : (N : ℤ) + Z = 2 ^ (2 * (k + 1)) := by exact_mod_cast hsum
  have hT : ((typeSign ε (k + 1) : ℕ) : ℤ) = 2 * 2 ^ k - (if ε then 1 else -1) := by
    cases ε
    · simp [typeSign]; ring
    · simp only [typeSign, ↓reduceIte]
      rw [Nat.cast_sub Nat.one_le_two_pow]
      push_cast; ring
  have hN' : (N : ℤ) = 2 ^ k * ((typeSign ε (k + 1) : ℕ) : ℤ) := by
    rw [hT]
    have e1 : (2 : ℤ) ^ (2 * (k + 1)) = 4 * (2 ^ k) ^ 2 := by ring
    have e2 : (2 : ℤ) ^ (2 * k + 1) = 2 * (2 ^ k) ^ 2 := by ring
    rw [e2] at hZ
    rw [e1] at hsum'
    have : (if ε then (1 : ℤ) else -1) * 2 ^ k * (if ε then (1 : ℤ) else -1) = 2 ^ k := by
      cases ε <;> simp
    nlinarith [hZ, hsum', this]
  have hdvd : p ∣ 2 ^ k * typeSign ε (k + 1) := by
    have : (p : ℤ) ∣ ((2 ^ k * typeSign ε (k + 1) : ℕ) : ℤ) := by
      push_cast
      rw [← hN']
      exact_mod_cast hN
    exact_mod_cast this
  exact (hp.dvd_mul.1 hdvd).resolve_left fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))

lemma statedQuadMinus_eq (n : ℕ) :
    CFSG.Open.StatedQuadMinus n (ZMod 2) 1 1 = ⇑(quadMinus n (ZMod 2) 1 1) :=
  funext fun v => by rw [quadMinus_apply]; rfl

lemma statedQuadPlus_eq (n : ℕ) :
    CFSG.Open.StatedQuadPlus n (ZMod 2) = ⇑(quadPlus n (ZMod 2)) :=
  funext fun v => by rw [quadPlus_apply]; rfl

theorem dvd_typeSign_of_hasFixedPointFreeOrder {ε : Bool} {n p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : 1 ≤ n) (h : HasFixedPointFreeOrder ε n p) : p ∣ typeSign ε n := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  cases ε
  · obtain ⟨A, hA, hord, hfree⟩ := h
    have hQ0 : CFSG.Open.StatedQuadMinus (k + 1) (ZMod 2) 1 1 0 = 0 := by
      simp [CFSG.Open.StatedQuadMinus]
    have hdiv := dvd_card_one_of_free _ hQ0 (statedOmega_le_isoSubgroup _ hA) hord hfree
    have hsum := card_one_add_card_zero (CFSG.Open.StatedQuadMinus (k + 1) (ZMod 2) 1 1)
    have hz := card_zeros_of_isStdSpace (V := Fin (k + 1 - 1) ⊕ Fin (k + 1 - 1) ⊕ Fin 2 → ZMod 2)
      (Q := quadMinus (k + 1) (ZMod 2) 1 1) (ε := false) (m := k + 1) (Nat.succ_pos k)
      ⟨LinearEquiv.refl _ _, fun v => rfl⟩
    rw [statedQuadMinus_eq] at hdiv hsum
    rw [Nat.card_eq_fintype_card] at hz
    refine dvd_typeSign_aux (k := k) hp hp2 hdiv ?_ hz
    rw [hsum]
    simp [Fintype.card_sum]
    omega
  · obtain ⟨A, hA, hord, hfree⟩ := h
    have hQ0 : CFSG.Open.StatedQuadPlus (k + 1) (ZMod 2) 0 = 0 := by
      simp [CFSG.Open.StatedQuadPlus]
    have hdiv := dvd_card_one_of_free _ hQ0 (statedOmega_le_isoSubgroup _ hA) hord hfree
    have hsum := card_one_add_card_zero (CFSG.Open.StatedQuadPlus (k + 1) (ZMod 2))
    have hz := card_zeros_of_isStdSpace (V := Fin (k + 1) ⊕ Fin (k + 1) → ZMod 2)
      (Q := quadPlus (k + 1) (ZMod 2)) (ε := true) (m := k + 1) (Nat.succ_pos k)
      ⟨LinearEquiv.refl _ _, fun v => rfl⟩
    rw [statedQuadPlus_eq] at hdiv hsum
    rw [Nat.card_eq_fintype_card] at hz
    refine dvd_typeSign_aux (k := k) hp hp2 hdiv ?_ hz
    rw [hsum]
    simp [Fintype.card_sum]
    omega

end Free

section Main

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem exists_fixed_hypPair_of_hasFpf (hQ : (polarBilin Q).Nondegenerate) {ε : Bool}
    {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n) (hfpf : HasFixedPointFreeOrder ε n p)
    (hstd : IsStdSpace ε Q (n + 1)) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hE : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hexp : ∀ x ∈ E, x ^ p = 1) :
    ∃ P : HypPair Q, ∀ g ∈ E, g P.e = P.e ∧ g P.f = P.f :=
  exists_fixed_hypPair_of_isStdSpace hQ hp hp2
    (dvd_typeSign_of_hasFixedPointFreeOrder hp hp2 hn hfpf) hstd hE hexp

end Main

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
