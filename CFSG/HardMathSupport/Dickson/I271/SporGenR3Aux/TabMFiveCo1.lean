module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveTwoB
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveFixData
public import CFSG.Sporadic.Schreier.Co1Base

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMFive

open CFSG.Sporadic.Co1Schreier CFSG.HardMathSupport.Dickson.I271.TabCo1
  CFSG.Monster.Existence.Co1Bridge

open scoped Matrix

section Conj

theorem fixCount_conj (c s : GL (Fin 24) (ZMod 2)) :
    fixCount (((c * s * c⁻¹ : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2))) =
      fixCount ((s : Matrix (Fin 24) (Fin 24) (ZMod 2))) := by
  have hCD : ∀ v : Fin 24 → ZMod 2, (c : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
      (((c⁻¹ : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hDC : ∀ v : Fin 24 → ZMod 2,
      ((c⁻¹ : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
        ((c : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  unfold fixCount
  refine Nat.card_congr (Equiv.subtypeEquiv
    { toFun := fun w => ((c⁻¹ : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w
      invFun := fun w => (c : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w
      left_inv := fun w => hCD w
      right_inv := fun w => hDC w } ?_)
  intro w
  show ((c * s * c⁻¹ : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w = w ↔
    (s : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
      (((c⁻¹ : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w) =
      ((c⁻¹ : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  constructor
  · intro h
    calc (s : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
          (((c⁻¹ : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w) =
        ((c⁻¹ : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
          ((c : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
            ((s : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
              (((c⁻¹ : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w))) :=
          (hDC _).symm
      _ = ((c⁻¹ : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w := by rw [h]
  · intro h
    rw [h]
    exact hCD w

end Conj

section Inputs


structure Co1FiveInputs : Prop where
  census : ∀ s : J24, orderOf s = 5 → ∃ c : J24,
    MRep repD0 ((c * s * c⁻¹ : J24) : GL24) ∨ MRep repD1 ((c * s * c⁻¹ : J24) : GL24) ∨
      MRep repZ ((c * s * c⁻¹ : J24) : GL24)
  cardA : ∀ x : J24, MRep repD0 (x : GL24) →
    Nat.card (Subgroup.centralizer ({x} : Set J24)) ≤ 3024000
  cardB : ∀ x : J24, MRep repD1 (x : GL24) →
    Nat.card (Subgroup.centralizer ({x} : Set J24)) ≤ 36000
  cardC : ∀ x : J24, MRep repZ (x : GL24) →
    Nat.card (Subgroup.centralizer ({x} : Set J24)) ≤ 15000

theorem co1FiveBound_of_inputs (h : Co1FiveInputs) : Co1FiveBound := by
  intro j hj
  obtain ⟨c, hc⟩ := h.census j hj
  have hcard := TabMSeven.card_centralizer_conj c j
  have hfix : fixCount (((c * j * c⁻¹ : J24) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) =
      fixCount ((j : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) :=
    fixCount_conj (c : GL24) (j : GL24)
  rw [← hcard, ← hfix]
  rcases hc with hA | hB | hC
  · have h1 := h.cardA _ hA
    have h2 := fixCount_fiveA_le hA
    calc 2 * fixCount (((c * j * c⁻¹ : J24) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
          Nat.card (Subgroup.centralizer ({c * j * c⁻¹} : Set J24)) ≤ 2 * 1 * 3024000 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 h2) h1
      _ ≤ 18432000 := by norm_num
  · have h1 := h.cardB _ hB
    have h2 := fixCount_fiveB_le hB
    calc 2 * fixCount (((c * j * c⁻¹ : J24) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
          Nat.card (Subgroup.centralizer ({c * j * c⁻¹} : Set J24)) ≤ 2 * 2 ^ 8 * 36000 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 h2) h1
      _ ≤ 18432000 := by norm_num
  · have h1 := h.cardC _ hC
    have h2 := fixCount_fiveC_le hC
    calc 2 * fixCount (((c * j * c⁻¹ : J24) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
          Nat.card (Subgroup.centralizer ({c * j * c⁻¹} : Set J24)) ≤ 2 * 2 ^ 4 * 15000 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 h2) h1
      _ ≤ 18432000 := by norm_num

theorem Co1FiveInputs.of_eq {G' : Subgroup GL24} (hG : J24 = G')
    (census : ∀ s : G', orderOf s = 5 → ∃ c : G',
      MRep repD0 ((c * s * c⁻¹ : G') : GL24) ∨ MRep repD1 ((c * s * c⁻¹ : G') : GL24) ∨
        MRep repZ ((c * s * c⁻¹ : G') : GL24))
    (cardA : ∀ x : G', MRep repD0 (x : GL24) →
      Nat.card (Subgroup.centralizer ({x} : Set G')) ≤ 3024000)
    (cardB : ∀ x : G', MRep repD1 (x : GL24) →
      Nat.card (Subgroup.centralizer ({x} : Set G')) ≤ 36000)
    (cardC : ∀ x : G', MRep repZ (x : GL24) →
      Nat.card (Subgroup.centralizer ({x} : Set G')) ≤ 15000) : Co1FiveInputs := by
  subst hG
  exact ⟨census, cardA, cardB, cardC⟩

end Inputs

end CFSG.HardMathSupport.Dickson.I271.TabMFive
