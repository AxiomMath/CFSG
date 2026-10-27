module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRSmallOddRigid
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRSmallEvenRigid
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRigidityStd
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRSmallTwo

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart)
open CFSG.Quasithin (perfectCore)

section Symm

variable {n : ℕ} {K : Type*} [Field K] [Finite K] {hn : 3 ≤ n}
  {X₁ X₂ : Subgroup (projectiveSL n K)}

theorem FieldRigidIn.symm (h : FieldRigidIn hn X₁ X₂) : FieldRigidIn hn X₂ X₁ := by
  intro Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hX γ β₁ β₂ hβX h₁ h₂
  have hβ₂X : ∀ x ∈ X₁, β₂ x ∈ X₁ := by
    intro x hx
    have hmem : φ₂ x ∈ X₂.map φ₁ := hX ▸ ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hzx⟩ := hmem
    have hmem' : φ₂ (β₂ x) ∈ X₁.map φ₂ := by
      rw [← hX, h₂, ← hzx, ← h₁]
      exact ⟨β₁ z, hβX z hz, rfl⟩
    obtain ⟨w, hw, hwx⟩ := hmem'
    rw [← hφ₂ hwx]
    exact hw
  exact (h Γ φ₂ φ₁ hφ₂ hφ₁ hX.symm γ β₂ β₁ hβ₂X h₂ h₁).symm

end Symm

section Cases

variable {n : ℕ} (K : Type) [Field K] [Finite K]

@[expose] def InnerMaxFieldRigid (hn : 3 ≤ n) : Prop :=
  ∀ (k k' : ℕ) (P : InvPlacement n k) (P' : InvPlacement n k'), P.elt K ≠ 1 → P'.elt K ≠ 1 →
    P.free.card ≤ 1 → P'.free.card ≤ 1 →
      FieldRigidIn hn (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))))
        (perfectCore (centralizer ({P'.elt K} : Set (projectiveSL n K))))

@[expose] def IsStdGraphForm (C : GL (Fin n) K) : Prop :=
  (C : Matrix (Fin n) (Fin n) K) = 1 ∨
    ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = UnitaryHigher.blockSwapJ n r

@[expose] def InnerGraphMixedFieldRigid (hn : 3 ≤ n) : Prop :=
  ∀ (k : ℕ) (P : InvPlacement n k) (C : GL (Fin n) K), P.elt K ≠ 1 → IsStdGraphForm K C →
    FieldRigidIn hn (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))))
      (perfectCore (autFixSubgroup (conjAut n K C * dualAut n K)))

@[expose] def GraphGraphFieldRigid (hn : 3 ≤ n) : Prop :=
  ∀ C C' : GL (Fin n) K, IsStdGraphForm K C → IsStdGraphForm K C' →
    FieldRigidIn hn (perfectCore (autFixSubgroup (conjAut n K C * dualAut n K)))
      (perfectCore (autFixSubgroup (conjAut n K C' * dualAut n K)))

variable {K}

theorem innerGraphFieldRigid_of_cases {f : ℕ} (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (hn : 4 ≤ n) (hAA : InnerMaxFieldRigid K (Nat.le_of_succ_le hn))
    (hAD : InnerGraphMixedFieldRigid K (Nat.le_of_succ_le hn))
    (hDD : GraphGraphFieldRigid K (Nat.le_of_succ_le hn)) :
    InnerGraphFieldRigid K (Nat.le_of_succ_le hn) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [hK, pow_zero] at hq
      omega
    · exact h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  refine innerGraphFieldRigid_of_std hK (Nat.le_of_succ_le hn) fun X₁ X₂ hX₁ hX₂ => ?_
  rcases hX₁ with ⟨k, P, hP, rfl⟩ | ⟨C, hC, rfl⟩ <;>
    rcases hX₂ with ⟨k', P', hP', rfl⟩ | ⟨C', hC', rfl⟩
  · by_cases hJ : 2 ≤ P.free.card ∨ 2 ≤ P'.free.card
    · exact fieldRigidIn_inner_of_two_le_or hq hn P P' hP hP' hJ
    · push Not at hJ
      exact hAA k k' P P' hP hP' (by omega) (by omega)
  · exact hAD k P C' hP hC'
  · exact (hAD k' P' C hP' hC).symm
  · exact hDD C C' hC hC'

theorem innerGraphFieldRigid_of_cases' {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    (hcases : 4 ≤ Nat.card K → InnerMaxFieldRigid K (Nat.le_of_succ_le hn) ∧
      InnerGraphMixedFieldRigid K (Nat.le_of_succ_le hn) ∧
        GraphGraphFieldRigid K (Nat.le_of_succ_le hn)) :
    InnerGraphFieldRigid K (Nat.le_of_succ_le hn) := by
  rcases Nat.lt_or_ge (Nat.card K) 4 with h | h
  · have h2 : Nat.card K = 2 := by
      have h1 := Finite.one_lt_card (α := K)
      rcases f with _ | _ | f
      · rw [hK, pow_zero] at h1
        omega
      · rw [hK, pow_one]
      · rw [hK, pow_succ, pow_succ] at h
        have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
        omega
    exact innerGraphFieldRigid_of_card_eq_two h2 _
  · obtain ⟨hAA, hAD, hDD⟩ := hcases h
    exact innerGraphFieldRigid_of_cases hK h hn hAA hAD hDD

theorem fieldRigidIn_inner_of_ne_one [CharP K 2] (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n) {k k' : ℕ}
    (P : InvPlacement n k) (P' : InvPlacement n k') (hP : P.elt K ≠ 1) (hP' : P'.elt K ≠ 1) :
    FieldRigidIn (Nat.le_of_succ_le hn)
      (perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))))
      (perfectCore (centralizer ({P'.elt K} : Set (projectiveSL n K)))) := by
  by_cases hJ : 2 ≤ P.free.card ∨ 2 ≤ P'.free.card
  · exact fieldRigidIn_inner_of_two_le_or hq hn P P' hP hP' hJ
  push Not at hJ
  have hc := P.card_free
  have hc' := P'.card_free
  have h2k : 2 * k ≤ n := by
    have := Fintype.card_le_of_injective P.supp P.supp_injective
    simpa [two_mul] using this
  have h2k' : 2 * k' ≤ n := by
    have := Fintype.card_le_of_injective P'.supp P'.supp_injective
    simpa [two_mul] using this
  rcases (by omega : (P.free.card = 1 ∧ P'.free.card = 1) ∨
      (P.free.card = 0 ∧ P'.free.card = 0)) with ⟨h1, h1'⟩ | ⟨h0, h0'⟩
  · exact fieldRigidIn_inner_of_card_free_eq_one hq hn P P' h1 h1'
  · exact fieldRigidIn_inner_of_free_eq_empty hq hn P P' (Finset.card_eq_zero.1 h0)
      (Finset.card_eq_zero.1 h0')

theorem innerMaxFieldRigid [CharP K 2] (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n) :
    InnerMaxFieldRigid K (Nat.le_of_succ_le hn) :=
  fun _ _ P P' hP hP' _ _ => fieldRigidIn_inner_of_ne_one hq hn P P' hP hP'

theorem innerGraphFieldRigid_of_graph_cases {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n) (hAD : InnerGraphMixedFieldRigid K (Nat.le_of_succ_le hn))
    (hDD : GraphGraphFieldRigid K (Nat.le_of_succ_le hn)) :
    InnerGraphFieldRigid K (Nat.le_of_succ_le hn) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [hK, pow_zero] at hq
      omega
    · exact h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  exact innerGraphFieldRigid_of_cases hK hq hn (innerMaxFieldRigid hq hn) hAD hDD

end Cases

end CFSG.SeitzReduction.LinearPilot
