module

public import CFSG.LieType.Universal.Spin.Datum

public section

namespace CFSG.LieType.Universal.Spin

open CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.CurtisTits

namespace OddCT

variable {n : ℕ} {K : Type} [Field K]

theorem mem_rootsB_iff {γ : Fin n → ℤ} :
    γ ∈ roots (isFiniteType_cartanB n) ∅ ↔
      (∃ (i j : Fin n) (_ : i ≠ j) (s t : Bool),
        toStdB n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) ∨
      ∃ (i : Fin n) (s : Bool), toStdB n γ = Pi.single i (boolSign s) := by
  rw [rootsB_eq, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨i, j, s, t, hij, hs, ht, h⟩ | ⟨i, s, hs, h⟩)
    · obtain ⟨s', rfl⟩ := exists_boolSign_eq hs
      obtain ⟨t', rfl⟩ := exists_boolSign_eq ht
      exact Or.inl ⟨i, j, hij, s', t', h⟩
    · obtain ⟨s', rfl⟩ := exists_boolSign_eq hs
      exact Or.inr ⟨i, s', h⟩
  · rintro (⟨i, j, hij, s, t, h⟩ | ⟨i, s, h⟩)
    · exact Or.inl ⟨i, j, boolSign s, boolSign t, hij, boolSign_eq_one_or_eq_neg_one s,
        boolSign_eq_one_or_eq_neg_one t, h⟩
    · exact Or.inr ⟨i, boolSign s, boolSign_eq_one_or_eq_neg_one s, h⟩

theorem ofStdB_add_mem {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    ofStdB n (Pi.single i (boolSign s) + Pi.single j (boolSign t)) ∈
      roots (isFiniteType_cartanB n) ∅ :=
  ofStdB_mem_rootsB n (Or.inl ⟨i, j, boolSign s, boolSign t, hij,
    boolSign_eq_one_or_eq_neg_one s, boolSign_eq_one_or_eq_neg_one t, rfl⟩)

theorem ofStdB_single_mem (i : Fin n) (s : Bool) :
    ofStdB n (Pi.single i (boolSign s)) ∈ roots (isFiniteType_cartanB n) ∅ :=
  ofStdB_mem_rootsB n (Or.inr ⟨i, boolSign s, boolSign_eq_one_or_eq_neg_one s, rfl⟩)

theorem exists_oddRootGroup_eq {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanB n) ∅) :
    (∃ (i j : Fin n) (hij : i ≠ j) (s t : Bool),
      toStdB n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t) ∧
        oddRootGroup n K γ = ((oddFrame n K).longRoot hij s t).range) ∨
    ∃ (i : Fin n) (s : Bool), toStdB n γ = Pi.single i (boolSign s) ∧
      oddRootGroup n K γ = ((oddFrame n K).shortRoot i s).range := by
  rcases mem_rootsB_iff.mp hγ with ⟨i, j, hij, s, t, h⟩ | ⟨i, s, h⟩
  · exact Or.inl ⟨i, j, hij, s, t, h, oddRootGroup_eq_long hij s t h⟩
  · exact Or.inr ⟨i, s, h, oddRootGroup_eq_short i s h⟩

theorem boolSign_mul_self (s : Bool) : boolSign s * boolSign s = 1 := by
  cases s <;> rfl

theorem dotProduct_toStdB_of_mem {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanB n) ∅) :
    toStdB n γ ⬝ᵥ toStdB n γ = 1 ∨ toStdB n γ ⬝ᵥ toStdB n γ = 2 := by
  rcases mem_rootsB_iff.mp hγ with ⟨i, j, hij, s, t, h⟩ | ⟨i, s, h⟩
  · right
    rw [h]
    simp only [add_dotProduct, dotProduct_add, single_dotProduct, Pi.single_eq_same,
      Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm, add_zero, zero_add, mul_zero,
      boolSign_mul_self]
    norm_num
  · left
    rw [h, single_dotProduct, Pi.single_eq_same, boolSign_mul_self]

theorem eq_one_or_eq_neg_one_of_smul_mem {γ : Fin n → ℤ} {c : ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB n) ∅) (hcγ : c • γ ∈ roots (isFiniteType_cartanB n) ∅) :
    c = 1 ∨ c = -1 := by
  have h₁ := dotProduct_toStdB_of_mem hγ
  have h₂ := dotProduct_toStdB_of_mem hcγ
  rw [toStdB_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h₂
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at h₂
  have hle : c ≤ 1 := by
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> rw [h₁] at h₂ <;> nlinarith
  have hge : -1 ≤ c := by
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> rw [h₁] at h₂ <;> nlinarith
  omega

theorem eq_smul_single_of_support {γ : Fin n → ℤ} {i : Fin n} (h : ∀ k, k ≠ i → γ k = 0) :
    γ = γ i • Pi.single i 1 := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp
  · simp [h k hk, hk]

theorem single_mem_rootsB (i : Fin n) :
    (Pi.single i 1 : Fin n → ℤ) ∈ roots (isFiniteType_cartanB n) ∅ :=
  Or.inl ⟨1, i, by rw [map_one, Module.End.one_apply]⟩

end OddCT

open OddCT

variable (n : ℕ) (K : Type) [Field K]

theorem oddDatum_ne_bot : ∀ γ ∈ (oddDatum n K).roots, (oddDatum n K).rootGroup γ ≠ ⊥ := by
  show ∀ γ ∈ roots (isFiniteType_cartanB n) ∅, oddRootGroup n K γ ≠ ⊥
  intro γ hγ hbot
  rcases exists_oddRootGroup_eq (K := K) hγ with ⟨i, j, hij, s, t, -, h⟩ | ⟨i, s, -, h⟩
  · have hmem : (oddFrame n K).longRoot hij s t (.ofAdd 1) ∈ oddRootGroup n K γ := by
      rw [h]
      exact ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot, ← map_one ((oddFrame n K).longRoot hij s t)] at hmem
    exact one_ne_zero (Multiplicative.ofAdd.injective
      ((oddFrame n K).longRoot_injective hij s t hmem))
  · have hmem : (oddFrame n K).shortRoot i s (.ofAdd 1) ∈ oddRootGroup n K γ := by
      rw [h]
      exact ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot, ← map_one ((oddFrame n K).shortRoot i s)] at hmem
    exact one_ne_zero (Multiplicative.ofAdd.injective
      ((oddFrame n K).shortRoot_injective i s hmem))

theorem oddDatum_two_smul_le : ∀ γ ∈ (oddDatum n K).roots, 2 • γ ∈ (oddDatum n K).roots →
    (oddDatum n K).rootGroup (2 • γ) ≤ (oddDatum n K).rootGroup γ := by
  show ∀ γ ∈ roots (isFiniteType_cartanB n) ∅, 2 • γ ∈ roots (isFiniteType_cartanB n) ∅ →
    oddRootGroup n K (2 • γ) ≤ oddRootGroup n K γ
  intro γ hγ h2
  have h2' : (2 : ℤ) • γ ∈ roots (isFiniteType_cartanB n) ∅ := by
    rw [two_zsmul, ← two_nsmul]
    exact h2
  rcases eq_one_or_eq_neg_one_of_smul_mem hγ h2' with h | h <;> norm_num at h

theorem oddDatum_le_rankOne : ∀ i : Fin n, ∀ γ ∈ roots (isFiniteType_cartanB n) ∅,
    (∀ k, k ≠ i → γ k = 0) → oddRootGroup n K γ ≤ rankOne (oddRootGroup n K) i := by
  intro i γ hγ hsupp
  have hγi := eq_smul_single_of_support hsupp
  rw [hγi] at hγ
  rcases eq_one_or_eq_neg_one_of_smul_mem (single_mem_rootsB i) hγ with h | h
  · rw [hγi, h, one_smul]
    exact le_sup_left
  · rw [hγi, h, neg_one_zsmul]
    exact le_sup_right

end CFSG.LieType.Universal.Spin
