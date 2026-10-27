module

public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.CGT.PushingUpLit.BHS6.ThreeEightAlt
public import CFSG.CGT.PushingUpLit.BHS.SymNatBasic
public import CFSG.CGT.PushingUpLit.BHS6.ThreeEightGaps

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.Quasithin.G6 hiding allOnes

section Conv

variable {n : ℕ}

theorem altMod_evenWeightOnes_eq_bot (hn : Odd n) : evenWeightOnes n = ⊥ := by
  rw [eq_bot_iff]
  rintro x hx
  rw [evenWeightOnes, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_zmultiples_iff] at hx
  obtain ⟨k, hk⟩ := hx
  have hsum := x.2
  simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply] at hsum
  rw [← hk] at hsum
  simp only [allOnes, Pi.smul_apply, zsmul_eq_mul, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hn1 : (n : ZMod 2) = 1 := by
    obtain ⟨m, rfl⟩ := hn
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
  rw [hn1, one_mul] at hsum
  rw [AddSubgroup.mem_bot]
  apply Subtype.ext
  rw [← hk]
  funext i
  simp [allOnes, zsmul_eq_mul, hsum]

@[expose] noncomputable def altMod_altHeartEquivEven (hn : Odd n) : altHeart n ≃+ evenWeight n :=
  (QuotientAddGroup.quotientAddEquivOfEq (altMod_evenWeightOnes_eq_bot hn)).trans
    QuotientAddGroup.quotientBot

@[expose] noncomputable def altMod_toCore (hn : Odd n) :
    Multiplicative (altHeart n) ≃* ↥(coreMod n) :=
  (AddEquiv.toMultiplicative (altMod_altHeartEquivEven hn)).trans (coreModEvenEquiv n).symm

theorem altMod_toCore_equivar (hn : Odd n) (σ : Perm (Fin n)) (x : evenWeight n) :
    altMod_toCore hn
        (Multiplicative.ofAdd (QuotientAddGroup.mk (evenWeightPerm σ x) : altHeart n)) =
      coreAct n σ
        (altMod_toCore hn (Multiplicative.ofAdd (QuotientAddGroup.mk x : altHeart n))) := by
  apply vcoord_ext
  intro i
  rfl

end Conv

section Pairs

variable {n : ℕ}

@[expose] def swapPairStab (a b : Fin n) : Subgroup (Perm (Fin n)) where
  carrier := {σ | (σ a = a ∧ σ b = b) ∨ (σ a = b ∧ σ b = a)}
  one_mem' := Or.inl ⟨rfl, rfl⟩
  mul_mem' := by
    rintro σ τ (⟨h1, h2⟩ | ⟨h1, h2⟩) (⟨h3, h4⟩ | ⟨h3, h4⟩)
    · exact Or.inl ⟨by simp [*], by simp [*]⟩
    · exact Or.inr ⟨by simp [*], by simp [*]⟩
    · exact Or.inr ⟨by simp [*], by simp [*]⟩
    · exact Or.inl ⟨by simp [*], by simp [*]⟩
  inv_mem' := by
    rintro σ (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨by rw [Perm.inv_eq_iff_eq]; exact h1.symm,
        by rw [Perm.inv_eq_iff_eq]; exact h2.symm⟩
    · exact Or.inr ⟨by rw [Perm.inv_eq_iff_eq]; exact h2.symm,
        by rw [Perm.inv_eq_iff_eq]; exact h1.symm⟩

theorem mem_swapPairStab_of_commute {a b : Fin n} (hab : a ≠ b) {σ : Perm (Fin n)}
    (h : σ * swap a b = swap a b * σ) : σ ∈ swapPairStab a b := by
  have h1 : σ b = swap a b (σ a) := by
    have := congrArg (fun f : Perm (Fin n) => f a) h
    simpa using this
  by_cases hσa : σ a = a
  · left
    exact ⟨hσa, by rw [h1, hσa, swap_apply_left]⟩
  · by_cases hσb : σ a = b
    · right
      exact ⟨hσb, by rw [h1, hσb, swap_apply_right]⟩
    · exfalso
      rw [swap_apply_of_ne_of_ne hσa hσb] at h1
      exact hab (σ.injective h1).symm

theorem swap_mul_swap_swap_eq {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    swap b a * swap a c = swap b c * swap a b := by
  ext x
  by_cases h1 : x = a
  · subst h1
    simp [swap_apply_of_ne_of_ne, hac.symm, hbc.symm]
  by_cases h2 : x = b
  · subst h2
    simp [swap_apply_of_ne_of_ne, hab, hac, hab.symm, hbc]
  by_cases h3 : x = c
  · subst h3
    simp [swap_apply_of_ne_of_ne, hac.symm, hbc.symm]
  simp [swap_apply_of_ne_of_ne, h1, h2, h3]

theorem swapMulSwap_conj_mem {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    {σ : Perm (Fin n)} (hσ : σ ∈ swapPairStab a b) (hc : σ c = c) :
    σ * (swap a b * swap b c) * σ⁻¹ = swap a b * swap b c ∨
      σ * (swap a b * swap b c) * σ⁻¹ = (swap a b * swap b c)⁻¹ := by
  have e : σ * (swap a b * swap b c) * σ⁻¹ = swap (σ a) (σ b) * swap (σ b) (σ c) := by
    rw [swap_apply_apply, swap_apply_apply]
    group
  rw [e, hc]
  rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    rw [h1, h2]
  · right
    rw [h1, h2, mul_inv_rev, swap_inv, swap_inv]
    exact swap_mul_swap_swap_eq hab hbc hac

theorem altMod_not_two_dvd_index (hn : 2 ≤ n) {Q P₀ : Subgroup (Perm (Fin n))}
    (hP₀Q : P₀ ≤ Q) (hP₀A : P₀ ≤ alternatingGroup (Fin n))
    (hP₀ : ¬ 2 ∣ P₀.relIndex (alternatingGroup (Fin n)))
    (hQ : ¬ Q ≤ alternatingGroup (Fin n)) : ¬ 2 ∣ Q.index := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  set A := alternatingGroup (Fin n) with hA
  have hA2 : A.index = 2 := alternatingGroup.index_eq_two
  have h1 : (Q ⊓ A).relIndex A ∣ P₀.relIndex A :=
    Subgroup.relIndex_dvd_of_le_left A (le_inf hP₀Q hP₀A)
  have h2 : (Q ⊓ A).relIndex A * A.index = (Q ⊓ A).index := Subgroup.relIndex_mul_index inf_le_right
  have h3 : (Q ⊓ A).relIndex Q * Q.index = (Q ⊓ A).index := Subgroup.relIndex_mul_index inf_le_left
  have h4 : (Q ⊓ A).relIndex Q = A.relIndex Q := Subgroup.inf_relIndex_left Q A
  have h5 : A.relIndex Q ∣ A.index := Subgroup.relIndex_dvd_index_of_normal A Q
  have h6 : A.relIndex Q ≠ 1 := by
    intro h
    exact hQ (Subgroup.relIndex_eq_one.1 h)
  have h7 : A.relIndex Q = 2 := by
    rw [hA2] at h5
    rcases (Nat.dvd_prime Nat.prime_two).1 h5 with h | h
    · exact absurd h h6
    · exact h
  intro hd
  rw [h4, h7] at h3
  rw [hA2] at h2
  have h8 : Q.index = (Q ⊓ A).relIndex A := by omega
  have hd' : 2 ∣ (Q ⊓ A).relIndex A := by rw [← h8]; exact hd
  exact hP₀ (hd'.trans h1)

end Pairs

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
