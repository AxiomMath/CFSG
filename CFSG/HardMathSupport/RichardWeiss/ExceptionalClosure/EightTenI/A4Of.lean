module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1547Block
public import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLGroup

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open CFSG.Open CFSG.Quasithin.EmptyFaithfulMultiple.L1547
open CFSG.HardMathSupport.Cooperstein.StructureLie

variable {G : Type} [Group G]

theorem alt4_pow_six (g : alternatingGroup (Fin 4)) (h : g ^ 6 = 1) : g ^ 2 = 1 ∨ g ^ 3 = 1 := by
  revert g; decide +kernel

theorem exists_isA4_of_mulEquiv {A : Subgroup G}
    (e : ↥A ≃* alternatingGroup (Fin 4)) : ∃ Q : Subgroup G, IsA4 A Q ∧ Q = pCoreOf 2 A := by
  have h4 : Nat.card (Fin 4) = 4 := by simp
  set K : Subgroup (alternatingGroup (Fin 4)) := alternatingGroup.kleinFour (Fin 4) with hK
  have hKn : K.Normal := alternatingGroup.normal_kleinFour h4
  have hKcard : Nat.card K = 4 := alternatingGroup.kleinFour_card_of_card_eq_four h4
  let Qa : Subgroup ↥A := K.map e.symm.toMonoidHom
  have hQan : Qa.Normal := hKn.map _ e.symm.surjective
  have hmemQa : ∀ a : ↥A, a ∈ Qa ↔ e a ∈ K := by
    intro a
    constructor
    · rintro ⟨k, hk, rfl⟩
      simpa using hk
    · intro h
      exact ⟨e a, h, by simp⟩
  have hQacard : Nat.card Qa = 4 := by
    rw [Subgroup.card_map_of_injective e.symm.injective]; exact hKcard
  set Q : Subgroup G := Qa.map A.subtype with hQdef
  have hQle : Q ≤ A := Subgroup.map_subtype_le Qa
  have hmemQ : ∀ a : ↥A, (a : G) ∈ Q ↔ a ∈ Qa := by
    intro a
    exact Subgroup.mem_map_iff_mem A.subtype_injective
  have hsq : ∀ a : ↥A, a ∈ Qa → a ^ 2 = 1 := by
    intro a ha
    have h1 : e a ∈ K := (hmemQa a).mp ha
    have h2 : (⟨e a, h1⟩ : K) ^ Monoid.exponent K = 1 := Monoid.pow_exponent_eq_one _
    rw [alternatingGroup.exponent_kleinFour_of_card_eq_four h4] at h2
    have h3 : (e a) ^ 2 = 1 := congrArg Subtype.val h2
    apply e.injective
    rw [map_pow, h3, map_one]
  have hKidx : K.index = 3 := by
    have h1 := Subgroup.card_mul_index K
    have h2 : Nat.card (alternatingGroup (Fin 4)) = 12 := by
      rw [Nat.card_eq_fintype_card]; decide +kernel
    rw [hKcard, h2] at h1
    omega
  have hcubeA : ∀ a : ↥A, a ^ 3 ∈ Qa := by
    intro a
    rw [hmemQa, map_pow]
    have := Subgroup.pow_index_mem K (e a)
    rwa [hKidx] at this
  have hAcard : Nat.card A = 12 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]; decide +kernel
  have hQsub : Q.subgroupOf A = Qa := by
    ext a
    rw [Subgroup.mem_subgroupOf]
    exact hmemQ a
  have hnorm : A ≤ Subgroup.normalizer (Q : Set G) := by
    have hn : (Q.subgroupOf A).Normal := by rw [hQsub]; exact hQan
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQle).mp hn
  have hQcard : Nat.card Q = 4 := by
    rw [hQdef, Subgroup.card_map_of_injective A.subtype_injective]; exact hQacard
  have hA4 : IsA4 A Q := by
    refine ⟨hQle, hnorm, hQcard, ?_, hAcard, ?_, ?_⟩
    · intro q hq
      obtain ⟨a, ha, rfl⟩ := hq
      have := hsq a ha
      simpa using congrArg Subtype.val this
    · intro x hx
      have := (hmemQ (⟨x, hx⟩ ^ 3)).mpr (hcubeA ⟨x, hx⟩)
      simpa using this
    · intro p hpA hp3 q hq hpq
      obtain ⟨a, ha, rfl⟩ := hq
      have hp3' : p ^ 3 = 1 := by rw [← hp3]; exact pow_orderOf_eq_one p
      have hp2 : p ^ 2 ≠ 1 := by
        intro h
        have := orderOf_dvd_of_pow_eq_one h
        rw [hp3] at this
        omega
      let pA : ↥A := ⟨p, hpA⟩
      have hcomm : Commute pA a := Subtype.ext hpq
      have hpA3 : pA ^ 3 = 1 := Subtype.ext (by simpa using hp3')
      have ha2 := hsq a ha
      have hr6 : (pA * a) ^ 6 = 1 := by
        have e1 : pA ^ 6 = 1 := by rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, hpA3, one_pow]
        have e2 : a ^ 6 = 1 := by rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, ha2, one_pow]
        rw [hcomm.mul_pow, e1, e2, one_mul]
      have h6 : (e (pA * a)) ^ 6 = 1 := by rw [← map_pow, hr6, map_one]
      rcases alt4_pow_six _ h6 with h | h
      · exfalso
        have h' : (pA * a) ^ 2 = 1 := e.injective (by rw [map_pow, h, map_one])
        rw [hcomm.mul_pow, ha2, mul_one] at h'
        exact hp2 (by simpa using congrArg Subtype.val h')
      · have h' : (pA * a) ^ 3 = 1 := e.injective (by rw [map_pow, h, map_one])
        rw [hcomm.mul_pow, hpA3, one_mul, pow_succ, ha2, one_mul] at h'
        simpa using congrArg Subtype.val h'
  refine ⟨Q, hA4, le_antisymm ?_ ?_⟩
  · exact le_pCoreOf_of_le_normalizer hQle hnorm hA4.isPGroup
  · intro z hz
    have hzA : z ∈ A := pCoreOf_le_self A hz
    obtain ⟨k, hk⟩ := isPGroup_pCoreOf A ⟨z, hz⟩
    have hzk : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hz3 : z ^ 3 ∈ Q := hA4.cube z hzA
    have hcop : IsCoprime (3 : ℤ) (2 ^ k) := by
      apply IsCoprime.pow_right
      exact Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num)
    obtain ⟨u, v, huv⟩ := hcop
    have h1 : z ^ ((3 : ℤ) * u + (2 ^ k : ℤ) * v) = z := by
      rw [show (3 : ℤ) * u + 2 ^ k * v = 1 by linarith]
      exact zpow_one z
    rw [zpow_add, zpow_mul, zpow_mul] at h1
    have e3 : z ^ (3 : ℤ) = z ^ 3 := zpow_natCast z 3
    have e4 : z ^ ((2 : ℤ) ^ k) = 1 := by
      have : ((2 : ℤ) ^ k) = ((2 ^ k : ℕ) : ℤ) := by push_cast; rfl
      rw [this, zpow_natCast, hzk]
    rw [e3, e4, one_zpow, mul_one] at h1
    rw [← h1]
    exact Q.zpow_mem hz3 u

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

end
