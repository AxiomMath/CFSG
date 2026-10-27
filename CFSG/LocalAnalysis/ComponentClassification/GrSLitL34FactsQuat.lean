
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsQuatBase
import all CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsQuatBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsLocal
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePCases
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCover

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Subgroup

theorem q8_spec {k : ℕ} (hk : k < 64) :
    wordPerm (tg k) * r₄ = r₄ * wordPerm (tg k) ↔ k ∈ q8Idx := by
  have h := coverParts.q8 k hk
  have hrep := tabRep_wordTab (tg k)
  rw [← (hrep.comp tabRep_r₄).beq_iff (tabRep_r₄.comp hrep), h]
  exact List.elem_iff

theorem qt₁_mul_qt₂_ne : qt₁ * qt₂ ≠ qt₂ * qt₁ := by
  obtain ⟨-, -, -, hc1, h5, -⟩ := quat_relations
  generalize qt₁ = a at *
  generalize qt₂ = b at *
  generalize qc = c at *
  intro h
  apply hc1
  have : b * c * a = b * a := h5.symm.trans h
  simpa using this

theorem tg_mem_Q8 {k : ℕ} (hk : k ∈ q8Idx) : wordPerm (tg k) ∈ Q8 :=
  mem_Q8.2 ⟨(q8_spec (lt_of_mem_q8Idx k hk)).2 hk, tg_mem_T0 k (lt_of_mem_q8Idx k hk)⟩

theorem qt₁_mem_Q8 : qt₁ ∈ Q8 := tg_mem_Q8 (by decide)

theorem qt₂_mem_Q8 : qt₂ ∈ Q8 := tg_mem_Q8 (by decide)

theorem qc_mem_Q8 : qc ∈ Q8 := tg_mem_Q8 (by decide)

theorem card_Q8 : Nat.card Q8 = 8 := by
  have h := card_set_of_tabs (X := (Q8 : Set (Equiv.Perm (Fin 42)))) (L := q8Idx.map tgT)
    (fun t ht => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht
      exact ⟨_, tg_mem_Q8 hk, tabRep_tgT k⟩)
    (fun g hg => by
      obtain ⟨hc, hT⟩ := mem_Q8.1 hg
      obtain ⟨k, hk, rfl⟩ := exists_tg hT
      exact ⟨tgT k, List.mem_map.mpr ⟨k, (q8_spec hk).1 hc, rfl⟩, tabRep_tgT k⟩)
    (List.Nodup.map_on (fun k hk l hl he => by
      by_contra hne
      have hk' := lt_of_mem_q8Idx k hk
      have hl' := lt_of_mem_q8Idx l hl
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact coverParts.distinct l hl' k h he.symm
      · exact coverParts.distinct k hk' l h he) (by decide))
  rw [List.length_map] at h
  exact h

theorem eq_of_mem_Q8_of_mul_self {t : Equiv.Perm (Fin 42)} (ht : t ∈ Q8) (h2 : t * t = 1) :
    t = 1 ∨ t = qc := by
  obtain ⟨hc, hT⟩ := mem_Q8.1 ht
  obtain ⟨k, hk, rfl⟩ := exists_tg hT
  have hq := (q8_spec hk).1 hc
  have hinv := coverParts.invols k hk
  have h1 : comp 42 (wordTab (tg k)) (wordTab (tg k)) = idTab 42 :=
    ((tabRep_wordTab _).comp (tabRep_wordTab _)).tab_eq (h2 ▸ TabRep.idTab)
  rw [h1, beq_self_eq_true] at hinv
  rcases q8_invol_idx k hq hinv.symm with rfl | rfl
  · exact Or.inl wordPerm_tg_zero
  · exact Or.inr rfl

theorem not_isCyclic_Q8 : ¬ IsCyclic Q8 :=
  not_isCyclic_of_ne qt₁_mem_Q8 qt₂_mem_Q8 qt₁_mul_qt₂_ne

theorem mul_self_mem_Q8 {t : Equiv.Perm (Fin 42)} (ht : t ∈ Q8) :
    t * t = 1 ∨ t * t = qc := by
  have hdvd : orderOf (⟨t, ht⟩ : Q8) ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = Nat.card Q8 by rw [card_Q8]; rfl]
    exact orderOf_dvd_natCard _
  obtain ⟨m, hm, hmo⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hm3 : m ≠ 3 := by
    rintro rfl
    exact not_isCyclic_Q8 (isCyclic_of_orderOf_eq_card _ (by rw [hmo, card_Q8]; rfl))
  have h4 : (⟨t, ht⟩ : Q8) ^ (2 ^ 2) = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.1
    rw [hmo]
    exact pow_dvd_pow 2 (by omega)
  have h4' : t ^ 4 = 1 := by
    have := congrArg Subtype.val h4
    simpa using this
  have h4'' : t * t * (t * t) = 1 := by
    rw [← h4']
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  exact eq_of_mem_Q8_of_mul_self (Q8.mul_mem ht ht) h4''

theorem nonempty_Q8_equiv :
    Nonempty (Q8 ≃* QuaternionGroup 2) := by
  have hp : IsPGroup 2 Q8 := IsPGroup.of_card (n := 3) (by rw [card_Q8]; rfl)
  have hrank : CFSG.Open.twoRank Q8 ≤ 1 :=
    CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore.twoRank_le_one_of_unique (e := qc)
      fun t ht ho => by
        have h2 : t * t = 1 := by rw [← pow_two, ← ho, pow_orderOf_eq_one]
        rcases eq_of_mem_Q8_of_mul_self ht h2 with h | h
        · rw [h, orderOf_one] at ho
          exact absurd ho (by norm_num)
        · exact h
  rcases CFSG.TwoRankLowerBound.Helpers.rank_one_two_group_cyclic_or_quaternion Q8 hp hrank with
    h | ⟨n, hn, ⟨e⟩⟩
  · exact absurd h not_isCyclic_Q8
  · have hc := Nat.card_congr e.toEquiv
    rw [card_Q8, CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore.card_quaternionGroup_two_pow
      hn] at hc
    have hn3 : n = 3 := by
      have : (2 : ℕ) ^ n = 2 ^ 3 := by rw [← hc]; rfl
      exact Nat.pow_right_injective le_rfl this
    subst hn3
    exact ⟨e⟩

end CFSG.ComponentClassification.GrSLit.L34Facts
