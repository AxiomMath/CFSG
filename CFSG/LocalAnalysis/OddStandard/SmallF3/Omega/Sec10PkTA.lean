module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PkE
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Syl

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.ClassicalInvolution.Q3.TA3.Check

local notation "P45" => Equiv.Perm (Fin 45)

namespace Pk

theorem exists_pair_of_pocket {K : Subgroup P45} (hK : IsSL23Mod K) {y : P45} (hyK : y ∈ K)
    (hy : orderOf y = 2) :
    ∃ a b : P45, a ∈ K ∧ b ∈ K ∧ a * a = y ∧ b * b = y ∧ b * a = y * a * b := by
  obtain ⟨f, -, hf2, hfK⟩ := exists_quaternion_of_isSL23Mod hK hyK hy
  refine ⟨f (QuaternionGroup.a 1), f (QuaternionGroup.xa 0), hfK (MonoidHom.mem_range.2 ⟨_, rfl⟩),
    hfK (MonoidHom.mem_range.2 ⟨_, rfl⟩), ?_, ?_, ?_⟩
  · rw [← map_mul, show (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 =
      QuaternionGroup.a 2 by decide +kernel, hf2]
  · rw [← map_mul, show (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
      QuaternionGroup.a 2 by decide +kernel, hf2]
  · rw [← hf2]
    simp only [← map_mul]
    congr 1

theorem not_both_quaternion {K : Subgroup P45}
    (hK24 : Nat.card K = 24) (h1 : ∀ q ∈ Q1l, q ∈ K) (h2 : ∀ q ∈ Q2l, q ∈ K) : False := by
  obtain ⟨s, hs, hsp⟩ := facts.prod
  have := card_finset_le_card (K := K) (s := s) fun p hp => by
    obtain ⟨q, hq, r, hr, rfl⟩ := hsp p hp
    exact K.mul_mem (h1 q hq) (h2 r hr)
  omega

theorem q8B_subset {K : Subgroup P45} {t a b : P45} (ht : t ∈ K) (ha : a ∈ K) (hb : b ∈ K) :
    ∀ q ∈ q8B t a b, q ∈ K := by
  intro q hq
  simp only [q8B, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact K.one_mem
  · exact ha
  · exact ht
  · exact K.mul_mem ht ha
  · exact hb
  · exact K.mul_mem hb ha
  · exact K.mul_mem hb ht
  · exact K.mul_mem hb (K.mul_mem ht ha)

theorem pocket_tA_cases
    {K : Subgroup P45} (hK : Sl23PocketIn P0 tA K) : K = KA ∨ K = KB := by
  have hKC : K ≤ Cs := hK.2.1
  have hodd := oddCore_eq_bot_of_subnormal hKC noOdd_Cs hK.2.2.1
  obtain ⟨hK24, hgen⟩ := sl23_facts hK.2.2.2 hodd
  obtain ⟨a, b, haK, hbK, haa, hbb, hba⟩ := exists_pair_of_pocket hK.2.2.2 hK.1 orderOf_tA
  have hq8 := q8B_subset hK.1 haK hbK
  have hcases := facts.pair a (hKC haK) b (hKC hbK) haa hbb hba
  have hP : ∀ x ∈ K, x ∈ P0 := fun x hx => (Subgroup.mem_inf.1 (hKC hx)).1
  rcases hcases with h1 | h2
  · left
    have hQ1 : ∀ q ∈ Q1l, q ∈ K := fun q hq => hq8 q (h1 q hq)
    have hcube : ∀ x ∈ K, x ^ 3 = 1 → x ∈ KA := by
      intro x hx hx3
      refine cent_KA (hP x hx) ?_
      by_contra hnc
      obtain ⟨hQC, h1', h2', h3'⟩ := facts.subQ2
      exact not_both_quaternion hK24 hQ1 (list_le_of_noncentral hKC hK.2.2.1 hK.1 hx
        hQC h1' h2' h3' (facts.nsQ2 x (hKC hx) hx3 hnc))
    exact Subgroup.eq_of_le_of_card_ge (hgen KA hcube) (by rw [hK24, card_KA])
  · right
    have hQ2 : ∀ q ∈ Q2l, q ∈ K := fun q hq => hq8 q (h2 q hq)
    have hcube : ∀ x ∈ K, x ^ 3 = 1 → x ∈ KB := by
      intro x hx hx3
      refine cent_KB (hP x hx) ?_
      by_contra hnc
      obtain ⟨hQC, h1', h2', h3'⟩ := facts.subQ1
      exact not_both_quaternion hK24 (list_le_of_noncentral hKC hK.2.2.1 hK.1 hx
        hQC h1' h2' h3' (facts.nsQ1 x (hKC hx) hx3 hnc)) hQ2
    exact Subgroup.eq_of_le_of_card_ge (hgen KB hcube) (by rw [hK24, card_KB])

end Pk

end CFSG.OddStandard.SmallF3.Omega
