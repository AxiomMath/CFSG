module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.GroupTheory

open CFSG.ABGLocalTools

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem le_sup_of_isPGroup_quotient_of_isSylowOf {C S Y : Subgroup G} (hCY : C ≤ Y)
    [hCnormal : (C.subgroupOf Y).Normal] (hSyl : IsSylowOf p S Y)
    (hquot : IsPGroup p (↥Y ⧸ C.subgroupOf Y)) :
    Y ≤ C ⊔ S := by
  have hSleY : S ≤ Y := hSyl.le
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hquot
  have hCrel : C.relIndex Y = p ^ k := by
    rw [show C.relIndex Y = (C.subgroupOf Y).index from rfl, Subgroup.index_eq_card]
    exact hk
  have hSnot : ¬ p ∣ S.relIndex Y := (isSylowOf_iff.mp hSyl).2.2
  have hdvdC : (C ⊔ S).relIndex Y ∣ C.relIndex Y :=
    Subgroup.relIndex_dvd_of_le_left Y le_sup_left
  have hdvdS : (C ⊔ S).relIndex Y ∣ S.relIndex Y :=
    Subgroup.relIndex_dvd_of_le_left Y le_sup_right
  have hdvdPow : (C ⊔ S).relIndex Y ∣ p ^ k := hCrel ▸ hdvdC
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvdPow
  have hnotdvd : ¬ p ∣ (C ⊔ S).relIndex Y := fun h => hSnot (h.trans hdvdS)
  have hj0 : j = 0 := by
    by_contra h
    apply hnotdvd
    rw [hj]
    exact dvd_pow_self p h
  have hrel1 : (C ⊔ S).relIndex Y = 1 := by rw [hj, hj0, pow_zero]
  exact Subgroup.relIndex_eq_one.mp hrel1

end CFSG.GroupTheory
