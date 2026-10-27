module

public import CFSG.Quasithin.Background.BlueprintB2Thompson
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG

open CFSG.Quasithin.BlueprintB2

variable {H : Type*} [Group H] [Finite H]

theorem le_elemThompson_of_le_centralizer {p : ℕ} (hp : p.Prime) {X : Subgroup H}
    (hX : CFSG.Open.IsElemAbelian p X)
    (hcent : ∀ A : Subgroup H, IsElementaryAbelian p A → Nat.card A = p ^ pRank p H →
      X ≤ Subgroup.centralizer (A : Set H)) :
    X ≤ elemThompson H p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, hA⟩ := elemThompsonFamily_nonempty H p
  intro x hx
  exact le_elemThompson hA
    (mem_of_mem_centralizer_of_pow_eq_one hA.1 (mem_elemThompsonFamily_iff.mp hA).2
      (hcent A hA.1 hA.2 hx) (hX.2 x hx))

theorem elemThompsonCenterTorsion_le {p : ℕ} (hp : p.Prime) :
    elemThompsonCenterTorsion H p ≤ elemThompson H p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, hA⟩ := elemThompsonFamily_nonempty H p
  rw [elemThompsonCenterTorsion_eq_sInf]
  exact (sInf_le hA).trans (le_elemThompson hA)

end CFSG
