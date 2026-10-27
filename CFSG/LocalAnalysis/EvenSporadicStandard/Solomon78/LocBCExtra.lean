module

public import CFSG.Sporadic.Co1Block.TwoBComp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBCCheck
public import Certificates.Certificate26683

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block

section Extra


theorem co1_exists_not_mem : ∃ c : C₁, triHom c ∉ twoBD :=
  Certificates.certificate26683.2.2.2.1

theorem co1_card_ker_le : Nat.card (triHom : C₁ →* Equiv.Perm (Fin 1365)).ker ≤ 4 := by
  obtain ⟨t, ht, h8⟩ := exists_card_range_ker
  obtain ⟨c, hc⟩ := co1_exists_not_mem
  have ht2 : 2 ≤ t := by
    by_contra hlt
    have ht0 : t ≠ 0 := by
      rintro rfl
      have : 0 < Nat.card (triHom : C₁ →* Equiv.Perm (Fin 1365)).range := Nat.card_pos
      omega
    have ht1 : t = 1 := by omega
    subst ht1
    have hD : twoBD = (triHom : C₁ →* Equiv.Perm (Fin 1365)).range :=
      Subgroup.eq_of_le_of_card_ge twoBD_le_range (by rw [ht, mul_one])
    exact hc (hD ▸ ⟨c, rfl⟩)
  have : 2 * Nat.card (triHom : C₁ →* Equiv.Perm (Fin 1365)).ker ≤
      t * Nat.card (triHom : C₁ →* Equiv.Perm (Fin 1365)).ker := Nat.mul_le_mul_right _ ht2
  omega

theorem co1_centralizer_trivial {y : Equiv.Perm (Fin 1365)} (hy : ∀ d ∈ twoBD, y * d = d * y) :
    y = 1 :=
  Certificates.certificate26683.2.2.2.2 y hy

end Extra

end CFSG.EvenSporadicStandard.Solomon78
