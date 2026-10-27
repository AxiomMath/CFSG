module

public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
import CFSG.FeitThompson.Local.SecondCenterPlaneCharacteristicCentralizer

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {p a : ℕ} {P : Type*} [Group P] {X : Subgroup P}

theorem inf_eq_bot_of_natCard_eq_prime_of_not_le [Finite P] (hp : p.Prime) (hX : Nat.card X = p)
    {S : Subgroup P} (hXS : ¬ X ≤ S) : X ⊓ S = ⊥ := by
  have hdvd : Nat.card (X ⊓ S : Subgroup P) ∣ p :=
    hX ▸ Subgroup.card_dvd_of_le (inf_le_left : X ⊓ S ≤ X)
  rcases (Nat.dvd_prime hp).1 hdvd with h | h
  · exact Subgroup.card_eq_one.1 h
  · exact absurd (inf_eq_left.1
      (Subgroup.eq_of_le_of_card_ge (inf_le_left : X ⊓ S ≤ X) (by rw [hX, h]))) hXS

theorem inf_commutator_eq_bot_of_elementaryAbelianPRank_centralizer_le [Finite P] (hp : p.Prime)
    (hodd : Odd p) (hPp : IsPGroup p P) (hrank : 3 ≤ elementaryAbelianPRank p P)
    (hX : Nat.card X = p) (hCX : elementaryAbelianPRank p (centralizer (X : Set P)) ≤ 2) :
    X ⊓ commutator P = ⊥ := by
  have hfp := Fact.mk hp
  obtain ⟨a, hPa⟩ := hPp.exists_card_eq
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · exfalso
      have : Subsingleton P := (Nat.card_eq_one_iff_unique.1 (by simpa using hPa)).1
      rw [elementaryAbelianPRank_eq_zero_of_subsingleton hp.one_lt] at hrank
      omega
    · exact h
  obtain ⟨Z, hZ, hZc⟩ := exists_le_center_natCard_eq hp hPa ha
  have hmax : Maximal (fun A : Subgroup P => IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ p = 1) (X ⊔ Z) :=
    maximal_isElementaryAbelian_iff_maximal.1
      (maximal_isElementaryAbelian_sup hp hrank hCX hX hZ hZc)
  have hplane : Nat.card (X ⊔ Z : Subgroup P) = p ^ 2 :=
    natCard_sup_eq_sq_of_elementaryAbelianPRank_centralizer_le hp hrank hCX hX hZ hZc
  obtain ⟨hTchar, hTidx⟩ :=
    characteristic_and_index_centralizer_secondCenterTorsion hp hodd hPp hmax hplane hrank
  have hAT := not_le_centralizer_secondCenterTorsion hp hodd hPp hmax hplane hrank
  set T := centralizer ((secondCenterTorsion p P : Subgroup P) : Set P) with hT
  have : T.Characteristic := hTchar
  have hZT : Z ≤ T := hZ.trans (center_le_centralizer _)
  have hXT : ¬ X ≤ T := fun h => hAT (sup_le h hZT)
  have hcard : Nat.card (P ⧸ T) = p := by rw [← Subgroup.index_eq_card]; exact hTidx
  have : IsCyclic (P ⧸ T) := isCyclic_of_prime_card hcard
  have hcomm : commutator P ≤ T :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.1 inferInstance
  exact inf_eq_bot_of_natCard_eq_prime_of_not_le hp hX fun h => hXT (h.trans hcomm)

theorem inf_commutator_eq_bot_of_natCard_eq_pow (hp : p.Prime) (hodd : Odd p)
    (hPa : Nat.card P = p ^ a) (hrank : 3 ≤ elementaryAbelianPRank p P) (hX : Nat.card X = p)
    (hCX : elementaryAbelianPRank p (centralizer (X : Set P)) ≤ 2) :
    X ⊓ commutator P = ⊥ := by
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hPa]; exact pow_ne_zero _ hp.ne_zero)
  exact inf_commutator_eq_bot_of_elementaryAbelianPRank_centralizer_le hp hodd
    (IsPGroup.of_card hPa) hrank hX hCX

end

end CFSG.FeitThompson
