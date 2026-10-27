module

public import CFSG.RankThree.Chevalley.SmallReeCentralExtension

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.LieType.Ree
open CFSG.RankThree.Chevalley (small_Ree_sylow_isCyclic)

theorem ree_no_plane {a : ℕ} (_ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) {r : ℕ} (hr : r.Prime)
    (hr3 : 3 < r) (E : Subgroup ↥(ReeTag.G2.reeGamma K a)) (hE : CFSG.IsElementaryAbelian r E)
    (hEc : Nat.card E = r ^ 2) : False := by
  have : Fact r.Prime := ⟨hr⟩
  have := hE
  obtain ⟨R, hER⟩ := (IsElementaryAbelian.isPGroup r E).exists_le_sylow
  have := small_Ree_sylow_isCyclic a K hK hr hr3 R
  have hEcyc : IsCyclic E :=
    isCyclic_of_injective (Subgroup.inclusion hER) (Subgroup.inclusion_injective hER)
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; exact pow_ne_zero 2 hr.ne_zero)
  exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hEc hEcyc

end CFSG.GH74.GLS.Stage2.Bender.Thm1
