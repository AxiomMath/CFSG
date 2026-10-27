module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticSixCoverRadical

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticSixCover

open Subgroup CFSG.Assembly.LowTwoRank

theorem even_symplectic_six_catalog_perfect_central_two_cover_trivial {E : Type*} {J : Type}
    [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ center E) (h2 : IsPGroup 2 η.ker) {f : ℕ}
    (hf : 2 ≤ f) (hJ : CFSG.Blueprint.LieModel J .PSp 3 2 f) :
    η.ker = ⊥ ∧ Function.Bijective η := by
  obtain ⟨K, _, _, hcard, ⟨e⟩⟩ := exists_mulEquiv_statedSp_three_of_lieModel hJ
  have := finite_field_prime_power_characteristic (K := K) Nat.prime_two (by omega) hcard
  have hK : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set η' : E →* StatedSp 3 K := e.toMonoidHom.comp η
  have hη' : Function.Surjective η' := e.surjective.comp hη
  have hker' : η'.ker = η.ker := by
    ext z
    exact e.map_eq_one_iff
  have hbot := ker_eq_bot_of_statedSp_three hη' (hker' ▸ hC) hK (hker' ▸ h2)
  rw [hker'] at hbot
  exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩

end CFSG.LocalAnalysis.ComponentInitial.SymplecticSixCover
