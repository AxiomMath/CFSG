module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverPrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverLevi

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open OrthogonalSplit Matrix CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

theorem even_split_orthogonal_prime_field_central_two_cover_trivial {E : Type*} {J : Type}
    [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    {n : ℕ} (hn : 5 ≤ n) (hJ : CFSG.Blueprint.LieModel J .POmegaPlus n 2 1) :
    η.ker = ⊥ ∧ Function.Bijective η := by
  obtain ⟨K, _, _, _, hcard, -, ⟨e⟩⟩ := exists_mulEquiv_elementaryGroup_of_lieModel hJ
  have hK : Nat.card K = 2 := by rw [hcard, pow_one]
  have hr : 3 ≤ n := by omega
  have hcomp : (leviTwo n K hr).comp SpecialLinearGroup.toGL = leviSLTwo n K hr :=
    MonoidHom.ext (leviTwo_toGL hr)
  obtain ⟨S, hS, hVUR⟩ := exists_sylow_leviSLTwo_radicalTwo hr hK
  rw [← hcomp] at hS hVUR
  set η' := e.toMonoidHom.comp η with hη'
  have hker' : η'.ker = η.ker := by
    ext z
    exact e.map_eq_one_iff
  have hbot := ker_eq_bot_of_model hn (leviTwo n K hr) (leviTwo_injective hr) (radicalTwo n K)
    radicalTwo_injective altCongr coe_altCongr (leviTwo_mul_radicalTwo_mul_inv hr) S hS hVUR η'
    (e.surjective.comp hη) (hker' ▸ hC) (hker' ▸ h2)
  rw [hker'] at hbot
  exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩

end CFSG.LocalAnalysis.ComponentInitial
