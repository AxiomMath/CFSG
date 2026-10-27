module

public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.ExactGL2Recognition
public import CFSG.LocalAnalysis.RankTwoShapes.Homocyclic.ExponentTwo

public section

open scoped Classical

namespace CFSG.Semidihedral.GL2Recognition

open CFSG.Semidihedral.Principal

theorem odd_core_free_GL2_centralizer_quotient_ker_eq_bot {G : Type} [Group G] [Finite G]
    (hodd : ∀ K : Subgroup G, K.Normal → Odd (Nat.card K) → K = ⊥)
    (hinv : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) (t : G) (ht : orderOf t = 2)
    (π : Subgroup.centralizer ({t} : Set G) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (hπ : Function.Surjective π) (hN : Odd (Nat.card π.ker))
    (hπt : π ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ = -1) :
    π.ker = ⊥ := by
  have := Fintype.ofFinite G
  obtain ⟨ideal, hmax, hchar⟩ := CFSG.RankTwoShapes.exists_maximal_ideal_residue_two
  obtain ⟨basis⟩ :=
    CFSG.TwoRankLowerBound.Helpers.finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_exists_principal_label basis
  obtain ⟨⟨β, hβ, hβz⟩, hall⟩ := odd_kernel_GL2_scaled_orders_and_faithful_small_character
    ideal basis principal hprincipal hinv t ht π hπ hN hπt
  have helim := small_faithful_principal_character_eliminates_GL2_odd_kernel ideal basis
    principal hprincipal t ht π hπ hN hπt
  rcases hall β hβ hβz with ⟨⟨-, -, χ, hχ, h10, ht2, -, hrat, hfaith⟩, -⟩ |
      ⟨⟨-, -, χ, hχ, h12, -, ht4, hrat, hfaith⟩, -⟩
  · exact (helim χ hχ (hfaith hodd) hrat).2 (Or.inl ⟨h10, ht2⟩)
  · exact (helim χ hχ (hfaith hodd) hrat).2 (Or.inr ⟨h12, ht4⟩)

theorem odd_core_free_GL2_centralizer_quotient_recognition
    {G : Type} [Group G] [Finite G]
    (hodd : ∀ K : Subgroup G, K.Normal → Odd (Nat.card K) → K = ⊥)
    (hinv : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) (t : G) (ht : orderOf t = 2)
    (π : Subgroup.centralizer ({t} : Set G) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (hπ : Function.Surjective π) (hN : Odd (Nat.card π.ker))
    (hπt : π ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ = -1) :
    π.ker = ⊥ ∧ Function.Bijective π ∧ commutator G = ⊤ ∧
      Xor (Nat.card G = 5616 ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 3 1)
        (Nat.card G = 7920 ∧ Nonempty (G ≃* CFSG.Open.StatedM11) ∧
          Nonempty (G ≃* CFSG.Assembly.LowTwoRank.StatedM11)) := by
  have hker := odd_core_free_GL2_centralizer_quotient_ker_eq_bot hodd hinv t ht π hπ hN hπt
  have hbij : Function.Bijective π := ⟨(MonoidHom.ker_eq_bot_iff π).mp hker, hπ⟩
  exact ⟨hker, hbij, exact_GL2_three_involution_centralizer_recognition hinv t ht
    ⟨MulEquiv.ofBijective π hbij⟩⟩

end CFSG.Semidihedral.GL2Recognition
