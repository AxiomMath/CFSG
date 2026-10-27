module

public import CFSG.GH74.E2.Shapes
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6D8
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.E2

open Subgroup

open CFSG.LocalAnalysis.ComponentInitial in
theorem shapeA6_alternating {K : Type} [Group K] (h : ShapeA6 K) :
    Nonempty (K ≃* alternatingGroup (Fin 6)) := by
  rcases h with h | h
  · exact h
  · rcases h with ⟨-, hm⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · obtain ⟨-, F, hfield, hfinite, hF, ⟨e⟩⟩ := hm
      let _ := hfield
      let _ := hfinite
      let _ : Fintype F := Fintype.ofFinite F
      have hF9 : Fintype.card F = 9 := by
        rw [← Nat.card_eq_fintype_card, hF]
        norm_num
      obtain ⟨e6⟩ :=
        unique_field_nine_projective_linear_alternating_six_isomorphism F hF9
      exact ⟨(e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
        F).symm).trans e6⟩
    · exact absurd h0 (by norm_num)
    · exact absurd h0 (by norm_num)
    · exact absurd h0 (by norm_num)

theorem sylow_two_of_shapeA6 {K : Type} [Group K] [Finite K] (h : ShapeA6 K) (T : Sylow 2 K) :
    Nonempty (↥(T : Subgroup K) ≃* DihedralGroup 4) := by
  obtain ⟨e⟩ := shapeA6_alternating h
  have hK : Nat.card K = 360 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.QuasithinUnique.DoubleA3.card_alt6
  have hfac : (Nat.card K).factorization 2 = 3 := by
    rw [hK, show (360 : ℕ) = 2 ^ 3 * 45 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.add_apply, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hT : Nat.card (T : Subgroup K) = 8 := by
    rw [T.card_eq_multiplicity, hfac]
    norm_num
  have hmap : Nat.card ((T : Subgroup K).map e.toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact hT
  obtain ⟨f⟩ := CFSG.QuasithinUnique.DoubleA3.nonempty_dihedral_of_card_eight _ hmap
  exact ⟨((T : Subgroup K).equivMapOfInjective e.toMonoidHom e.injective).trans f⟩

end CFSG.GH74.E2
