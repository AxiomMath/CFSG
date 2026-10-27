module

public import CFSG.LocalAnalysis.RankTwoShapes.SylowShapes
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverWreathFusion

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

@[expose] def RankTwoCoverUnitaryExcluded : Prop :=
  ∀ (J : Type) [Group J] [Finite J], commutator J = ⊤ → IsPGroup 2 (Subgroup.center J) →
    Subgroup.center J ≠ ⊥ → IsCyclic (Subgroup.center J) →
    IsSimpleGroup (J ⧸ Subgroup.center J) → ∀ S : Sylow 2 (J ⧸ Subgroup.center J),
    (∃ (H : Type) (_ : Group H) (U : Sylow 2 H),
      CFSG.Assembly.LowTwoRank.StatedClassicalModel H .PSU 3 2 2 ∧
        Nonempty ((S : Subgroup (J ⧸ Subgroup.center J)) ≃* (U : Subgroup H))) → False

theorem exists_mul_ne_of_perfect {K : Type*} [Group K] [Nontrivial K]
    (hperf : commutator K = ⊤) : ∃ a b : K, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hle : commutator K ≤ ⊥ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def, h a b, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  rw [hperf] at hle
  obtain ⟨a, b, hab⟩ := exists_pair_ne K
  have ha := Subgroup.mem_bot.mp (hle (Subgroup.mem_top a))
  have hb := Subgroup.mem_bot.mp (hle (Subgroup.mem_top b))
  exact hab (ha.trans hb.symm)

theorem eq_of_orderOf_eq_two_of_rankTwo_cover_of_unitaryExcluded
    (hU : RankTwoCoverUnitaryExcluded) {J : Type} [Group J] [Finite J]
    (hperf : commutator J = ⊤) (hZ : IsPGroup 2 (Subgroup.center J))
    (hZne : Subgroup.center J ≠ ⊥) (hcyc : IsCyclic (Subgroup.center J))
    (hsimple : IsSimpleGroup (J ⧸ Subgroup.center J))
    (hrank : CFSG.Assembly.twoRank (J ⧸ Subgroup.center J) = 2) {x y : J}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  obtain ⟨Q⟩ : Nonempty (Sylow 2 J) := inferInstance
  have hnonab := exists_mul_ne_of_perfect (commutator_quotient_center_eq_top hperf)
  rcases CFSG.RankTwoShapes.rank_two_sylow_shapes hnonab hrank (centralSylow Q) with
    ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | hunit
  · have hm : 2 ≤ 2 ^ (n - 1) := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right two_pos (by omega)
    exact eq_of_orderOf_eq_two_of_isCyclic hcyc (mem_center_of_dihedral hperf hZ hZne Q hm e hx)
      (mem_center_of_dihedral hperf hZ hZne Q hm e hy) hx hy
  · exact (false_of_semidihedral hperf hZ hZne Q hn e).elim
  · exact (false_of_wreathed hperf hZ hZne Q hn e).elim
  · exact (hU J hperf hZ hZne hcyc hsimple _ hunit).elim

end CFSG.ProperTwoGeneratedCore.Lemma37
