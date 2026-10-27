module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveCard
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaInvol
import CFSG.CharacterTheory.Burnside

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem cl_isSolvable_of_natCard {G : Type} [Group G] [Finite G] {a b : ℕ}
    (h : Nat.card G = 2 ^ a * 3 ^ b) : Group.IsSolvable G := by
  have := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    Nat.prime_two Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact h)

private theorem cl_subsingleton_oGroup_of_finrank_eq_zero
    (h : Module.finrank (ZMod 3) V = 0) : Subsingleton (OGroup Q) :=
  ⟨fun _ _ => Subtype.ext (LinearEquiv.ext fun _ =>
    (finrank_zero_iff_forall_zero.mp h _).trans (finrank_zero_iff_forall_zero.mp h _).symm)⟩

theorem cl_omegaGroup_eq_bot_of_finrank_le_one (hQ : Q.Nondegenerate)
    (h : Module.finrank (ZMod 3) V ≤ 1) : omegaGroup hQ = ⊥ := by
  refine eq_bot_iff.mpr fun g hg => (Subgroup.mem_bot).mpr ?_
  rcases Nat.lt_or_ge (Module.finrank (ZMod 3) V) 1 with h0 | h1
  · have := cl_subsingleton_oGroup_of_finrank_eq_zero (Q := Q) (by omega)
    exact Subsingleton.elim _ _
  · have hdim : Module.finrank (ZMod 3) V = 1 := by omega
    have hπ1 : piOrth Q ≠ 1 := piOrth_ne_one (by omega)
    have hπ : piOrth Q ∉ omegaGroup hQ := by
      rw [piOrth_mem_omegaGroup_iff hQ, hdim]
      exact fun h => (by decide : ¬ Even (1 : ℕ)) h.1
    by_contra hg1
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : OGroup Q)).mp (natCard_oGroup_one hQ hdim)
    exact hπ ((hy g hg1).trans (hy _ hπ1).symm ▸ hg)

theorem cl_blockHom_left_mem_omegaGroup (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    {a : OGroup (Q.restrict (fixSp s))}
    (ha : a ∈ omegaGroup (nondegenerate_restrict_fixSp hQ hs)) :
    blockHom hs (a, 1) ∈ omegaGroup hQ := by
  rcases le_or_gt 2 (Module.finrank (ZMod 3) (fixSp s)) with hW | hW
  · exact blockHom_left_mem_omegaGroup hQ hs hW ha
  · rw [cl_omegaGroup_eq_bot_of_finrank_le_one (nondegenerate_restrict_fixSp hQ hs) (by omega),
      Subgroup.mem_bot] at ha
    rw [ha, Prod.mk_one_one, map_one]
    exact (omegaGroup hQ).one_mem

theorem cl_blockHom_right_mem_omegaGroup (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    {b : OGroup (Q.restrict (commSp s))}
    (hb : b ∈ omegaGroup (nondegenerate_restrict_commSp hQ hs)) :
    blockHom hs (1, b) ∈ omegaGroup hQ := by
  rcases le_or_gt 2 (Module.finrank (ZMod 3) (commSp s)) with hU | hU
  · exact blockHom_right_mem_omegaGroup hQ hs hU hb
  · rw [cl_omegaGroup_eq_bot_of_finrank_le_one (nondegenerate_restrict_commSp hQ hs) (by omega),
      Subgroup.mem_bot] at hb
    rw [hb, Prod.mk_one_one, map_one]
    exact (omegaGroup hQ).one_mem

theorem cl_isSolvable_oGroup_of_finrank_le_three (hQ : Q.Nondegenerate)
    (h : Module.finrank (ZMod 3) V ≤ 3) : Group.IsSolvable (OGroup Q) := by
  rcases (by omega : Module.finrank (ZMod 3) V = 0 ∨ Module.finrank (ZMod 3) V = 1 ∨
      Module.finrank (ZMod 3) V = 2 ∨ Module.finrank (ZMod 3) V = 3) with h0 | h1 | h2 | h3
  · have := cl_subsingleton_oGroup_of_finrank_eq_zero (Q := Q) h0
    infer_instance
  · exact cl_isSolvable_of_natCard (a := 1) (b := 0) (by rw [natCard_oGroup_one hQ h1]; norm_num)
  · rcases Int.units_eq_one_or (quadSign Q) with hs | hs
    · exact cl_isSolvable_of_natCard (a := 2) (b := 0)
        (by rw [natCard_oGroup_two_plus hQ h2 hs]; norm_num)
    · exact cl_isSolvable_of_natCard (a := 3) (b := 0)
        (by rw [natCard_oGroup_two_minus hQ h2 hs]; norm_num)
  · exact cl_isSolvable_of_natCard (a := 4) (b := 1)
      (by rw [natCard_oGroup_three hQ h3]; norm_num)

theorem cl_isSolvable_oGroup_four_plus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 4) (hs : quadSign Q = 1) :
    Group.IsSolvable (OGroup Q) :=
  cl_isSolvable_of_natCard (a := 7) (b := 2) (by rw [natCard_oGroup_four_plus hQ hdim hs]; norm_num)

theorem cl_isSolvable_omegaGroup_of_small (hQ : Q.Nondegenerate)
    (h : Module.finrank (ZMod 3) V ≤ 3 ∨
      (Module.finrank (ZMod 3) V = 4 ∧ quadSign Q = 1)) :
    Group.IsSolvable (omegaGroup hQ) := by
  have : Group.IsSolvable (OGroup Q) := by
    rcases h with h | ⟨hdim, hs⟩
    · exact cl_isSolvable_oGroup_of_finrank_le_three hQ h
    · exact cl_isSolvable_oGroup_four_plus hQ hdim hs
  infer_instance

end CFSG.OddStandard.SmallF3.Omega
