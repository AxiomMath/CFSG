module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0Mono
public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Perf
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.UniqueCo1
public import CFSG.Monster.Existence.Compat.Co1Iso

public section

namespace CFSG.ComponentClassification.Sol76T13.R12.Pcls

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Open CFSG.Monster
  CFSG.Monster.ScalarKernel CFSG.Monster.Existence.Compat CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.EvenSporadicStandard.TwoCo1 CFSG.RankThree.PartTwo.Sec4.Census

theorem sporadicCoverRankInput_Co1 :
    SporadicCoverRankInput .Co1 := by
  intro Q _ _ hQ hZ2 hS
  have hmCo0 : IsSporadic (monsterCo0 ⧸ center monsterCo0) .Co1 := ⟨co1EquivMonsterCo1.symm⟩
  have hnegsq : negCo0 ^ 2 = 1 := by
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    show (negCo0 * negCo0 : monsterCo0).1 v = v
    show (negCo0 : monsterCo0).1 ((negCo0 : monsterCo0).1 v) = v
    rw [coe_negCo0, coe_negCo0, neg_neg]
  have hnegne : negCo0 ≠ 1 := by
    intro h1
    rw [← co0Equiv_negOneO] at h1
    have h2' : negOneO = 1 := co0Equiv.injective (h1.trans (map_one co0Equiv).symm)
    have h3 := congrArg (fun g => mat g (0 : Fin 24) 0) h2'
    simp [mat_negOneO, mat_one] at h3
    norm_num at h3
  have hc2 : Nat.card (center monsterCo0) = 2 := by
    rw [center_monsterCo0, Nat.card_zpowers]
    exact orderOf_eq_prime hnegsq hnegne
  have : Finite monsterCo0 := by
    have hfC : Finite NativeSporadic.Co1 := (CFSG.Sporadic.Co1.fam_co1_simplicity).1
    have hfQ : Finite MonsterCo1 := Finite.of_equiv _ co1EquivMonsterCo1.toEquiv
    refine Nat.finite_of_card_ne_zero ?_
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center monsterCo0), hc2]
    have : Nat.card (monsterCo0 ⧸ center monsterCo0) ≠ 0 := Nat.card_pos.ne'
    omega
  obtain ⟨e⟩ := nonempty_mulEquiv_of_doubleCovers_Co1 hQ.1 monsterCo0_isPerfect hZ2 hc2 hS hmCo0
  have hA2 : ∀ g ∈ monoSub ⊥, g ^ 2 = 1 := by
    rintro _ ⟨a, p, hp, rfl⟩
    rw [mem_bot] at hp
    rw [hp, PO_one, mul_one, pow_two, gO_mul_self]
  have hcardA : Nat.card (monoSub ⊥) = 2 ^ 12 := by
    rw [card_monoSub, Subgroup.card_bot, mul_one]
  set f : latticeO →* Q := e.symm.toMonoidHom.comp co0Equiv.toMonoidHom with hf
  have hfinj : Function.Injective f := e.symm.injective.comp co0Equiv.injective
  set A : Subgroup Q := (monoSub ⊥).map f
  have hA'2 : ∀ a ∈ A, a ^ 2 = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    rw [← map_pow, hA2 g hg, map_one]
  have hA : CFSG.IsElementaryAbelian 2 A :=
    { toIsMulCommutative :=
        ⟨⟨fun a b => Subtype.ext (DoubleCoverLift.mul_comm_of_sq_eq_one hA'2 a.2 b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (hA'2 a a.2) }
  have hcard : Nat.card A = 2 ^ 12 := by
    rw [Subgroup.card_map_of_injective hfinj, hcardA]
  exact TransitiveLift.le_pRank_of_card hA (k := 3) (by rw [hcard]; norm_num)

end CFSG.ComponentClassification.Sol76T13.R12.Pcls
