module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTheorem1
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.ResidualOddLie
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem oddLieType_of_lieModel_of_ne_two {G : Type} [Group G]
    {τ : Assembly.LowTwoRank.StatedLieTag} {n p k : ℕ} (h : LieModel G τ n p k) (hp : p.Prime)
    (hp2 : p ≠ 2) : OddLieType G :=
  ⟨τ, n, p, k, hp, hp2, CFSG.Blueprint.LieModel.admissible h, h⟩

theorem exists_intrinsic_twoComponent {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : standardComponentIsStandard L) (hev : Even (Nat.card (center L))) :
    ∃ z : G, orderOf z = 2 ∧ z ∈ L ∧ L ≤ centralizer ({z} : Set G) ∧
      ComponentClassification.HarrisLit.IsTwoComponentIn L (centralizer {z}) := by
  obtain ⟨z, hz⟩ : ∃ z : center L, orderOf z = 2 :=
    exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hev)
  set t : G := ((z : L) : G) with ht
  have ht2 : orderOf t = 2 := by
    rw [ht, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have htC : t ∈ centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hc := Subgroup.mem_center_iff.1 z.2 ⟨h, hh⟩
    exact congrArg Subtype.val hc
  have hev2 : 2 ∣ Nat.card L :=
    (even_iff_two_dvd.1 hev).trans (Subgroup.card_subgroup_dvd_card (center L))
  obtain ⟨hLT, hcomp⟩ := isPComponent_two_of_standard hL htC ht2 hev2
  exact ⟨t, ht2, (z : L).2, hLT,
    (ComponentClassification.HarrisLit.isTwoComponentIn_iff hLT).2 hcomp⟩

@[expose] def OddLieThm187bResidual : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    ((∃ z : G, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set G)) ≠ ⊥) →
      ComponentClassification.OutcomeLocal.UOutcome G) →
    OddLieType (L ⧸ center L) →
    ¬ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 5)) →
    ¬ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 6)) →
    ¬ HarrisSolomonFritzScope L →
    (Odd (Nat.card (center L)) ∨
      ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ ComponentClassification.HarrisLit.IsMTypeSchur p L) →
    ∀ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))) →
      AltOutcome G ∨ OddLieType G ∨
        (IsSporadic G .M12 ∨ IsSporadic G .J1 ∨ IsSporadic G .J2 ∨ IsSporadic G .HS)

end CFSG.OddStandard
