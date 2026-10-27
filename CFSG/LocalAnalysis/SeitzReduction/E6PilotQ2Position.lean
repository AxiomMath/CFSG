module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2PositionB
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAutDTwoHR7
public import CFSG.Assembly.RankThreeEvenDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms

theorem not_normal_map_oddCore_neighbour_E6_two {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : StandardSetting G L) {K : Type} [Field K] (hK : Nat.card K = 2)
    (e : L ≃* adjointGroup .E6 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((posJ K).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((a5Levi K).map e.symm.toMonoidHom).map L.subtype)
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : CharP K 2 := F4Pilot.charP_two_of_natCard_eq_two_pow (f := 1) (by rw [pow_one]; exact hK)
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hLt : L ≤ centralizer ({t} : Set G) := le_centralizer_of_mem_centralizer htC
  have hXL : X ≤ L := hXJ.trans (map_subtype_le _)
  have htX : t ∈ centralizer (X : Set G) := centralizer_le hXL htC
  obtain ⟨g, z, hzL, hgz, hz1, hzU⟩ := exists_conj_eq_mul_twoCentral_E6_two hset hK e ht hKt
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_le_centralizer_mulEquiv_of_conj_eq_mul_E6_two hset hK e
    htC ht hXodd hXJ hzL hz1 hzU hgz
  subst hDe
  have hDL : ((a5Levi K).map e.symm.toMonoidHom).map L.subtype ≤ L := map_subtype_le _
  have hyD : (e.symm (e6Rep K 0) : G) ∈ ((a5Levi K).map e.symm.toMonoidHom).map L.subtype :=
    ⟨e.symm (e6Rep K 0), ⟨e6Rep K 0, e6Rep_mem_a5Levi 0, rfl⟩, rfl⟩
  have hy1 : (e.symm (e6Rep K 0) : G) ≠ 1 := by
    intro h
    apply e6Rep_ne_one (K := K) 0
    have h' : e.symm (e6Rep K 0) = 1 := Subtype.ext h
    rw [← e.apply_symm_apply (e6Rep K 0), h', map_one]
  exact F4Pilot.not_normal_map_oddCore_centralizer_of_mulEquiv htX ht
    (map_a5Levi_le_centralizer e hXJ) (isQuasisimple_open_map_a5Levi e)
    (center_map_a5Levi_eq_bot e) (isSolvable_outer_map_a5Levi e) (hDL.trans hLt) hsyl hyD hy1
    (Or.inr rfl) hP ⟨eP.trans (a5LeviMapEquiv e)⟩

theorem not_normal_neighbour_E6_nonsplit_two {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : StandardSetting G L) {K : Type} [Field K] (hK : Nat.card K = 2)
    (e : L ≃* adjointGroup .E6 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {A : Subgroup (adjointGroup .E6 K)} (hAJ : A ≤ posJ K) (hA : Nat.card A = 3)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((a5Levi K).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hXL : X ≤ L := by
    rw [hX]
    exact map_subtype_le _
  have htX : t ∈ centralizer (X : Set G) := centralizer_le hXL htC
  have hXJ : X ≤ ((posJ K).map e.symm.toMonoidHom).map L.subtype := by
    rw [hX]
    exact map_mono (map_mono hAJ)
  have hXodd : Odd (Nat.card X) := by
    rw [hX, card_map_of_injective L.subtype_injective, card_map_of_injective e.symm.injective, hA]
    decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic A := isCyclic_of_prime_card hA
  have hA' : Nat.card A = Nat.card K + 1 := by rw [hA, hK]
  exact not_normal_map_oddCore_neighbour_E6_two hset hK e ht hKt hXodd hXJ hDe
    (neighbour_standard_E6_nonsplit_of_one_le hset.standard htC ht hKt le_rfl
      (by rw [pow_one]; exact hK) e hAJ hA' hcyc hX htX hDe).2.1

end CFSG.SeitzReduction.E6Pilot
