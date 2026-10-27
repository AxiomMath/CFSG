module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionB
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionFusion

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms

theorem exists_conj_eq_mul_twoCentral_E8_of_one_le {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : StandardSetting G L) {K : Type} [Field K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ g : G, ∃ z ∈ L, g⁻¹ * t * g = t * z ∧ z ≠ 1 ∧
      ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  rcases Nat.lt_or_ge f 2 with h | h
  · obtain rfl : f = 1 := by omega
    exact exists_conj_eq_mul_twoCentral_E8_two hset (by simpa using hK) e ht hKt
  · exact exists_conj_eq_mul_twoCentral_E8_of_two_le hset h hK e ht hKt

theorem not_normal_map_oddCore_neighbour_E8_of_one_le {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((posJE8 K).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype)
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hLt : L ≤ centralizer ({t} : Set G) := le_centralizer_of_mem_centralizer htC
  have hXL : X ≤ L := hXJ.trans (map_subtype_le _)
  have htX : t ∈ centralizer (X : Set G) := centralizer_le hXL htC
  obtain ⟨g, z, hzL, hgz, hz1, hzU⟩ := exists_conj_eq_mul_twoCentral_E8_of_one_le hset hf hK e ht hKt
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_le_centralizer_mulEquiv_of_conj_eq_mul_E8_of_one_le hset hf hK e
    htC ht hXodd hXJ hzL hz1 hzU hgz
  subst hDe
  set eD := e7LeviMapEquivE8 (G := G) e with heD
  have hDL : ((e7Levi K).map e.symm.toMonoidHom).map L.subtype ≤ L := map_subtype_le _
  have hyD : (e.symm (repXE8 K) : G) ∈ ((e7Levi K).map e.symm.toMonoidHom).map L.subtype :=
    ⟨e.symm (repXE8 K), ⟨repXE8 K, repXE8_mem_e7Levi, rfl⟩, rfl⟩
  have hy1 : (e.symm (repXE8 K) : G) ≠ 1 := by
    intro h
    apply repXE8_ne_one (K := K)
    have h' : e.symm (repXE8 K) = 1 := Subtype.ext h
    rw [← e.apply_symm_apply (repXE8 K), h', map_one]
  have hDX : ((e7Levi K).map e.symm.toMonoidHom).map L.subtype ≤ centralizer (X : Set G) :=
    (F4Pilot.map_le_centralizer_map L.subtype
      (F4Pilot.map_le_centralizer_map e.symm.toMonoidHom
        e7Levi_le_centralizer_posJE8_of_finite)).trans (centralizer_le hXJ)
  exact F4Pilot.not_normal_map_oddCore_centralizer_of_mulEquiv htX ht hDX
    (F4Pilot.isQuasisimple_open_of_mulEquiv eD isQuasisimple_open_e7Levi)
    (F4Pilot.center_eq_bot_congr eD center_e7Levi_eq_bot)
    ⟨⟨2, derivedSeries_outer_eq_bot_of_mulEquiv (eD.symm.trans (e7LeviEquiv K))
      (exceptional_E_pinned_model_Schreier K).2.1⟩⟩
    (hDL.trans hLt) hsyl hyD hy1 (Or.inr rfl) hP ⟨eP.trans eD⟩

theorem not_normal_neighbour_E8_nonsplit_of_one_le {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {A : Subgroup (adjointGroup .E8 K)} (hAJ : A ≤ posJE8 K) (hA : Nat.card A = Nat.card K + 1)
    (hcyc : IsCyclic A) {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hXL : X ≤ L := by
    rw [hX]
    exact map_subtype_le _
  have htX : t ∈ centralizer (X : Set G) := centralizer_le hXL htC
  have hXJ : X ≤ ((posJE8 K).map e.symm.toMonoidHom).map L.subtype := by
    rw [hX]
    exact map_mono (map_mono hAJ)
  have hXodd : Odd (Nat.card X) := by
    rw [hX, card_map_of_injective L.subtype_injective, card_map_of_injective e.symm.injective,
      hA, hK]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  exact not_normal_map_oddCore_neighbour_E8_of_one_le hset hf hK e ht hKt hXodd hXJ hDe
    (neighbour_standard_E8_nonsplit hset.standard htC ht hKt hK e hAJ hA hcyc hX htX hDe).2.1

theorem not_normal_neighbour_E8_nonsplit_two {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : StandardSetting G L) {K : Type} [Field K] (hK : Nat.card K = 2)
    (e : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {A : Subgroup (adjointGroup .E8 K)} (hAJ : A ≤ posJE8 K) (hA : Nat.card A = Nat.card K + 1)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have hA3 : Nat.card A = 3 := by rw [hA, hK]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact not_normal_neighbour_E8_nonsplit_of_one_le hset le_rfl (by rw [pow_one]; exact hK) e ht
    hKt hAJ hA (isCyclic_of_prime_card hA3) hX hDe

theorem exists_nonsplit_le_posJE8 {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∃ A : Subgroup (adjointGroup .E8 K), A ≤ posJE8 K ∧ IsCyclic A ∧
      Nat.card A = Nat.card K + 1 :=
  E6Pilot.exists_nonsplit_le_subgroupOf_highRootSL2 (τ := .E8) (K := K)

end CFSG.SeitzReduction.E8Pilot
