module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1DegreeSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1Fusion

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

theorem card_isConj_mul_card_centralizer_eq {G : Type*} [Group G] [Finite G] (x : G) :
    Nat.card {y : G // IsConj x y} * Nat.card (Subgroup.centralizer {x}) = Nat.card G := by
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer, mul_comm]
  have h1 := (MulAction.stabilizer (ConjAct G) x).card_mul_index
  rw [MulAction.index_stabilizer] at h1
  have h2 : Nat.card {y : G // IsConj x y} = (MulAction.orbit (ConjAct G) x).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun y => by
      rw [isConj_comm]
      exact ConjAct.mem_orbit_conjAct.symm)
  rw [h2]
  exact h1

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

variable (htype : ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
  s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
    CaseC3.Genuine (Subgroup.center J) s)
include htype

theorem genuine_iff_isConj_forty (s : J ⧸ Subgroup.center J) :
    CaseC3.Genuine (Subgroup.center J) s ∧ s ≠ 1 ↔
      IsConj (caseC3Word (Subgroup.center J) u m y x 40) s := by
  refine ⟨fun hs => (d.isConj_forty_iff htype (CaseC3.mul_self_of_genuine hs.1) hs.2).mpr hs.1,
    fun hc => ?_⟩
  obtain ⟨c, hc'⟩ := isConj_iff.mp hc
  have hgen := CaseC3.genuine_conj _ d.caseC3BCD.genuine_forty c⁻¹
  rw [inv_inv, hc'] at hgen
  refine ⟨hgen, fun h1 => ?_⟩
  rw [← hc', conj_eq_one_iff, d.caseC3BCD.caseC3Word_eq_one_iff] at h1
  exact absurd h1 (by decide)

theorem card_genuine_eq
    (h192 : Nat.card (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}) = 192)
    (hord : Nat.card (J ⧸ Subgroup.center J) = 181440) :
    Nat.card {s : J ⧸ Subgroup.center J // CaseC3.Genuine (Subgroup.center J) s ∧ s ≠ 1} =
      945 := by
  have hconj := card_isConj_mul_card_centralizer_eq (caseC3Word (Subgroup.center J) u m y x 40)
  rw [h192, hord] at hconj
  rw [Nat.card_congr (Equiv.subtypeEquivRight (d.genuine_iff_isConj_forty htype))]
  omega

theorem index_eq_nine
    (h192 : Nat.card (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}) = 192)
    (hord : Nat.card (J ⧸ Subgroup.center J) = 181440) :
    (B.map (QuotientGroup.mk' (Subgroup.center J))).index = 9 := by
  have hcount := d.setting.card_genuine_eq_index_mul
  rw [d.card_genuine_eq htype h192 hord] at hcount
  have h17 := d.seventeen_le_card_genuine_mem htype
  have hmod : (B.map (QuotientGroup.mk' (Subgroup.center J))).index % 8 = 1 := d.index_modEq_one
  have hne : (B.map (QuotientGroup.mk' (Subgroup.center J))).index ≠ 1 := fun h1 =>
    d.setting.map_ne_top (Subgroup.index_eq_one.mp h1)
  refine eq_nine_of_dvd_nine_hundred_forty_five (Dvd.intro _ hcount.symm) hmod ?_ ?_
  · by_contra hlt
    push Not at hlt
    have := Nat.mul_le_mul hlt h17
    omega
  · omega

theorem nonempty_mulEquiv_alternating_of_card
    (h192 : Nat.card (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}) = 192)
    (hord : Nat.card (J ⧸ Subgroup.center J) = 181440) :
    Nonempty ((J ⧸ Subgroup.center J) ≃* alternatingGroup (Fin 9)) :=
  nonempty_mulEquiv_alternatingGroup_nine_of_index d.setting.simple
    (d.index_eq_nine htype h192 hord) hord

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
