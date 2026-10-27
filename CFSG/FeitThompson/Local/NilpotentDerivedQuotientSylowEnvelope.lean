module

public import Mathlib.GroupTheory.Nilpotent
import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
import CFSG.FeitThompson.Foundations.HallImageQuotient
import CFSG.FeitThompson.Foundations.NilpotentSylowNormalCharacteristic
import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise Subgroup

variable {X : Type*} [Group X] {p : ℕ}

theorem map_mk'_commutator (D : Subgroup X) [D.Normal] :
    (commutator X).map (QuotientGroup.mk' D) = commutator (X ⧸ D) := by
  rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective D),
    commutator_def]

noncomputable def commutatorQuotientEquiv (D : Subgroup X) [D.Normal] (hD : D ≤ commutator X) :
    (↥(commutator X) ⧸ D.subgroupOf (commutator X)) ≃* ↥(commutator (X ⧸ D)) :=
  (QuotientGroup.quotientMulEquivOfEq (M := D.subgroupOf (commutator X))
      (by rw [inf_eq_left.mpr hD])).trans
    ((quotientInfEquivMapMk' (commutator X) D).trans
      (MulEquiv.subgroupCongr (map_mk'_commutator D)))

theorem isNilpotent_commutator_quotient_iff (D : Subgroup X) [D.Normal] (hD : D ≤ commutator X) :
    Group.IsNilpotent (↥(commutator X) ⧸ D.subgroupOf (commutator X)) ↔
      Group.IsNilpotent ↥(commutator (X ⧸ D)) :=
  Group.isNilpotent_congr (commutatorQuotientEquiv D hD)

variable [Finite X] [Fact p.Prime]

theorem normal_sup_sylow (D : Subgroup X) [D.Normal] (hD : D ≤ commutator X)
    (hnil : Group.IsNilpotent (↥(commutator X) ⧸ D.subgroupOf (commutator X)))
    (S : Sylow p X) (hS : (S : Subgroup X) ≤ commutator X) :
    (D ⊔ (S : Subgroup X)).Normal := by
  have : Group.IsNilpotent ↥(commutator (X ⧸ D)) :=
    (isNilpotent_commutator_quotient_iff D hD).mp hnil
  set T : Sylow p (X ⧸ D) := S.mapSurjective (QuotientGroup.mk'_surjective D) with hTdef
  have hTcoe : (T : Subgroup (X ⧸ D)) = (S : Subgroup X).map (QuotientGroup.mk' D) :=
    Sylow.coe_mapSurjective _ _
  have hle : (T : Subgroup (X ⧸ D)) ≤ commutator (X ⧸ D) := by
    rw [hTcoe, ← map_mk'_commutator D]
    exact Subgroup.map_mono hS
  have hchar : ((T : Subgroup (X ⧸ D)).subgroupOf (commutator (X ⧸ D))).Characteristic := by
    have h := sylow_characteristic_of_isNilpotent (T.subtype hle)
    rwa [Sylow.coe_subtype] at h
  have hn : ((S : Subgroup X).map (QuotientGroup.mk' D)).Normal := by
    rw [← hTcoe]
    have : (T : Subgroup (X ⧸ D)).Characteristic :=
      characteristic_of_characteristic_subgroupOf_of_characteristic hle
    infer_instance
  have h2 := hn.comap (QuotientGroup.mk' D)
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
  rwa [sup_comm] at h2

theorem isPGroup_le_of_normal_sup {D S : Subgroup X}
    (hDS : (D ⊔ S).Normal) (hScard : Nat.card S = p ^ (Nat.card X).factorization p)
    {T : Subgroup X} (hT : IsPGroup p T) : T ≤ D ⊔ S := by
  obtain ⟨g, hg⟩ := exists_le_conj_smul_of_isPGroup hScard hT
  refine hg.trans ((Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr
    (le_sup_right : S ≤ D ⊔ S)).trans ?_)
  exact (hDS.conj_smul_eq_self g _).le

theorem le_sup_sylow_of_isPGroup (D : Subgroup X) [D.Normal] (hD : D ≤ commutator X)
    (hnil : Group.IsNilpotent (↥(commutator X) ⧸ D.subgroupOf (commutator X)))
    (S : Sylow p X) (hS : (S : Subgroup X) ≤ commutator X)
    {T : Subgroup X} (hT : IsPGroup p T) : T ≤ D ⊔ (S : Subgroup X) :=
  isPGroup_le_of_normal_sup (normal_sup_sylow D hD hnil S hS) S.card_eq_multiplicity hT

theorem prime_dvd_natCard_sup_sylow (D : Subgroup X) [D.Normal] (S : Sylow p X)
    {q : ℕ} (hq : q.Prime) (hdvd : q ∣ Nat.card (D ⊔ (S : Subgroup X) : Subgroup X)) :
    q ∣ Nat.card D ∨ q = p := by
  rcases (Nat.Prime.dvd_mul hq).mp (hdvd.trans (natCard_sup_dvd D (S : Subgroup X))) with h | h
  · exact Or.inl h
  · obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    rw [hn] at h
    exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp (hq.dvd_of_dvd_pow h))

end
end CFSG.FeitThompson

