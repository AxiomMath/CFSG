module

public import CFSG.FeitThompson.Foundations.NilpotentNormalizerCondition
import CFSG.FeitThompson.Foundations.NilpotentSylowNormalCharacteristic
import CFSG.FeitThompson.Foundations.HallImageQuotient

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {L : Type*} [Group L] {q : ℕ}

theorem ker_mk'_comp_subtype_of_normal (H D : Subgroup L) [D.Normal] :
    ((QuotientGroup.mk' D).comp H.subtype).ker = D.subgroupOf H := by
  rw [ker_mk'_comp_subtype, inf_subgroupOf_right]

noncomputable def subgroupQuotientEquivMapMk' (H D : Subgroup L) [D.Normal] :
    H ⧸ D.subgroupOf H ≃* H.map (QuotientGroup.mk' D) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_mk'_comp_subtype_of_normal H D).symm).trans
    ((QuotientGroup.quotientKerEquivRange _).trans
      (MulEquiv.subgroupCongr (range_mk'_comp_subtype H D)))

@[simp]
theorem subgroupQuotientEquivMapMk'_mk (H D : Subgroup L) [D.Normal] (x : H) :
    (subgroupQuotientEquivMapMk' H D (QuotientGroup.mk x) : L ⧸ D) = QuotientGroup.mk (x : L) :=
  (rfl)

theorem map_commutator_mk' (D : Subgroup L) [D.Normal] :
    (commutator L).map (QuotientGroup.mk' D) = commutator (L ⧸ D) := by
  rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective D),
    _root_.commutator_def]

theorem exists_normal_isPGroup_forall_le [Finite L] [Fact q.Prime] (C : Subgroup L) [C.Normal]
    [Group.IsNilpotent C] :
    ∃ T ≤ C, T.Normal ∧ IsPGroup q T ∧ ∀ P ≤ C, IsPGroup q P → P ≤ T := by
  obtain ⟨T⟩ : Nonempty (Sylow q C) := inferInstance
  have hTn : (T : Subgroup C).Normal := sylow_normal_of_isNilpotent T
  have : (T : Subgroup C).Characteristic := sylow_characteristic_of_isNilpotent T
  have : Unique (Sylow q C) := T.unique_of_normal hTn
  refine ⟨(T : Subgroup C).map C.subtype, map_subtype_le _,
    ConjAct.normal_of_characteristic_of_normal, T.isPGroup'.map _, ?_⟩
  intro P hPC hP
  obtain ⟨S, hS⟩ := (hP.comap_subtype (K := C)).exists_le_sylow
  have hST : S = T := Subsingleton.elim _ _
  calc P = map C.subtype (P.subgroupOf C) := (map_subgroupOf_eq_of_le hPC).symm
    _ ≤ map C.subtype (S : Subgroup C) := map_mono hS
    _ = map C.subtype (T : Subgroup C) := by rw [hST]

theorem commutator_le_of_isNilpotent_commutator_quotient [Finite L] [Fact q.Prime]
    {D : Subgroup L} [D.Normal] (_hD : D ≤ commutator L)
    (hnil : Group.IsNilpotent (commutator L ⧸ D.subgroupOf (commutator L)))
    {Q V : Subgroup L} (hQ : Q ≤ commutator L) (hQp : IsPGroup q Q)
    (hV : (Nat.card V).Coprime q) (hnorm : Q ≤ normalizer (V : Set L)) :
    ⁅V, Q⁆ ≤ D := by
  set f := QuotientGroup.mk' D with hf
  have hsurj : Function.Surjective f := QuotientGroup.mk'_surjective D
  set C := (commutator L).map f with hC
  have hCn : C.Normal := (inferInstance : (commutator L).Normal).map _ hsurj
  have hCnil : Group.IsNilpotent C :=
    Group.nilpotent_of_mulEquiv (subgroupQuotientEquivMapMk' (commutator L) D)
  obtain ⟨T, -, hTn, hTp, hTmax⟩ := exists_normal_isPGroup_forall_le (q := q) C
  have hfQ : Q.map f ≤ T := hTmax _ (map_mono hQ) (hQp.map f)
  have h1 : ⁅V.map f, Q.map f⁆ ≤ T :=
    le_trans (commutator_mono le_rfl hfQ) (commutator_le_right _ _)
  have h2 : ⁅V.map f, Q.map f⁆ ≤ V.map f := by
    rw [← Subgroup.map_commutator]
    exact map_mono (le_normalizer_iff_commutator_le_left.mp hnorm)
  have hqV : ¬ q ∣ Nat.card V := fun h =>
    (Fact.out : q.Prime).one_lt.ne' (Nat.eq_one_of_dvd_coprimes hV.symm dvd_rfl h)
  have hbot : ⁅V.map f, Q.map f⁆ = ⊥ := by
    rcases (hTp.to_le h1).card_eq_or_dvd with h | h
    · exact card_eq_one.mp h
    · exact absurd (h.trans ((card_dvd_of_le h2).trans (V.card_map_dvd f))) hqV
  rw [← Subgroup.map_commutator] at hbot
  rw [← QuotientGroup.ker_mk' D]
  exact (Subgroup.map_eq_bot_iff _).mp hbot

theorem commutator_le_of_isNilpotent_commutator_quotientGroup [Finite L] [Fact q.Prime]
    {D : Subgroup L} [D.Normal] (hD : D ≤ commutator L)
    (hnil : Group.IsNilpotent (commutator (L ⧸ D)))
    {Q V : Subgroup L} (hQ : Q ≤ commutator L) (hQp : IsPGroup q Q)
    (hV : (Nat.card V).Coprime q) (hnorm : Q ≤ normalizer (V : Set L)) :
    ⁅V, Q⁆ ≤ D := by
  refine commutator_le_of_isNilpotent_commutator_quotient hD ?_ hQ hQp hV hnorm
  rw [← map_commutator_mk' D] at hnil
  exact Group.nilpotent_of_mulEquiv (subgroupQuotientEquivMapMk' (commutator L) D).symm

theorem IsCentralSeries.commutator_le_of_isPGroup [Finite L] [Fact q.Prime]
    {D : Subgroup L} [D.Normal] (hD : D ≤ commutator L)
    {X : ℕ → Subgroup (commutator L ⧸ D.subgroupOf (commutator L))} {r : ℕ}
    (hX : IsCentralSeries X r)
    {Q V : Subgroup L} (hQ : Q ≤ commutator L) (hQp : IsPGroup q Q)
    (hV : (Nat.card V).Coprime q) (hnorm : Q ≤ normalizer (V : Set L)) :
    ⁅V, Q⁆ ≤ D :=
  commutator_le_of_isNilpotent_commutator_quotient hD hX.isNilpotent hQ hQp hV hnorm

end
end CFSG.FeitThompson
