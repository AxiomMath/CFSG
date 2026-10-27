module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Local.PLengthOneSubgroupInheritance
public import CFSG.FeitThompson.Local.OddAutomorphismMaximalPlaneDerivedPrimePower
public import CFSG.FeitThompson.Local.PLengthOneSylowNormalizerDerivedTransfer
public import CFSG.FeitThompson.Definitions.NarrowPGroupsAndBetaPrimes
import CFSG.FeitThompson.Local.PiCoreQuotientPiCore
import CFSG.FeitThompson.Local.NilpotentDerivedQuotientSylowEnvelope
import CFSG.FeitThompson.Local.PCoreSelfCentralizingNoNormalComplement
import CFSG.FeitThompson.Local.ExponentPrimeRankTwoOrderCube

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {p : ℕ} {X : Type*} [Group X]

theorem maximal_congr {α : Type*} [LE α] {q r : α → Prop} (h : ∀ a, q a ↔ r a) {a : α} :
    Maximal q a ↔ Maximal r a :=
  ⟨fun ha => ⟨(h _).1 ha.1, fun _ hb hab => ha.2 ((h _).2 hb) hab⟩,
    fun ha => ⟨(h _).2 ha.1, fun _ hb hab => ha.2 ((h _).1 hb) hab⟩⟩

theorem isElementaryAbelian_iff_isElementaryAbelianSubgroup {A : Subgroup X} :
    IsElementaryAbelian p A ↔ IsElementaryAbelianSubgroup p A := by
  rw [isElementaryAbelian_iff, isElementaryAbelianSubgroup_iff]

theorem maximal_isElementaryAbelian_map {Y : Type*} [Group Y] (e : X ≃* Y) {A : Subgroup X}
    (h : Maximal (IsElementaryAbelian p) A) :
    Maximal (IsElementaryAbelian p) (A.map e.toMonoidHom) :=
  (maximal_congr fun _ => isElementaryAbelian_iff_isElementaryAbelianSubgroup).2
    (maximal_isElementaryAbelianSubgroup_map e
      ((maximal_congr fun _ => isElementaryAbelian_iff_isElementaryAbelianSubgroup).1 h))

theorem index_inf_subgroupOf_commutator (N : Subgroup X) [N.Normal] :
    ((N ⊓ commutator X).subgroupOf (commutator X)).index = Nat.card ↥(commutator (X ⧸ N)) := by
  have h := Subgroup.relIndex_ker (commutator X) (QuotientGroup.mk' N)
  rw [QuotientGroup.ker_mk', map_mk'_commutator] at h
  rw [Subgroup.inf_subgroupOf_right]
  exact h

theorem isPGroup_of_isPGroup_map {Y : Type*} [Group Y] [Finite X] [Finite Y] (hp : p.Prime)
    {f : X →* Y} {K : Subgroup X} (hmap : IsPGroup p (K.map f))
    (hker : IsPGroup p ↥(f.ker ⊓ K)) : IsPGroup p K := by
  have := Fact.mk hp
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hmap
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hker
  refine IsPGroup.of_card (n := a + b) ?_
  have h1 := Subgroup.card_mul_index (f.ker.subgroupOf K)
  have h2 : (f.ker.subgroupOf K).index = Nat.card (K.map f) := Subgroup.relIndex_ker K f
  have h3 : Nat.card ↥(f.ker.subgroupOf K) = Nat.card ↥(f.ker ⊓ K) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [h3, h2, hb, ha] at h1
  rw [← h1, pow_add, mul_comm]

variable [Finite X] {P : Subgroup X}

theorem pCore_quotient_eq_map_mk' [Fact p.Prime]
    (hP : Nat.card P = p ^ (Nat.card X).factorization p)
    (hV : ¬ p ∣ (pComplPCore p X).index) :
    pCore p (X ⧸ pComplCore p X) = P.map (QuotientGroup.mk' (pComplCore p X)) := by
  have hD : (pComplCore p X).map (QuotientGroup.mk' (pComplCore p X)) = ⊥ :=
    Subgroup.map_eq_bot_iff _ |>.2 (QuotientGroup.ker_mk' _).ge
  rw [← map_mk'_pComplPCore, pComplPCore_eq_pComplCore_sup hP hV, Subgroup.map_sup, hD,
    bot_sup_eq]

noncomputable def sylowMulEquivPCoreQuotient [Fact p.Prime]
    (hP : Nat.card P = p ^ (Nat.card X).factorization p)
    (hV : ¬ p ∣ (pComplPCore p X).index) :
    ↥P ≃* ↥(pCore p (X ⧸ pComplCore p X)) := by
  set f : ↥P →* (X ⧸ pComplCore p X) :=
    (QuotientGroup.mk' (pComplCore p X)).comp P.subtype with hf
  have hker : f.ker = ⊥ := by
    rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.comap_subtype,
      Subgroup.subgroupOf_eq_bot]
    exact disjoint_iff.2 (inf_pComplCore_eq_bot (IsPGroup.of_card hP))
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).1 hker
  have hrange : f.range = pCore p (X ⧸ pComplCore p X) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype, pCore_quotient_eq_map_mk' hP hV]
  exact (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)

theorem isPGroup_commutator_quotient_pComplCore [Group.IsSolvable X] (hp : p.Prime)
    (hoddX : Odd (Nat.card X)) (hpX : p ∣ Nat.card X)
    (hP : Nat.card P = p ^ (Nat.card X).factorization p)
    (hV : ¬ p ∣ (pComplPCore p X).index)
    (halt : IsCyclic ↥P ∨
      ∃ A : Subgroup ↥P, Maximal (IsElementaryAbelian p) A ∧ Nat.card A = p ^ 2) :
    IsPGroup p ↥(commutator (X ⧸ pComplCore p X)) := by
  have := Fact.mk hp
  set Y := X ⧸ pComplCore p X with hY
  set R := pCore p Y with hR
  have hbot : pComplCore p Y = ⊥ := pComplCore_quotient_pComplCore p X
  have e : ↥P ≃* ↥R := sylowMulEquivPCoreQuotient hP hV
  have haltR : IsCyclic ↥R ∨
      ∃ A : Subgroup ↥R, Maximal (IsElementaryAbelian p) A ∧ Nat.card A = p ^ 2 := by
    rcases halt with hcyc | ⟨A, hA, hAcard⟩
    · exact Or.inl ((MulEquiv.isCyclic e).1 hcyc)
    · refine Or.inr ⟨A.map e.toMonoidHom, maximal_isElementaryAbelian_map e hA, ?_⟩
      rw [Subgroup.card_map_of_injective e.injective, hAcard]
  set φ : Y →* MulAut ↥R := MulAut.conjNormal with hφ
  have hoddY : Odd (Nat.card Y) := hoddX.of_dvd_nat (Subgroup.card_quotient_dvd_card _)
  have hoddB : Odd (Nat.card ↥φ.range) := hoddY.of_dvd_nat (Subgroup.card_range_dvd φ)
  have hoddp : Odd p := hoddX.of_dvd_nat hpX
  have hmap : IsPGroup p ↥((commutator Y).map φ) := by
    have h := isPGroup_commutator_subgroup_of_odd_aut_of_isCyclic_or_maximal_plane hp hoddp
      (isPGroup_pCore hp Y) haltR (B := φ.range) hoddB
    rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map]
  have hker : IsPGroup p ↥(φ.ker ⊓ commutator Y) := by
    refine (isPGroup_pCore hp Y).to_le (le_trans inf_le_left ?_)
    rw [hφ, ker_conjNormal]
    exact centralizer_pCore_le_pCore hp hbot
  exact isPGroup_of_isPGroup_map hp hmap hker

theorem isNormalPComplement_inf_commutator [Group.IsSolvable X] (hp : p.Prime)
    (hoddX : Odd (Nat.card X)) (hpX : p ∣ Nat.card X)
    (hP : Nat.card P = p ^ (Nat.card X).factorization p)
    (hV : ¬ p ∣ (pComplPCore p X).index)
    (halt : IsCyclic ↥P ∨
      ∃ A : Subgroup ↥P, Maximal (IsElementaryAbelian p) A ∧ Nat.card A = p ^ 2) :
    IsNormalPComplement p ((pComplCore p X ⊓ commutator X).subgroupOf (commutator X)) := by
  have := Fact.mk hp
  have hDnorm : (pComplCore p X ⊓ commutator X).Normal := Subgroup.normal_inf_normal _ _
  refine isNormalPComplement_of (hDnorm.subgroupOf _) ?_ ?_
  ·
    have hcard : Nat.card ↥((pComplCore p X ⊓ commutator X).subgroupOf (commutator X))
        = Nat.card ↥(pComplCore p X ⊓ commutator X) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [hcard]
    exact fun hdvd => not_dvd_natCard_pComplCore hp X
      (hdvd.trans (Subgroup.card_dvd_of_le inf_le_left))
  ·
    rw [index_inf_subgroupOf_commutator]
    exact IsPGroup.iff_card.1
      (isPGroup_commutator_quotient_pComplCore hp hoddX hpX hP hV halt)

theorem isNormalPComplement_inf_commutator' [Group.IsSolvable X] (hp : p.Prime)
    (hoddX : Odd (Nat.card X)) (hpX : p ∣ Nat.card X)
    (hP : Nat.card P = p ^ (Nat.card X).factorization p)
    (hV : ¬ p ∣ (pComplPCore p X).index)
    (halt : IsCyclic ↥P ∨
      ∃ A : Subgroup ↥P, Maximal (IsElementaryAbelian p) A ∧ Nat.card A = p ^ 2) :
    ((pComplCore p X ⊓ commutator X).subgroupOf (commutator X)).Normal ∧
      ¬ p ∣ Nat.card ↥((pComplCore p X ⊓ commutator X).subgroupOf (commutator X)) ∧
      ∃ n : ℕ, ((pComplCore p X ⊓ commutator X).subgroupOf (commutator X)).index = p ^ n :=
  isNormalPComplement_iff.1 (isNormalPComplement_inf_commutator hp hoddX hpX hP hV halt)

end

end CFSG.FeitThompson
