module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import CFSG.FeitThompson.Local.NilpotentDerivedNormalizerFactorization
import CFSG.FeitThompson.Local.CoprimeActionCyclicNoFixedPoint
import CFSG.FeitThompson.Foundations.NilpotentSylowNormalCharacteristic

open Subgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem not_dvd_natCard_commutator_of_normalizer_le_centralizer (P : Sylow p X)
    [IsCyclic ((P : Subgroup X))]
    (h : normalizer ((P : Subgroup X) : Set X) ≤ centralizer ((P : Subgroup X) : Set X)) :
    ¬ p ∣ Nat.card (commutator X) := by
  set φ := MonoidHom.transferSylow P h with hφ
  have hc : φ.ker.IsComplement' (P : Subgroup X) := MonoidHom.ker_transferSylow_isComplement' P h
  have hker : (P : Subgroup X).index = Nat.card φ.ker := hc.index_eq_card
  have hnd : ¬ p ∣ (P : Subgroup X).index := P.not_dvd_index
  have hle : commutator X ≤ φ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm' _ _
  exact fun hdvd => hnd (hker ▸ hdvd.trans (Subgroup.card_dvd_of_le hle))

theorem not_normalizer_le_centralizer (P : Sylow p X) [IsCyclic ((P : Subgroup X))]
    (hdvd : p ∣ Nat.card (commutator X)) :
    ¬ normalizer ((P : Subgroup X) : Set X) ≤ centralizer ((P : Subgroup X) : Set X) :=
  fun h => not_dvd_natCard_commutator_of_normalizer_le_centralizer P h hdvd

theorem cyclicSylow_le_commutator (P : Sylow p X) [IsCyclic ((P : Subgroup X))]
    (hdvd : p ∣ Nat.card (commutator X)) : (P : Subgroup X) ≤ commutator X :=
  P.normalizer_le_centralizer_or_le_commutator.resolve_left
    (not_normalizer_le_centralizer P hdvd)

theorem cyclicSylow_normal (hnil : Group.IsNilpotent (commutator X)) (P : Sylow p X)
    [IsCyclic ((P : Subgroup X))] (hdvd : p ∣ Nat.card (commutator X)) :
    (P : Subgroup X).Normal := by
  have := hnil
  have hPX : (P : Subgroup X) ≤ commutator X := cyclicSylow_le_commutator P hdvd
  have hcard : Nat.card ((P : Subgroup X).subgroupOf (commutator X))
      = p ^ (Nat.card (commutator X)).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPX).toEquiv,
      natCard_eq_pow_factorization_of_le Fact.out hPX P.card_eq_multiplicity]
  have hn : ((P : Subgroup X).subgroupOf (commutator X)).Normal :=
    normal_of_natCard_eq_pow_factorization hcard
  have hle : (P : Subgroup X).subgroupOf (commutator X) ≤ pCore p (commutator X) :=
    le_pCore Fact.out hn (IsPGroup.of_card hcard)
  have hmap : (P : Subgroup X) ≤ derivedPCore p X := by
    have h2 := Subgroup.map_mono (f := (commutator X).subtype) hle
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPX, ← derivedPCore_eq_map] at h2
  have heq : derivedPCore p X = (P : Subgroup X) :=
    le_antisymm (derivedPCore_le_of_natCard_eq Fact.out P.card_eq_multiplicity) hmap
  rw [← heq]
  infer_instance

theorem centralizer_eq_top_of_inf_center_ne_bot (P : Sylow p X) [IsCyclic ((P : Subgroup X))]
    [(P : Subgroup X).Normal] (hne : (P : Subgroup X) ⊓ center X ≠ ⊥) :
    centralizer ((P : Subgroup X) : Set X) = ⊤ := by
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨hyP, hyZ⟩ := Subgroup.mem_inf.1 y.2
  have hy1' : (y : X) ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hconj : ∀ (a z : X) (hz : z ∈ (P : Subgroup X)),
      ((MulAut.conjNormal (H := (P : Subgroup X)) a) ⟨z, hz⟩ : X) = a * z * a⁻¹ :=
    fun a z hz => MulAut.conjNormal_apply a ⟨z, hz⟩
  refine eq_top_of_forall_sylow_le fun q hq Q => ?_
  have : Fact q.Prime := ⟨hq⟩
  by_cases hqp : q = p
  ·
    subst hqp
    have := P.unique_of_normal ‹_›
    have hQP : Q = P := Subsingleton.elim _ _
    rw [hQP]
    exact le_centralizer _
  ·
    set φ : ((Q : Subgroup X)) →* MulAut ((P : Subgroup X)) :=
      (MulAut.conjNormal).comp (Q : Subgroup X).subtype with hφ
    have hfix : ∃ w : ((P : Subgroup X)), w ≠ 1 ∧ ∀ a : ((Q : Subgroup X)), φ a w = w := by
      refine ⟨⟨(y : X), hyP⟩, fun h => hy1' (congrArg Subtype.val h), fun a => Subtype.ext ?_⟩
      change ((MulAut.conjNormal (H := (P : Subgroup X)) (a : X)) ⟨(y : X), hyP⟩ : X) = (y : X)
      rw [hconj, Subgroup.mem_center_iff.1 hyZ (a : X)]
      group
    have h1 : φ = 1 :=
      eq_one_of_exists_ne_one_fixed (p := q) (q := p) hqp Q.isPGroup'
        (IsPGroup.of_card P.card_eq_multiplicity) φ hfix
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h2 := congrArg (fun f => (((f ⟨a, ha⟩) ⟨z, hz⟩ : ((P : Subgroup X))) : X)) h1
    simp only [hφ, MonoidHom.comp_apply, MonoidHom.one_apply] at h2
    rw [hconj] at h2
    simp only [MulAut.one_apply] at h2
    have h3 : a * z * a⁻¹ = z := h2
    calc z * a = (a * z * a⁻¹) * a := by rw [h3]
      _ = a * z := by group

theorem cyclicSylow_inf_center_eq_bot (hnil : Group.IsNilpotent (commutator X)) (P : Sylow p X)
    [IsCyclic ((P : Subgroup X))] (hdvd : p ∣ Nat.card (commutator X)) :
    (P : Subgroup X) ⊓ center X = ⊥ := by
  have := cyclicSylow_normal hnil P hdvd
  by_contra hne
  exact not_normalizer_le_centralizer P hdvd
    ((centralizer_eq_top_of_inf_center_ne_bot P hne) ▸ le_top)

theorem cyclicSylow_inf_centralizer_univ_eq_bot (hnil : Group.IsNilpotent (commutator X))
    (P : Sylow p X) [IsCyclic ((P : Subgroup X))] (hdvd : p ∣ Nat.card (commutator X)) :
    (P : Subgroup X) ⊓ centralizer (Set.univ : Set X) = ⊥ := by
  rw [centralizer_univ]
  exact cyclicSylow_inf_center_eq_bot hnil P hdvd

theorem eq_one_of_mem_cyclicSylow_of_forall_mul_comm (hnil : Group.IsNilpotent (commutator X))
    (P : Sylow p X) [IsCyclic ((P : Subgroup X))] (hdvd : p ∣ Nat.card (commutator X))
    {x : X} (hxP : x ∈ (P : Subgroup X)) (hx : ∀ z : X, x * z = z * x) : x = 1 := by
  have hmem : x ∈ (P : Subgroup X) ⊓ center X :=
    Subgroup.mem_inf.2 ⟨hxP, Subgroup.mem_center_iff.2 fun z => (hx z).symm⟩
  rw [cyclicSylow_inf_center_eq_bot hnil P hdvd] at hmem
  simpa using hmem

theorem cyclicSylow_le_commutator_and_normal_and_inf_center
    (hnil : Group.IsNilpotent (commutator X)) (P : Sylow p X) [IsCyclic ((P : Subgroup X))]
    (hdvd : p ∣ Nat.card (commutator X)) :
    (P : Subgroup X) ≤ commutator X ∧ (P : Subgroup X).Normal ∧
      (P : Subgroup X) ⊓ center X = ⊥ :=
  ⟨cyclicSylow_le_commutator P hdvd, cyclicSylow_normal hnil P hdvd,
    cyclicSylow_inf_center_eq_bot hnil P hdvd⟩

theorem natCard_eq_pow_factorization_conclusions (hnil : Group.IsNilpotent (commutator X))
    {P : Subgroup X} (hP : Nat.card P = p ^ (Nat.card X).factorization p) [IsCyclic P]
    (hdvd : p ∣ Nat.card (commutator X)) :
    P ≤ commutator X ∧ P.Normal ∧ P ⊓ center X = ⊥ := by
  obtain ⟨S, hS⟩ : ∃ S : Sylow p X, (S : Subgroup X) = P := ⟨Sylow.ofCard P hP, Sylow.coe_ofCard _ _⟩
  subst hS
  exact cyclicSylow_le_commutator_and_normal_and_inf_center hnil S hdvd

end

end CFSG.FeitThompson
