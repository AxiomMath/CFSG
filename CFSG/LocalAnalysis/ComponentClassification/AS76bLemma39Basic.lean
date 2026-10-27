module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.ComponentClassification.AS76b

namespace Lemma39

open Subgroup
open scoped commutatorElement

@[expose] def SolvAbSylow (Q : Type*) [Group Q] : Prop :=
  Group.IsSolvable Q ∧ ∀ S : Sylow 2 Q, IsMulCommutative (S : Subgroup Q)

section General

variable {Q Q' : Type*} [Group Q] [Group Q']

theorem isMulCommutative_of_injective (f : Q →* Q') (hf : Function.Injective f)
    {P : Subgroup Q} {P' : Subgroup Q'} (hPP' : P.map f ≤ P') (hc : IsMulCommutative P') :
    IsMulCommutative P := by
  refine ⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩
  have ha : f a ∈ P' := hPP' ⟨a, a.2, rfl⟩
  have hb : f b ∈ P' := hPP' ⟨b, b.2, rfl⟩
  have h := congrArg Subtype.val (hc.is_comm.comm ⟨f a, ha⟩ ⟨f b, hb⟩)
  simpa using h

theorem absSylow_of_injective [Finite Q'] (f : Q →* Q') (hf : Function.Injective f)
    (h : ∀ S : Sylow 2 Q', IsMulCommutative (S : Subgroup Q')) :
    ∀ S : Sylow 2 Q, IsMulCommutative (S : Subgroup Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S
  obtain ⟨S', hS'⟩ := (S.isPGroup'.map f).exists_le_sylow
  exact isMulCommutative_of_injective f hf hS' (h S')

theorem absSylow_of_surjective [Finite Q] (f : Q →* Q') (hf : Function.Surjective f)
    (h : ∀ S : Sylow 2 Q, IsMulCommutative (S : Subgroup Q)) :
    ∀ S : Sylow 2 Q', IsMulCommutative (S : Subgroup Q') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S
  obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective hf 2 S
  have hc := h P
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨_, x, hx, rfl⟩ := a
  obtain ⟨_, y, hy, rfl⟩ := b
  apply Subtype.ext
  change f x * f y = f y * f x
  rw [← map_mul, ← map_mul]
  exact congrArg f (congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))

theorem SolvAbSylow.of_injective [Finite Q'] (f : Q →* Q') (hf : Function.Injective f)
    (h : SolvAbSylow Q') : SolvAbSylow Q := by
  have := h.1
  exact ⟨Group.isSolvable_of_isSolvable_injective hf, absSylow_of_injective f hf h.2⟩

theorem SolvAbSylow.of_surjective [Finite Q] (f : Q →* Q') (hf : Function.Surjective f)
    (h : SolvAbSylow Q) : SolvAbSylow Q' := by
  have := h.1
  exact ⟨Group.isSolvable_of_surjective hf, absSylow_of_surjective f hf h.2⟩

theorem SolvAbSylow.of_mulEquiv [Finite Q'] (e : Q ≃* Q') (h : SolvAbSylow Q') : SolvAbSylow Q :=
  SolvAbSylow.of_injective e.toMonoidHom e.injective h

theorem eq_bot_of_isPGroup_of_le [Finite Q'] {P H : Subgroup Q'} (hP : IsPGroup 2 P)
    (hH : Odd (Nat.card H)) (hPH : P ≤ H) : P = ⊥ :=
  AschbacherTightEmbedding.two_subgroup_of_odd_eq_bot P H hP hH hPH

theorem SolvAbSylow.of_ker [Finite Q] [Finite Q'] (f : Q →* Q') (hker : SolvAbSylow f.ker)
    (hodd : Odd (Nat.card f.range)) : SolvAbSylow Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, fun S => ?_⟩
  · have := hker.1
    have : Group.IsSolvable f.range := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    exact Group.isSolvable_of_ker_le_range f.ker.subtype f.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict, range_subtype])
  · have hSk : (S : Subgroup Q) ≤ f.ker := by
      have hbot := eq_bot_of_isPGroup_of_le (S.isPGroup'.map f) hodd (map_le_range f _)
      rwa [Subgroup.map_eq_bot_iff] at hbot
    obtain ⟨S', hS'⟩ :=
      (S.isPGroup'.comap_subtype : IsPGroup 2 ((S : Subgroup Q).subgroupOf f.ker)).exists_le_sylow
    have hc := hker.2 S'
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have ha : (⟨a, hSk a.2⟩ : f.ker) ∈ (S' : Subgroup f.ker) := hS' a.2
    have hb : (⟨b, hSk b.2⟩ : f.ker) ∈ (S' : Subgroup f.ker) := hS' b.2
    have h := congrArg (fun z : (S' : Subgroup f.ker) => ((z : f.ker) : Q))
      (hc.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
    simpa using h

theorem SolvAbSylow.of_le [Finite Q] {Z S K : Subgroup Q} (hZS : Z ≤ S)
    (hS : Group.IsSolvable S) (hZK : Z ≤ K) (hK : ∀ P : Sylow 2 K, IsMulCommutative (P : Subgroup K)) :
    SolvAbSylow Z :=
  ⟨Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hZS),
    absSylow_of_injective (Subgroup.inclusion hZK) (Subgroup.inclusion_injective hZK) hK⟩

end General

theorem admResidual_le {G : Type*} [Group G] {X Y : Subgroup G} (hYX : Y ≤ X)
    [hN : (Y.subgroupOf X).Normal] (h : SolvAbSylow (X ⧸ Y.subgroupOf X)) : admResidual X ≤ Y :=
  sInf_le ⟨hYX, hN, h.1, h.2⟩

theorem orderOf_odd_of_mem_oUpperTwo_sup_commutator {Q : Type*} [Group Q] [Finite Q]
    (h : Odd (Nat.card (commutator Q))) {x : Q}
    (hx : x ∈ oUpperTwo (⊤ : Subgroup Q) ⊔ commutator Q) : Odd (orderOf x) := by
  have hcomm : ∀ a b : Q ⧸ commutator Q, a * b = b * a := by
    intro a b
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (commutator Q) a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (commutator Q) b
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  let O : Subgroup (Q ⧸ commutator Q) :=
    { carrier := {z | Odd (orderOf z)}
      mul_mem' := fun {a b} ha hb =>
        Odd.of_dvd_nat (Odd.mul ha hb) (Commute.orderOf_mul_dvd_mul_orderOf (hcomm a b))
      one_mem' := by simp
      inv_mem' := fun {a} ha => by simpa using ha }
  have hle : oUpperTwo (⊤ : Subgroup Q) ⊔ commutator Q ≤ O.comap (QuotientGroup.mk' _) := by
    refine sup_le ((closure_le _).mpr fun z hz => ?_) fun z hz => ?_
    · exact Odd.of_dvd_nat hz.2 (orderOf_map_dvd _ z)
    · change Odd (orderOf (QuotientGroup.mk' (commutator Q) z))
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).mpr hz, orderOf_one]
      exact odd_one
  have hk : Odd (orderOf (QuotientGroup.mk' (commutator Q) x)) := hle hx
  set k := orderOf (QuotientGroup.mk' (commutator Q) x) with hkdef
  have hxk : x ^ k ∈ commutator Q := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, hkdef, pow_orderOf_eq_one]
  have hm : Odd (orderOf (x ^ k)) := by
    have := Subgroup.orderOf_dvd_natCard (commutator Q) hxk
    exact Odd.of_dvd_nat h this
  refine Odd.of_dvd_nat (Odd.mul hk hm) (orderOf_dvd_of_pow_eq_one ?_)
  rw [pow_mul, pow_orderOf_eq_one]

end Lemma39

end CFSG.ComponentClassification.AS76b
