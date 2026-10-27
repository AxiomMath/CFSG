module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Mult
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chains

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard

@[expose] def PairShape (P : ℕ → Prop) : PairClass := fun _ _ L K u =>
  u ∈ L ∧ orderOf u = 2 ∧ K ≤ L ∧ (∀ k ∈ K, k * u = u * k) ∧ P (Nat.card K)

@[expose] def IsKPinned (s : TauCeti.SporadicName) (P : ℕ → Prop) : GroupClass :=
  fun X _ => ∃ (u : Carrier s) (K : Subgroup (Carrier s)),
    PairShape P (Carrier s) ⊤ K u ∧ Nonempty (X ≃* ↥K)

theorem pairShape_restrict {P : ℕ → Prop} {H : Type} [Group H] {L K : Subgroup H} {u : H}
    (h : PairShape P H L K u) :
    PairShape P ↥L ⊤ (K.subgroupOf L) ⟨u, h.1⟩ := by
  obtain ⟨huL, hu2, hKL, hKu, hP⟩ := h
  refine ⟨mem_top _, ?_, le_top, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]; exact hu2
  · intro k hk
    exact Subtype.ext (hKu k hk)
  · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv]

theorem isKPinned_of_pair {s : TauCeti.SporadicName} {P : ℕ → Prop} {H : Type} [Group H]
    {L K : Subgroup H} {u : H} (e : ↥L ≃* Carrier s) (h : PairShape P H L K u) :
    IsKPinned s P ↥K := by
  obtain ⟨huL, hu2, hKL, hKu, hP⟩ := h
  have hcard : Nat.card ((K.subgroupOf L).map e.toMonoidHom) = Nat.card K := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv
  refine ⟨e ⟨u, huL⟩, (K.subgroupOf L).map e.toMonoidHom,
    ⟨mem_top _, ?_, le_top, ?_, hcard ▸ hP⟩,
    ⟨(Subgroup.subgroupOfEquivOfLe hKL).symm.trans
      ((K.subgroupOf L).equivMapOfInjective e.toMonoidHom e.injective)⟩⟩
  · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hu2
  · rintro _ ⟨k, hk, rfl⟩
    show e k * e ⟨u, huL⟩ = e ⟨u, huL⟩ * e k
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hKu k hk))

theorem exists_pair_of_pinned {s : TauCeti.SporadicName} {P : ℕ → Prop} {H : Type} [Group H]
    {L : Subgroup H} (e : ↥L ≃* Carrier s)
    (hex : ∃ (u : Carrier s) (K : Subgroup (Carrier s)), PairShape P (Carrier s) ⊤ K u) :
    ∃ (K : Subgroup H) (u : H), PairShape P H L K u := by
  obtain ⟨u, K, -, hu2, -, hKu, hP⟩ := hex
  refine ⟨(K.map e.symm.toMonoidHom).map L.subtype, ((e.symm u : ↥L) : H),
    (e.symm u).2, ?_, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hu2
  · rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    show ((e.symm k : ↥L) : H) * ((e.symm u : ↥L) : H) = ((e.symm u : ↥L) : H) * (e.symm k : ↥L)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hKu k hk]
  · rw [Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective]
    exact hP

theorem oddCover_finite {s : TauCeti.SporadicName} (hfin : Finite (Carrier s)) {H : Type}
    [Group H] {L : Subgroup H} (h : OddCover s L) : Finite ↥L := by
  have hZ : Finite ↥(center ↥L) := Nat.finite_of_card_ne_zero h.2.1.pos.ne'
  obtain ⟨e⟩ := h.2.2
  have : Finite (↥L ⧸ center ↥L) := Finite.of_equiv _ e.symm.toEquiv
  exact Finite.of_subgroup_quotient (center ↥L)

theorem oddCover_isSporadic {s : TauCeti.SporadicName} (hfin : Finite (Carrier s))
    (hmult : OddMultTrivial s) {H : Type} [Group H] {L : Subgroup H} (h : OddCover s L) :
    IsSporadic ↥L s := by
  have := oddCover_finite hfin h
  exact isSporadic_of_center_eq_bot (hmult ↥L h.1 h.2.1 h.2.2) h.2.2

end CFSG.EvenSporadicStandard.Induction
