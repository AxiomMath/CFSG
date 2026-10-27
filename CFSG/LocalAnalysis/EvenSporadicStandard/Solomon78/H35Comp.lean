module

public import CFSG.Quasithin.Background.A1aFStar
public import CFSG.Walter.AStar.Subnormal
public import CFSG.Adapters.GeneralizedFittingTop
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

variable {G : Type} [Group G]

@[expose] def IsCompIn (M X : Subgroup G) : Prop :=
  M ≤ X ∧ CFSG.IsComponent (M.subgroupOf X)

theorem IsCompIn.le {M X : Subgroup G} (h : IsCompIn M X) : M ≤ X := h.1

theorem IsCompIn.isQuasisimple {M X : Subgroup G} (h : IsCompIn M X) : CFSG.IsQuasisimple ↥M :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.1) h.2.1

theorem isCompIn_of_subnormal {M X : Subgroup G} (hMX : M ≤ X) (hq : CFSG.IsQuasisimple ↥M)
    (hs : (M.subgroupOf X).IsSubnormal) : IsCompIn M X :=
  ⟨hMX, CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hMX).symm hq, hs⟩

theorem isCompIn_of_normal {M X : Subgroup G} (hMX : M ≤ X) (hq : CFSG.IsQuasisimple ↥M)
    (hn : (M.subgroupOf X).Normal) : IsCompIn M X :=
  isCompIn_of_subnormal hMX hq hn.isSubnormal

theorem IsCompIn.map_conj {M X : Subgroup G} (h : IsCompIn M X) {x : G} (hx : x ∈ X) :
    IsCompIn (M.map (MulAut.conj x).toMonoidHom) X := by
  have hle : M.map (MulAut.conj x).toMonoidHom ≤ X := by
    rintro _ ⟨m, hm, rfl⟩
    exact X.mul_mem (X.mul_mem hx (h.1 hm)) (X.inv_mem hx)
  refine ⟨hle, ?_⟩
  have hc := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (⟨x, hx⟩ : ↥X)) h.2
  have heq : (M.map (MulAut.conj x).toMonoidHom).subgroupOf X =
      (M.subgroupOf X).map (MulAut.conj (⟨x, hx⟩ : ↥X)).toMonoidHom := by
    ext ⟨y, hy⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨m, hm, hmy⟩
      refine ⟨⟨m, h.1 hm⟩, hm, ?_⟩
      apply Subtype.ext
      simpa using hmy
    · rintro ⟨⟨m, hmX⟩, hm, hmy⟩
      refine ⟨m, hm, ?_⟩
      simpa using congrArg Subtype.val hmy
  rw [heq]
  exact hc

theorem IsCompIn.commute_of_ne [Finite G] {M₁ M₂ X : Subgroup G} (h₁ : IsCompIn M₁ X)
    (h₂ : IsCompIn M₂ X) (hne : M₁ ≠ M₂) : ∀ a ∈ M₁, ∀ b ∈ M₂, a * b = b * a := by
  rcases CFSG.LocalCores.distinct_components_commute h₁.2 h₂.2 with h | h
  · exfalso
    apply hne
    have h1 := congrArg (Subgroup.map X.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le h₁.1, Subgroup.map_subgroupOf_eq_of_le h₂.1] at h1
  · intro a ha b hb
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    have ha' : (⟨a, h₁.1 ha⟩ : ↥X) ∈ M₁.subgroupOf X := ha
    have hb' : (⟨b, h₂.1 hb⟩ : ↥X) ∈ M₂.subgroupOf X := hb
    have := Subgroup.mem_centralizer_iff.1 (hle ha') _ hb'
    exact congrArg Subtype.val this.symm

theorem oddCore_eq_pPrimeCore_two' (X : Type*) [Group X] :
    CFSG.oddCore X = CFSG.pPrimeCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, CFSG.pPrimeCore_eq_piCore]

theorem odd_card_oddCore' (X : Type*) [Group X] [Finite X] : Odd (Nat.card (CFSG.oddCore X)) := by
  rw [oddCore_eq_pPrimeCore_two']
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem isCompIn_of_isTwoComponentIn [Finite G] {M X : Subgroup G} (hO : CFSG.oddCore ↥X = ⊥)
    (h : CFSG.QuasithinUnique.Id2519.IsTwoComponentIn M X) : IsCompIn M X := by
  have hMX : M ≤ X := CFSG.Quasithin.le_of_mem_cComp h.1
  have hsub : (M.subgroupOf X).IsSubnormal := by
    have h1 : CFSG.Open.IsSubnormal M X := CFSG.Quasithin.subnormal_of_mem_cComp h.1
    exact (CFSG.Adapters.isSubnormal_top_iff _).1
      ((CFSG.Quasithin.isSubnormal_subgroupOf_top_iff hMX).2 h1)
  have hO2 : CFSG.pPrimeCore 2 ↥X = ⊥ := by rw [← oddCore_eq_pPrimeCore_two', hO]
  have hle := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hsub
  rw [hO2, le_bot_iff] at hle
  have hcore : CFSG.oddCore ↥(M.subgroupOf X) = ⊥ := by
    rw [oddCore_eq_pPrimeCore_two']
    exact (Subgroup.map_eq_bot_iff_of_injective _ (M.subgroupOf X).subtype_injective).1 hle
  let e : ↥(M.subgroupOf X) ≃* ↥M := Subgroup.subgroupOfEquivOfLe hMX
  have hOM : CFSG.oddCore ↥M = ⊥ := by
    have hN : ((CFSG.oddCore ↥M).map e.symm.toMonoidHom).Normal :=
      Subgroup.Normal.map inferInstance _ e.symm.surjective
    have hodd : Odd (Nat.card ((CFSG.oddCore ↥M).map e.symm.toMonoidHom)) := by
      rw [Subgroup.card_map_of_injective e.symm.injective]
      exact odd_card_oddCore' _
    have hle2 : (CFSG.oddCore ↥M).map e.symm.toMonoidHom ≤ CFSG.oddCore ↥(M.subgroupOf X) :=
      le_sSup ⟨hN, hodd⟩
    rw [hcore, le_bot_iff] at hle2
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective).1 hle2
  have hqM : CFSG.IsQuasisimple ↥M :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hOM).trans QuotientGroup.quotientBot) h.2
  exact isCompIn_of_subnormal hMX hqM hsub

end CFSG.EvenSporadicStandard.Solomon78
