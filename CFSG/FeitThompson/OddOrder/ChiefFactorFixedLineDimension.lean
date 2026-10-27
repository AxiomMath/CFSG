module

public import CFSG.FeitThompson.Local.FixedOrderMultiplicativityNormal
public import CFSG.FeitThompson.OddOrder.ChiefFactorIrreducibleComplementModule
import CFSG.FeitThompson.Local.FrobeniusWielandtKernelFixedFree
import CFSG.FeitThompson.Local.WielandtFixedPointOrderSolvable
import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace ChiefFactorFixedLine

open Subgroup ChiefFactorLinearAction

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {M : Type*} [Group M]

theorem isInvariantSubgroup_conjNormal (H H₀ : Subgroup M) [H.Normal] [H₀.Normal] :
    IsInvariantSubgroup (MulAut.conjNormal : M →* MulAut ↥H) (H₀.subgroupOf H) :=
  isInvariantSubgroup_iff_forall_map_eq.mpr (map_conjNormal_subgroupOf H H₀)

theorem quotientAut_comp_eq (H H₀ D : Subgroup M) [H.Normal] [H₀.Normal] :
    ((isInvariantSubgroup_conjNormal H H₀).comp D.subtype).quotientAut
      = (factorConjAut H H₀).comp D.subtype := by
  ext d x
  induction x using QuotientGroup.induction_on with
  | H y =>
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [IsInvariantSubgroup.quotientAut_mk, factorConjAut_mk]
    rfl

theorem fixedPoints_conjNormal_comp_subtype {H : Subgroup M} [H.Normal] (D : Subgroup M) :
    FixedPoints.subgroup ((MulAut.conjNormal (H := H)).comp D.subtype).range ↥H
      = (H ⊓ Subgroup.centralizer (D : Set M)).subgroupOf H := by
  ext v
  rw [mem_fixedPoints_range_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  simp only [Subgroup.mem_centralizer_iff, MonoidHom.comp_apply, Subgroup.coe_subtype]
  constructor
  · intro h
    refine ⟨v.2, fun g hg => ?_⟩
    have h2 := congrArg (Subtype.val (p := fun y : M => y ∈ H)) (h ⟨g, hg⟩)
    rw [MulAut.conjNormal_apply] at h2
    calc g * (v : M) = g * (v : M) * g⁻¹ * g := by group
      _ = (v : M) * g := by rw [h2]
  · rintro ⟨-, h⟩ d
    refine Subtype.ext ?_
    rw [MulAut.conjNormal_apply, h (d : M) d.2]
    group

def factorCentralizer (H H₀ D : Subgroup M) [H.Normal] [H₀.Normal] :
    Subgroup (↥H ⧸ H₀.subgroupOf H) :=
  FixedPoints.subgroup ((factorConjAut H H₀).comp D.subtype).range (↥H ⧸ H₀.subgroupOf H)

@[simp]
theorem mem_factorCentralizer {H H₀ D : Subgroup M} [H.Normal] [H₀.Normal]
    {x : ↥H ⧸ H₀.subgroupOf H} :
    x ∈ factorCentralizer H H₀ D ↔ ∀ d ∈ D, factorConjAut H H₀ d x = x := by
  rw [factorCentralizer, mem_fixedPoints_range_iff]
  exact ⟨fun h d hd => h ⟨d, hd⟩, fun h d => h d d.2⟩

theorem factorCentralizer_mono {H H₀ D D' : Subgroup M} [H.Normal] [H₀.Normal] (h : D ≤ D') :
    factorCentralizer H H₀ D' ≤ factorCentralizer H H₀ D := fun x hx =>
  mem_factorCentralizer.2 fun d hd => mem_factorCentralizer.1 hx d (h hd)

@[simp]
theorem factorCentralizer_bot (H H₀ : Subgroup M) [H.Normal] [H₀.Normal] :
    factorCentralizer H H₀ (⊥ : Subgroup M) = ⊤ :=
  eq_top_iff.2 fun x _ => mem_factorCentralizer.2 fun d hd => by
    rw [Subgroup.mem_bot] at hd; simp [hd]

theorem centralizer_subgroupOf {A U : Subgroup M} {b : M} (hb : b ∈ A) :
    (U.subgroupOf A) ⊓ Subgroup.centralizer {(⟨b, hb⟩ : ↥A)}
      = (U ⊓ Subgroup.centralizer {b}).subgroupOf A := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
  exact and_congr Iff.rfl ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem range_comp_subgroupOf_subtype {N : Type*} [Group N] (f : M →* N) {A B : Subgroup M}
    (h : B ≤ A) :
    ((f.comp A.subtype).comp (B.subgroupOf A).subtype).range = (f.comp B.subtype).range := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨⟨_, a.2⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨⟨⟨(b : M), h b.2⟩, b.2⟩, rfl⟩

section Lifting

variable {H H₀ D : Subgroup M} [H.Normal] [H₀.Normal] [Finite H] [Finite D]
  [Group.IsSolvable ↥D] [Group.IsSolvable ↥H]

theorem factorCentralizer_eq_map (hcop : (Nat.card D).Coprime (Nat.card H)) :
    factorCentralizer H H₀ D
      = ((H ⊓ Subgroup.centralizer (D : Set M)).subgroupOf H).map
          (QuotientGroup.mk' (H₀.subgroupOf H)) := by
  rw [factorCentralizer, ← quotientAut_comp_eq,
    fixedPoints_quotientAut_range ((isInvariantSubgroup_conjNormal H H₀).comp D.subtype) hcop,
    fixedPoints_conjNormal_comp_subtype]

theorem factorCentralizer_eq_bot (hcop : (Nat.card D).Coprime (Nat.card H))
    (hle : H ⊓ Subgroup.centralizer (D : Set M) ≤ H₀) : factorCentralizer H H₀ D = ⊥ := by
  rw [factorCentralizer_eq_map hcop, eq_bot_iff]
  rintro x ⟨y, hy, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact hle hy

theorem isCyclic_factorCentralizer (hcop : (Nat.card D).Coprime (Nat.card H))
    [IsCyclic ↥(H ⊓ Subgroup.centralizer (D : Set M))] :
    IsCyclic ↥(factorCentralizer H H₀ D) := by
  have hcyc : IsCyclic ↥((H ⊓ Subgroup.centralizer (D : Set M)).subgroupOf H) :=
    isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe inf_le_left).toMonoidHom
      (MulEquiv.injective _)
  rw [factorCentralizer_eq_map hcop]
  exact isCyclic_of_surjective ((QuotientGroup.mk' (H₀.subgroupOf H)).subgroupMap _)
    (by rintro ⟨y, x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩)

end Lifting

structure IsFixedLineSetup (H A U B H₀ : Subgroup M) (q : ℕ) : Prop where
  isComplement_A : H.IsComplement' A
  coprime : (Nat.card ↥H).Coprime (Nat.card ↥A)
  le_U : U ≤ A
  le_B : B ≤ A
  normal_U : (U.subgroupOf A).Normal
  isComplement_B : Subgroup.IsComplement' (U.subgroupOf A) (B.subgroupOf A)
  prime_q : q.Prime
  card_B : Nat.card ↥B = q
  centralizer_inf_eq_bot : ∀ b ∈ B, b ≠ 1 → U ⊓ Subgroup.centralizer {b} = ⊥
  isChiefFactor : IsChiefFactor H H₀
  centralizer_U_le : H ⊓ Subgroup.centralizer (U : Set M) ≤ H₀
  isCyclic_centralizer_B : IsCyclic ↥(H ⊓ Subgroup.centralizer (B : Set M))

namespace IsFixedLineSetup

variable [Finite M] [Group.IsSolvable M] {H A U B H₀ : Subgroup M} [H.Normal] [H₀.Normal] {q : ℕ}
  (hs : IsFixedLineSetup H A U B H₀ q)

include hs

theorem isCyclic_B : IsCyclic ↥B :=
  haveI := Fact.mk hs.prime_q
  isCyclic_of_prime_card hs.card_B

theorem factorCentralizer_U : factorCentralizer H H₀ U = ⊥ :=
  factorCentralizer_eq_bot
    (hs.coprime.symm.coprime_dvd_left (Subgroup.card_dvd_of_le hs.le_U)) hs.centralizer_U_le

theorem factorCentralizer_B :
    factorCentralizer H H₀ B
      = ((H ⊓ Subgroup.centralizer (B : Set M)).subgroupOf H).map
          (QuotientGroup.mk' (H₀.subgroupOf H)) :=
  factorCentralizer_eq_map (hs.coprime.symm.coprime_dvd_left (Subgroup.card_dvd_of_le hs.le_B))

theorem isCyclic_factorCentralizer_B : IsCyclic ↥(factorCentralizer H H₀ B) :=
  have := hs.isCyclic_centralizer_B
  isCyclic_factorCentralizer (hs.coprime.symm.coprime_dvd_left (Subgroup.card_dvd_of_le hs.le_B))

theorem natCard_quotient_eq_pow :
    Nat.card (↥H ⧸ H₀.subgroupOf H) = Nat.card (factorCentralizer H H₀ B) ^ q := by
  set E := ↥H ⧸ H₀.subgroupOf H
  set ρ : ↥A →* MulAut E := (factorConjAut H H₀).comp A.subtype with hρ
  have hcopE : (Nat.card ↥A).Coprime (Nat.card E) :=
    hs.coprime.symm.coprime_dvd_right (Subgroup.card_quotient_dvd_card _)
  have hC : ∀ w ∈ B.subgroupOf A, w ≠ 1 →
      (U.subgroupOf A) ⊓ Subgroup.centralizer {w} = ⊥ := by
    intro w hw hw1
    rw [Subgroup.mem_subgroupOf] at hw
    rw [show w = (⟨(w : M), w.2⟩ : ↥A) from rfl, centralizer_subgroupOf w.2,
      hs.centralizer_inf_eq_bot (w : M) hw (fun h => hw1 (Subtype.ext h)), Subgroup.bot_subgroupOf]
  have hCU : ∀ v : E, (∀ b ∈ U.subgroupOf A, ρ b v = v) → v = 1 := by
    intro v hv
    have hmem : v ∈ factorCentralizer H H₀ U :=
      mem_factorCentralizer.2 fun u hu =>
        hv ⟨u, hs.le_U hu⟩ (by rwa [Subgroup.mem_subgroupOf])
    rw [hs.factorCentralizer_U, Subgroup.mem_bot] at hmem
    exact hmem
  have key := natCard_eq_natCard_fixedPoints_pow_natCard ρ hcopE hs.normal_U hs.isComplement_B
    hC hCU
  rw [← natCard_fixedPoints_comp_subtype_eq_natCard_subtype ρ (B.subgroupOf A), hρ,
    range_comp_subgroupOf_subtype _ hs.le_B] at key
  rw [key, ← factorCentralizer, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hs.le_B).toEquiv,
    hs.card_B]

section Linear

variable {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative V)

include e

theorem natCard_factorCentralizer_B_eq (hp : p.Prime) :
    Nat.card (factorCentralizer H H₀ B) = p := by
  have hfin : Finite V := Finite.of_equiv _ (e.toEquiv.trans Multiplicative.toAdd)
  have hcyc := hs.isCyclic_factorCentralizer_B
  have hpow : ∀ x : ↥(factorCentralizer H H₀ B), x ^ p = 1 := by
    intro x
    refine Subtype.ext ?_
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    refine e.injective ?_
    rw [map_pow, map_one]
    change p • (Multiplicative.toAdd (e (x : ↥H ⧸ H₀.subgroupOf H))) = (0 : V)
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_self, zero_smul]
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥(factorCentralizer H H₀ B))
  rcases hp.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one (hpow g)) with h1 | h1
  · exfalso
    have h1' : Nat.card ↥(factorCentralizer H H₀ B) = 1 := hg ▸ h1
    have hE : Nat.card (↥H ⧸ H₀.subgroupOf H) = 1 := by
      rw [hs.natCard_quotient_eq_pow, h1', one_pow]
    rw [← Subgroup.index_eq_card, Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at hE
    exact hs.isChiefFactor.lt.ne' (le_antisymm hE hs.isChiefFactor.le)
  · exact hg ▸ h1

theorem finrank_eq (hp : p.Prime) : Module.finrank (ZMod p) V = q := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite V := Finite.of_equiv _ (e.toEquiv.trans Multiplicative.toAdd)
  have hcard : Nat.card V = p ^ q := by
    rw [← Nat.card_congr (e.toEquiv.trans Multiplicative.toAdd), hs.natCard_quotient_eq_pow,
      hs.natCard_factorCentralizer_B_eq e hp]
  have hfinite : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have b := Module.finBasis (ZMod p) V
  have h2 : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    rw [Nat.card_congr (b.repr.toEquiv.trans Finsupp.equivFunOnFinite), Nat.card_eq_fintype_card,
      Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [hcard] at h2
  exact (Nat.pow_right_injective hp.two_le h2).symm

end Linear

end IsFixedLineSetup

end ChiefFactorFixedLine

end CFSG.FeitThompson
