module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Local.QuadraticActionsDescendSections
import CFSG.FeitThompson.Local.CommonFixedFrobeniusComplementPrimeOrder
import CFSG.FeitThompson.Local.WielandtFixedPointOrderSolvable
import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
import CFSG.FeitThompson.Representations.PrimeFieldFrobeniusComplementDerivedTrivial
import CFSG.FeitThompson.Local.FixedOrderElementaryAbelianCover
import CFSG.FeitThompson.Local.ConjugateFixedPointOrders
import CFSG.FeitThompson.Foundations.QuotientOrderByNormal
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u v

variable {A : Type u} [Group A] {D K : Subgroup A}

private theorem natCard_eq_prime_of_isCyclic_of_pow_eq_one {q : ℕ} (hq : q.Prime) {G : Type*}
    [Group G] [Nontrivial G] [IsCyclic G] (h : ∀ g : G, g ^ q = 1) : Nat.card G = q := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hg1 : g ≠ 1 := by
    rintro rfl
    obtain ⟨y, hy⟩ := exists_ne (1 : G)
    exact hy (by simpa using hg y)
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg, orderOf_eq_prime (h g) hg1]

theorem pow_eq_one_multiplicative_pi_zmod (q d : ℕ) (w : Multiplicative (Fin d → ZMod q)) :
    w ^ q = 1 := by
  refine Multiplicative.toAdd.injective ?_
  have h : Multiplicative.toAdd (w ^ q) = q • Multiplicative.toAdd w := rfl
  rw [h]
  funext i
  change q • (Multiplicative.toAdd w) i = 0
  simp [nsmul_eq_mul]

section Invariant

variable {V : Type v} [Group V] {ρ : A →* MulAut V} {N : Subgroup V}

theorem mem_fixedPoints_restrictAut_comp_subtype_iff (hN : IsInvariantSubgroup ρ N)
    (B : Subgroup A) {v : ↥N} :
    v ∈ FixedPoints.subgroup (hN.restrictAut.comp B.subtype).range ↥N
      ↔ ∀ b ∈ B, ρ b (v : V) = (v : V) := by
  rw [mem_fixedPoints_comp_subtype_iff]
  refine forall_congr' fun b => forall_congr' fun _ => ?_
  rw [Subtype.ext_iff, hN.coe_restrictAut_apply]

theorem map_subtype_fixedPoints_restrictAut_comp_subtype (hN : IsInvariantSubgroup ρ N)
    (B : Subgroup A) :
    (FixedPoints.subgroup (hN.restrictAut.comp B.subtype).range ↥N).map N.subtype
      = N ⊓ FixedPoints.subgroup (ρ.comp B.subtype).range V := by
  refine le_antisymm ?_ ?_
  · rintro v ⟨w, hw, rfl⟩
    exact ⟨w.2, (mem_fixedPoints_comp_subtype_iff ρ B).2
      ((mem_fixedPoints_restrictAut_comp_subtype_iff hN B).1 hw)⟩
  · intro v hv
    exact ⟨⟨v, hv.1⟩, (mem_fixedPoints_restrictAut_comp_subtype_iff hN B).2
      ((mem_fixedPoints_comp_subtype_iff ρ B).1 hv.2), rfl⟩

theorem isCyclic_fixedPoints_restrictAut (hN : IsInvariantSubgroup ρ N) (B : Subgroup A)
    [IsCyclic (FixedPoints.subgroup (ρ.comp B.subtype).range V)] :
    IsCyclic (FixedPoints.subgroup (hN.restrictAut.comp B.subtype).range ↥N) := by
  set C : Subgroup ↥N := FixedPoints.subgroup (hN.restrictAut.comp B.subtype).range ↥N with hC
  have h1 : IsCyclic ↥(C.map N.subtype) := by
    rw [hC, map_subtype_fixedPoints_restrictAut_comp_subtype hN B]
    exact Subgroup.isCyclic_of_le inf_le_right
  exact isCyclic_of_injective
    (Subgroup.equivMapOfInjective C N.subtype N.subtype_injective).toMonoidHom
    (Subgroup.equivMapOfInjective C N.subtype N.subtype_injective).injective

theorem fixedPoints_quotientAut_comp_subtype [Finite A] [Finite V] [N.Normal]
    [Group.IsSolvable ↥N] (hN : IsInvariantSubgroup ρ N) (B : Subgroup A) [Group.IsSolvable ↥B]
    (hcop : (Nat.card ↥B).Coprime (Nat.card V)) :
    FixedPoints.subgroup (hN.quotientAut.comp B.subtype).range (V ⧸ N)
      = (FixedPoints.subgroup (ρ.comp B.subtype).range V).map (QuotientGroup.mk' N) := by
  rw [← hN.quotientAut_comp B.subtype]
  exact fixedPoints_quotientAut_range_of_isSolvable_subgroup (hN.comp B.subtype) hcop

end Invariant

theorem eq_one_of_mem_commutator_of_natCard_fixedPoints_eq_prime {V : Type v} [Group V]
    [Finite A] {q d : ℕ} (hq : q.Prime) (e : V ≃* Multiplicative (Fin d → ZMod q))
    (hD : D.Normal) (hDK : Subgroup.IsComplement' D K) (hD1 : D ≠ ⊥) (hK1 : K ≠ ⊥)
    (hfrob : ∀ k ∈ K, k ≠ 1 → D ⊓ Subgroup.centralizer {k} = ⊥) [Group.IsSolvable ↥D]
    (hKprime : (Nat.card ↥K).Prime) (hqA : ¬ q ∣ Nat.card A) (ρ : A →* MulAut V)
    (hCK : Nat.card (FixedPoints.subgroup (ρ.comp K.subtype).range V) = q)
    {x : A} (hx : x ∈ ⁅D, D⁆) : ρ x = 1 := by
  let inst : MulDistribMulAction A V := MulDistribMulAction.compHom V ρ
  have : Fact q.Prime := ⟨hq⟩
  set σ : A →* GL (Fin d) (ZMod q) := elementaryAbelianRep A e with hσ
  have hcards : Nat.card (FixedPoints.subgroup (K : Type _) V)
      = Nat.card (FixedPoints.subgroup (ρ.comp K.subtype).range V) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v => by
      rw [mem_fixedPoints_subgroup_iff, mem_fixedPoints_comp_subtype_iff]
      exact ⟨fun h b hb => h b hb, fun h b hb => h b hb⟩)
  have hfin : finrank (ZMod q) (glFixedSpace σ K) = 1 := by
    have h := natCard_fixedPoints_subgroup_eq_pow (V := V) hq e K
    rw [hcards, hCK] at h
    have h1 : q ^ 1 = q ^ finrank (ZMod q) (glFixedSpace σ K) := by rw [pow_one]; exact h
    exact (Nat.pow_right_injective hq.two_le h1).symm
  have hrep : glRepresentation (σ.comp K.subtype) = (glRepresentation σ).comp K.subtype := by
    refine MonoidHom.ext fun b => LinearMap.ext fun w => ?_
    simp
  have hinv : finrank (ZMod q)
      (Representation.invariants ((glRepresentation σ).comp K.subtype)) = 1 := by
    rw [← hrep, ← glFixedSpace_eq_invariants]; exact hfin
  have hmain := forall_apply_eq_self_of_mem_commutator_of_finrank_invariants_eq_one_zmod
    (p := q) (K := D) (R := K) hD hDK hD1 hK1 hfrob inferInstance hKprime hqA
    (glRepresentation σ) hinv x hx
  refine MulEquiv.ext fun w => ?_
  have h1 := hmain (Multiplicative.toAdd (e w))
  rw [glRepresentation_apply_apply, hσ, elementaryAbelianRep_mulVec_toAdd] at h1
  have h2 : ρ x w = w := e.injective (Multiplicative.toAdd.injective h1)
  rw [h2]
  rfl

private theorem forall_apply_eq_self_aux [Finite A] [Group.IsSolvable A]
    (hD : D.Normal) (hDK : Subgroup.IsComplement' D K) (hD1 : D ≠ ⊥) (hK1 : K ≠ ⊥)
    (hfrob : ∀ k ∈ K, k ≠ 1 → D ⊓ Subgroup.centralizer {k} = ⊥) :
    ∀ n : ℕ, ∀ {V : Type v} [Group V] [Finite V] [Group.IsSolvable V] (ρ : A →* MulAut V),
      Nat.card V ≤ n → (Nat.card A).Coprime (Nat.card V) →
      FixedPoints.subgroup (ρ.comp D.subtype).range V = ⊥ →
      (∀ k ∈ K, k ≠ 1 → FixedPoints.subgroup (ρ.comp (Subgroup.zpowers k).subtype).range V
        = FixedPoints.subgroup (ρ.comp K.subtype).range V) →
      IsCyclic (FixedPoints.subgroup (ρ.comp K.subtype).range V) →
      ∀ x ∈ ⁅D, D⁆, ρ x = 1 := by
  intro n
  induction n with
  | zero =>
    intro V _ _ _ ρ hn _ _ _ _
    exact absurd (Nat.le_zero.1 hn) Nat.card_pos.ne'
  | succ n ih =>
    intro V _ _ _ ρ hn hcop hCD hCK hcyc x hx
    rcases subsingleton_or_nontrivial V with hV | hV
    · exact MulEquiv.ext fun _ => Subsingleton.elim _ _
    obtain ⟨N, q, d, hNn, hNinv, hNb, hq, hd, ⟨e⟩⟩ :=
      exists_invariant_normal_elementaryAbelian ρ
    have : N.Normal := hNn
    by_cases hNtop : N = ⊤
    ·
      subst hNtop
      have eV : V ≃* Multiplicative (Fin d → ZMod q) := Subgroup.topEquiv.symm.trans e
      have hqV : q ∣ Nat.card V := by
        rw [Nat.card_eq_of_bijective eV eV.bijective, natCard_multiplicative_pi_zmod]
        exact dvd_pow_self q (by omega)
      have hqA : ¬ q ∣ Nat.card A := fun hc =>
        hq.one_lt.ne' (Nat.dvd_one.1 (hcop ▸ Nat.dvd_gcd hc hqV))
      have hCKne : FixedPoints.subgroup (ρ.comp K.subtype).range V ≠ ⊥ :=
        fixedPoints_ne_bot_of_fixedPoints_eq hcop hD hDK hK1 hfrob hCD hCK
      have hKprime : (Nat.card ↥K).Prime :=
        prime_natCard_of_fixedPoints_eq hcop hD hDK hK1 hfrob hCD hCK
      have : Nontrivial (FixedPoints.subgroup (ρ.comp K.subtype).range V) :=
        (Subgroup.nontrivial_iff_ne_bot _).2 hCKne
      have hexp : ∀ g : FixedPoints.subgroup (ρ.comp K.subtype).range V, g ^ q = 1 := by
        intro g
        refine Subtype.ext ?_
        have h1 : eV ((g : V) ^ q) = 1 := by
          rw [map_pow]
          exact pow_eq_one_multiplicative_pi_zmod q d _
        have h2 := eV.injective (h1.trans (map_one eV).symm)
        simpa using h2
      have hCKcard : Nat.card (FixedPoints.subgroup (ρ.comp K.subtype).range V) = q :=
        natCard_eq_prime_of_isCyclic_of_pow_eq_one hq hexp
      exact eq_one_of_mem_commutator_of_natCard_fixedPoints_eq_prime hq eV hD hDK hD1 hK1 hfrob
        hKprime hqA ρ hCKcard hx
    ·
      have hNlt : N < ⊤ := lt_of_le_of_ne le_top hNtop
      have hNpos : ⊥ < N := lt_of_le_of_ne bot_le (Ne.symm hNb)
      have hNcard : Nat.card ↥N ≤ n :=
        Nat.lt_succ_iff.1 (lt_of_lt_of_le (natCard_lt_natCard_of_lt_top hNlt) hn)
      have hQcard : Nat.card (V ⧸ N) ≤ n :=
        Nat.lt_succ_iff.1 (lt_of_lt_of_le (natCard_quotient_lt_natCard_of_bot_lt N hNpos) hn)
      have hcopN : (Nat.card A).Coprime (Nat.card ↥N) :=
        hcop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card N)
      have hCDN : FixedPoints.subgroup (hNinv.restrictAut.comp D.subtype).range ↥N = ⊥ := by
        rw [← Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective,
          map_subtype_fixedPoints_restrictAut_comp_subtype hNinv D, hCD, inf_bot_eq]
      have hCKN : ∀ k ∈ K, k ≠ 1 →
          FixedPoints.subgroup (hNinv.restrictAut.comp (Subgroup.zpowers k).subtype).range ↥N
            = FixedPoints.subgroup (hNinv.restrictAut.comp K.subtype).range ↥N := by
        intro k hk hk1
        refine Subgroup.map_injective N.subtype_injective ?_
        rw [map_subtype_fixedPoints_restrictAut_comp_subtype hNinv,
          map_subtype_fixedPoints_restrictAut_comp_subtype hNinv, hCK k hk hk1]
      have hcycN : IsCyclic
          (FixedPoints.subgroup (hNinv.restrictAut.comp K.subtype).range ↥N) :=
        isCyclic_fixedPoints_restrictAut hNinv K
      have hN' : ∀ x ∈ ⁅D, D⁆, hNinv.restrictAut x = 1 :=
        ih hNinv.restrictAut hNcard hcopN hCDN hCKN hcycN
      have hcopQ : (Nat.card A).Coprime (Nat.card (V ⧸ N)) :=
        hcop.coprime_dvd_right N.card_quotient_dvd_card
      have hcopD : (Nat.card ↥D).Coprime (Nat.card V) :=
        hcop.coprime_dvd_left (Subgroup.card_subgroup_dvd_card D)
      have hcopK : (Nat.card ↥K).Coprime (Nat.card V) :=
        hcop.coprime_dvd_left (Subgroup.card_subgroup_dvd_card K)
      have hCDQ : FixedPoints.subgroup (hNinv.quotientAut.comp D.subtype).range (V ⧸ N) = ⊥ := by
        rw [fixedPoints_quotientAut_comp_subtype hNinv D hcopD, hCD, Subgroup.map_bot]
      have hCKQ : ∀ k ∈ K, k ≠ 1 →
          FixedPoints.subgroup (hNinv.quotientAut.comp (Subgroup.zpowers k).subtype).range (V ⧸ N)
            = FixedPoints.subgroup (hNinv.quotientAut.comp K.subtype).range (V ⧸ N) := by
        intro k hk hk1
        have hz : (Nat.card ↥(Subgroup.zpowers k)).Coprime (Nat.card V) :=
          hcop.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _)
        rw [fixedPoints_quotientAut_comp_subtype hNinv _ hz,
          fixedPoints_quotientAut_comp_subtype hNinv K hcopK, hCK k hk hk1]
      have hcycQ : IsCyclic
          (FixedPoints.subgroup (hNinv.quotientAut.comp K.subtype).range (V ⧸ N)) := by
        rw [fixedPoints_quotientAut_comp_subtype hNinv K hcopK]
        exact isCyclic_of_surjective ((QuotientGroup.mk' N).subgroupMap _)
          ((QuotientGroup.mk' N).subgroupMap_surjective _)
      have hQ' : ∀ x ∈ ⁅D, D⁆, hNinv.quotientAut x = 1 :=
        ih hNinv.quotientAut hQcard hcopQ hCDQ hCKQ hcycQ
      set Dc : Subgroup A := ⁅D, D⁆ with hDc
      have hcopDc : (Nat.card ↥Dc).Coprime (Nat.card V) :=
        hcop.coprime_dvd_left (Subgroup.card_subgroup_dvd_card Dc)
      refine MulEquiv.ext fun v => ?_
      have hvq : ∀ b : ↥Dc, v⁻¹ * (ρ.comp Dc.subtype) b v ∈ N := by
        intro b
        have h2 : hNinv.quotientAut (b : A) (QuotientGroup.mk v) = QuotientGroup.mk v := by
          rw [hQ' (b : A) b.2]; rfl
        rw [hNinv.quotientAut_mk] at h2
        exact QuotientGroup.eq.1 h2.symm
      obtain ⟨w, hwN, hfix⟩ :=
        exists_mem_forall_apply_mul_eq (hNinv.comp Dc.subtype) hcopDc hvq
      have h1 : ρ x (v * w) = v * w := hfix ⟨x, hx⟩
      have hwfix : ρ x w = w := by
        have h3 : hNinv.restrictAut x ⟨w, hwN⟩ = ⟨w, hwN⟩ := by rw [hN' x hx]; rfl
        have h4 := Subtype.ext_iff.1 h3
        rwa [hNinv.coe_restrictAut_apply] at h4
      rw [map_mul, hwfix] at h1
      rw [mul_right_cancel h1]
      rfl

section Main

variable [Finite A] [Group.IsSolvable A] {V : Type v} [Group V] [Finite V] [Group.IsSolvable V]
  (ρ : A →* MulAut V) (hcop : (Nat.card A).Coprime (Nat.card V)) (hD : D.Normal)
  (hDK : Subgroup.IsComplement' D K) (hD1 : D ≠ ⊥) (hK1 : K ≠ ⊥)
  (hfrob : ∀ k ∈ K, k ≠ 1 → D ⊓ Subgroup.centralizer {k} = ⊥)
  (hCD : FixedPoints.subgroup (ρ.comp D.subtype).range V = ⊥)
  (hCK : ∀ k ∈ K, k ≠ 1 → FixedPoints.subgroup (ρ.comp (Subgroup.zpowers k).subtype).range V
    = FixedPoints.subgroup (ρ.comp K.subtype).range V)
  (hcyc : IsCyclic (FixedPoints.subgroup (ρ.comp K.subtype).range V))

include hcop hD hDK hD1 hK1 hfrob hCD hCK hcyc

theorem eq_one_of_mem_commutator_of_isCyclic_fixedPoints {x : A} (hx : x ∈ ⁅D, D⁆) : ρ x = 1 :=
  forall_apply_eq_self_aux hD hDK hD1 hK1 hfrob (Nat.card V) ρ le_rfl hcop hCD hCK hcyc x hx

theorem forall_apply_eq_self_of_mem_commutator_of_isCyclic_fixedPoints :
    ∀ x ∈ ⁅D, D⁆, ∀ v : V, ρ x v = v := by
  intro x hx v
  rw [eq_one_of_mem_commutator_of_isCyclic_fixedPoints ρ hcop hD hDK hD1 hK1 hfrob hCD hCK hcyc hx]
  rfl

theorem commutator_le_ker_of_isCyclic_fixedPoints : ⁅D, D⁆ ≤ ρ.ker := fun _ hx =>
  eq_one_of_mem_commutator_of_isCyclic_fixedPoints ρ hcop hD hDK hD1 hK1 hfrob hCD hCK hcyc hx

end Main

theorem eq_one_of_mem_commutator_of_isCyclic_setOf_fixed [Finite A] [Group.IsSolvable A]
    {V : Type v} [Group V] [Finite V] [Group.IsSolvable V] (ρ : A →* MulAut V)
    (hcop : (Nat.card A).Coprime (Nat.card V)) (hD : D.Normal)
    (hDK : Subgroup.IsComplement' D K) (hD1 : D ≠ ⊥) (hK1 : K ≠ ⊥)
    (hfrob : ∀ k ∈ K, k ≠ 1 → D ⊓ Subgroup.centralizer {k} = ⊥)
    (hCD : {v : V | ∀ d ∈ D, ρ d v = v} = {1})
    (hCK : ∀ k ∈ K, k ≠ 1 → {v : V | ρ k v = v} = {v : V | ∀ k' ∈ K, ρ k' v = v})
    (hcyc : ∃ g : V, {v : V | ∀ k ∈ K, ρ k v = v} = (Subgroup.zpowers g : Set V))
    {x : A} (hx : x ∈ ⁅D, D⁆) : ρ x = 1 := by
  have hCD' : FixedPoints.subgroup (ρ.comp D.subtype).range V = ⊥ := by
    refine Subgroup.eq_bot_iff_forall _ |>.2 fun v hv => ?_
    have h : v ∈ ({1} : Set V) := hCD ▸ (mem_fixedPoints_comp_subtype_iff ρ D).1 hv
    simpa using h
  have hCK' : ∀ k ∈ K, k ≠ 1 →
      FixedPoints.subgroup (ρ.comp (Subgroup.zpowers k).subtype).range V
        = FixedPoints.subgroup (ρ.comp K.subtype).range V := by
    intro k hk hk1
    refine SetLike.ext fun v => ?_
    rw [mem_fixedPoints_comp_subtype_iff ρ (Subgroup.zpowers k),
      mem_fixedPoints_comp_subtype_iff ρ K, forall_mem_zpowers_map_eq_iff]
    exact Set.ext_iff.1 (hCK k hk hk1) v
  have hcyc' : IsCyclic (FixedPoints.subgroup (ρ.comp K.subtype).range V) := by
    obtain ⟨g, hg⟩ := hcyc
    have h : FixedPoints.subgroup (ρ.comp K.subtype).range V = Subgroup.zpowers g := by
      refine SetLike.ext fun v => ?_
      rw [mem_fixedPoints_comp_subtype_iff, ← SetLike.mem_coe, ← hg]
      exact Iff.rfl
    rw [h]
    infer_instance
  exact eq_one_of_mem_commutator_of_isCyclic_fixedPoints ρ hcop hD hDK hD1 hK1 hfrob hCD' hCK'
    hcyc' hx

end CFSG.FeitThompson
