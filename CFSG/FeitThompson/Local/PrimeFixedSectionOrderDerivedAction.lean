module

public import Mathlib.GroupTheory.Complement
public import CFSG.FeitThompson.Local.PrimeFixedMinimalQuotient
import CFSG.FeitThompson.Local.CommonFixedFrobeniusComplementPrimeOrder
import CFSG.FeitThompson.Local.CyclicCommonFixedFrobeniusKernelDerived
import CFSG.FeitThompson.Local.FixedOrderMultiplicativityNormal
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup QuotientGroup Pointwise
open scoped commutatorElement

section Conj

variable {G A : Type*} [Group G] [Group A] {W : Subgroup G} [W.Normal]

theorem mem_fixedPoints_conjNormal_comp_iff (f : A →* G) (B : Subgroup A) {v : ↥W} :
    v ∈ FixedPoints.subgroup (((MulAut.conjNormal (H := W)).comp f).comp B.subtype).range ↥W ↔
      ∀ b ∈ B, f b * (v : G) * (f b)⁻¹ = (v : G) := by
  rw [mem_fixedPoints_comp_subtype_iff]
  refine forall_congr' fun b => forall_congr' fun _ => ?_
  rw [Subtype.ext_iff]
  simp [MulAut.conjNormal_apply]

theorem map_subtype_fixedPoints_conjNormal_comp (f : A →* G) (B : Subgroup A) :
    (FixedPoints.subgroup (((MulAut.conjNormal (H := W)).comp f).comp B.subtype).range ↥W).map
        W.subtype = W ⊓ centralizer ((B.map f : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.2, mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    have hx := (mem_fixedPoints_conjNormal_comp_iff f B).1 hv b hb
    calc f b * (v : G) = f b * (v : G) * (f b)⁻¹ * f b := by group
      _ = (v : G) * f b := by rw [hx]
  · intro hx
    refine ⟨⟨x, hx.1⟩, (mem_fixedPoints_conjNormal_comp_iff f B).2 fun b hb => ?_, rfl⟩
    have hc := mem_centralizer_iff.1 hx.2 (f b) ⟨b, hb, rfl⟩
    calc f b * x * (f b)⁻¹ = x * f b * (f b)⁻¹ := by rw [hc]
      _ = x := by group

theorem natCard_fixedPoints_conjNormal_comp (f : A →* G) (B : Subgroup A) :
    Nat.card (FixedPoints.subgroup (((MulAut.conjNormal (H := W)).comp f).comp B.subtype).range ↥W)
      = Nat.card ↥(W ⊓ centralizer ((B.map f : Subgroup G) : Set G)) := by
  rw [← map_subtype_fixedPoints_conjNormal_comp f B]
  exact (Subgroup.card_map_of_injective W.subtype_injective).symm

end Conj

theorem prime_natCard_and_natCard_eq_pow_and_forall_conj_eq {G A : Type*} [Group G] [Finite G]
    [Group.IsSolvable G] {W : Subgroup G} [W.Normal] [Group A] [Finite A] [Group.IsSolvable A]
    (f : A →* G) {D K : Subgroup A} {q : ℕ} (hq : q.Prime) (hW : W ≠ ⊥)
    (hcop : (Nat.card A).Coprime (Nat.card ↥W)) (hD : D.Normal) (hDK : IsComplement' D K)
    (hD1 : D ≠ ⊥) (hK1 : K ≠ ⊥)
    (hfrob : ∀ k ∈ K, k ≠ 1 → D ⊓ centralizer ({k} : Set A) = ⊥)
    (hCD : W ⊓ centralizer ((D.map f : Subgroup G) : Set G) = ⊥)
    (hCK : ∀ k ∈ K, k ≠ 1 → W ⊓ centralizer (((zpowers k).map f : Subgroup G) : Set G)
      = W ⊓ centralizer ((K.map f : Subgroup G) : Set G))
    (hcard : Nat.card ↥(W ⊓ centralizer ((K.map f : Subgroup G) : Set G)) = q) :
    (Nat.card ↥K).Prime ∧ Nat.card ↥W = q ^ Nat.card ↥K ∧
      ∀ x ∈ ⁅D, D⁆, ∀ w ∈ W, f x * w * (f x)⁻¹ = w := by
  have : Fact q.Prime := ⟨hq⟩
  have : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).2 hW
  set ρ : A →* MulAut ↥W := (MulAut.conjNormal (H := W)).comp f with hρ
  have hCD' : FixedPoints.subgroup (ρ.comp D.subtype).range ↥W = ⊥ := by
    rw [← Subgroup.map_eq_bot_iff_of_injective _ W.subtype_injective, hρ,
      map_subtype_fixedPoints_conjNormal_comp f D, hCD]
  have hCK' : ∀ k ∈ K, k ≠ 1 →
      FixedPoints.subgroup (ρ.comp (zpowers k).subtype).range ↥W
        = FixedPoints.subgroup (ρ.comp K.subtype).range ↥W := by
    intro k hk hk1
    refine Subgroup.map_injective W.subtype_injective ?_
    rw [hρ, map_subtype_fixedPoints_conjNormal_comp f (zpowers k),
      map_subtype_fixedPoints_conjNormal_comp f K, hCK k hk hk1]
  have hcardFP : Nat.card (FixedPoints.subgroup (ρ.comp K.subtype).range ↥W) = q := by
    rw [hρ, natCard_fixedPoints_conjNormal_comp f K, hcard]
  have hcyc : IsCyclic (FixedPoints.subgroup (ρ.comp K.subtype).range ↥W) :=
    isCyclic_of_prime_card hcardFP
  refine ⟨prime_natCard_of_fixedPoints_eq hcop hD hDK hK1 hfrob hCD' hCK', ?_, ?_⟩
  · rw [natCard_eq_natCard_fixedPoints_pow_natCard_of_fixedPoints_eq hcop hD hDK hK1 hfrob hCD'
      hCK', hcardFP]
  · intro x hx w hw
    have h1 := forall_apply_eq_self_of_mem_commutator_of_isCyclic_fixedPoints ρ hcop hD hDK hD1
      hK1 hfrob hCD' hCK' hcyc x hx ⟨w, hw⟩
    have h2 := congrArg (Subtype.val (p := fun z : G => z ∈ W)) h1
    rw [hρ] at h2
    simpa [MulAut.conjNormal_apply] using h2

variable {X : Type*} [Group X] {q : ℕ} {Q D K Z : Subgroup X}

theorem map_subgroupOf_comp_subtype {G : Type*} [Group G] (g : X →* G) {D A : Subgroup X}
    (hDA : D ≤ A) : (D.subgroupOf A).map (g.comp A.subtype) = D.map g := by
  rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hDA]

theorem exists_mem_commutator_subgroupOf {D A : Subgroup X} (hDA : D ≤ A) {x : X}
    (hx : x ∈ ⁅D, D⁆) : ∃ y ∈ ⁅D.subgroupOf A, D.subgroupOf A⁆, (y : X) = x := by
  have hmap : (⁅D.subgroupOf A, D.subgroupOf A⁆ : Subgroup ↥A).map A.subtype = ⁅D, D⁆ := by
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hDA]
  rw [← hmap] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  exact ⟨y, hy, hyx⟩

namespace IsPrimeFixedSectionSetup

theorem isComplement'_subgroupOf (h : IsPrimeFixedSectionSetup X q Q D K Z) :
    IsComplement' (D.subgroupOf (D ⊔ K)) (K.subgroupOf (D ⊔ K)) := by
  refine isComplement'_of_disjoint_and_mul_eq_univ (Subgroup.disjoint_def.2 fun {x} hx1 hx2 =>
    Subtype.ext (Subgroup.mem_bot.1 (h.inf_D_K.le ⟨mem_subgroupOf.1 hx1, mem_subgroupOf.1 hx2⟩))) ?_
  refine Set.eq_univ_of_forall fun x => ?_
  have hx : (x : X) ∈ (D : Set X) * (K : Set X) := by rw [← h.coe_sup_D_K]; exact x.2
  obtain ⟨d, hd, k, hk, hdk⟩ := hx
  exact ⟨⟨d, (le_sup_left : D ≤ D ⊔ K) hd⟩, mem_subgroupOf.2 hd,
    ⟨k, (le_sup_right : K ≤ D ⊔ K) hk⟩, mem_subgroupOf.2 hk, Subtype.ext hdk⟩

theorem inf_centralizer_subgroupOf (h : IsPrimeFixedSectionSetup X q Q D K Z) :
    ∀ k ∈ K.subgroupOf (D ⊔ K), k ≠ 1 →
      D.subgroupOf (D ⊔ K) ⊓ centralizer ({k} : Set ↥(D ⊔ K)) = ⊥ := by
  intro k hk hk1
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxD : (x : X) ∈ D := mem_subgroupOf.1 hx.1
  have hxc : (k : X) * (x : X) = (x : X) * (k : X) := by
    have := Subgroup.mem_centralizer_iff.1 hx.2 k rfl
    exact_mod_cast congrArg Subtype.val this
  have hmem : (x : X) ∈ D ⊓ centralizer ({(k : X)} : Set X) :=
    ⟨hxD, Subgroup.mem_centralizer_iff.2 (by simpa using hxc)⟩
  rw [h.inf_centralizer_D k (mem_subgroupOf.1 hk) (fun hc => hk1 (Subtype.ext hc))] at hmem
  exact Subtype.ext (Subgroup.mem_bot.1 hmem)

variable (h : IsPrimeFixedSectionSetup X q Q D K Z)
  (hQ0 : Q ⊓ centralizer (D : Set X) < Q)

include h hQ0

theorem prime_natCard_K_and_natCard_map_mk'_Q_and_commutator_le :
    haveI := normal_inf_centralizer h hQ0
    (Nat.card ↥K).Prime ∧
      Nat.card ↥(Q.map (mk' (Q ⊓ centralizer (D : Set X)))) = q ^ Nat.card ↥K ∧
      ⁅Q, ⁅D, D⁆⁆ ≤ Q ⊓ centralizer (D : Set X) := by
  have := normal_inf_centralizer h hQ0
  have : Finite X := h.finite
  have : Group.IsSolvable X := h.isSolvable
  set Q0 : Subgroup X := Q ⊓ centralizer (D : Set X) with hQ0def
  set A : Subgroup X := D ⊔ K with hA
  set f : ↥A →* X ⧸ Q0 := (mk' Q0).comp A.subtype with hf
  have hVnormal : (Q.map (mk' Q0)).Normal := normal_map_mk' h hQ0
  have hDA : D ≤ A := le_sup_left
  have hKA : K ≤ A := le_sup_right
  have hcopV : (Nat.card ↥A).Coprime (Nat.card ↥(Q.map (mk' Q0))) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd Q (mk' Q0))
      (h.coprime_natCard_Q_of_le_sup (A := A) le_rfl)
  have hmapD : (D.subgroupOf A).map f = D.map (mk' Q0) := map_subgroupOf_comp_subtype _ hDA
  have hmapK : (K.subgroupOf A).map f = K.map (mk' Q0) := map_subgroupOf_comp_subtype _ hKA
  obtain ⟨hp, hcard, hact⟩ := prime_natCard_and_natCard_eq_pow_and_forall_conj_eq f h.prime
    (map_mk'_ne_bot h hQ0) hcopV h.normal_D h.isComplement'_subgroupOf
    (subgroupOf_ne_bot hDA h.D_ne_bot) (subgroupOf_ne_bot hKA h.K_ne_bot)
    h.inf_centralizer_subgroupOf
    (by rw [hmapD]; exact inf_centralizer_map_mk'_D_eq_bot h hQ0)
    (by
      intro k hk hk1
      have hz : (zpowers k).map f = (zpowers (k : X)).map (mk' Q0) := by
        rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers]
        rfl
      rw [hz, hmapK]
      exact inf_centralizer_map_mk'_singleton_eq h hQ0 (mem_subgroupOf.1 hk)
        fun hc => hk1 (Subtype.ext hc))
    (by
      rw [hmapK, inf_centralizer_map_mk'_K_eq h hQ0]
      exact natCard_map_mk'_Z h hQ0)
  have hKcard : Nat.card ↥(K.subgroupOf A) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKA).toEquiv
  refine ⟨hKcard ▸ hp, by rw [hcard, hKcard], ?_⟩
  rw [Subgroup.commutator_le]
  intro w hw x hx
  obtain ⟨y, hy, hyx⟩ := exists_mem_commutator_subgroupOf hDA hx
  have h1 : (QuotientGroup.mk x : X ⧸ Q0) * (QuotientGroup.mk w : X ⧸ Q0)
      * (QuotientGroup.mk x : X ⧸ Q0)⁻¹ = (QuotientGroup.mk w : X ⧸ Q0) := by
    have h0 := hact y hy (QuotientGroup.mk w) ⟨w, hw, rfl⟩
    rwa [show f y = (QuotientGroup.mk x : X ⧸ Q0) by rw [hf]; exact congrArg _ hyx] at h0
  have hcomm : Commute (QuotientGroup.mk w : X ⧸ Q0) (QuotientGroup.mk x : X ⧸ Q0) := by
    refine Commute.symm ?_
    calc (QuotientGroup.mk x : X ⧸ Q0) * (QuotientGroup.mk w : X ⧸ Q0)
        = (QuotientGroup.mk x : X ⧸ Q0) * (QuotientGroup.mk w : X ⧸ Q0)
          * (QuotientGroup.mk x : X ⧸ Q0)⁻¹ * (QuotientGroup.mk x : X ⧸ Q0) := by group
      _ = (QuotientGroup.mk w : X ⧸ Q0) * (QuotientGroup.mk x : X ⧸ Q0) := by rw [h1]
  refine (QuotientGroup.eq_one_iff _).1 ?_
  rw [show (QuotientGroup.mk ⁅w, x⁆ : X ⧸ Q0)
      = ⁅(QuotientGroup.mk w : X ⧸ Q0), (QuotientGroup.mk x : X ⧸ Q0)⁆ from
    map_commutatorElement (mk' Q0) w x]
  exact commutatorElement_eq_one_iff_commute.2 hcomm

theorem prime_natCard_K : (Nat.card ↥K).Prime :=
  (prime_natCard_K_and_natCard_map_mk'_Q_and_commutator_le h hQ0).1

theorem natCard_map_mk'_Q :
    haveI := normal_inf_centralizer h hQ0
    Nat.card ↥(Q.map (mk' (Q ⊓ centralizer (D : Set X)))) = q ^ Nat.card ↥K :=
  (prime_natCard_K_and_natCard_map_mk'_Q_and_commutator_le h hQ0).2.1

theorem natCard_quotient_subgroupOf_Q :
    Nat.card (↥Q ⧸ (Q ⊓ centralizer (D : Set X)).subgroupOf Q) = q ^ Nat.card ↥K := by
  have := normal_inf_centralizer h hQ0
  have hrel := Subgroup.relIndex_ker Q (mk' (Q ⊓ centralizer (D : Set X)))
  rw [QuotientGroup.ker_mk', natCard_map_mk'_Q h hQ0] at hrel
  rw [← hrel, Subgroup.relIndex, Subgroup.index_eq_card]

theorem commutator_commutator_le_inf_centralizer :
    ⁅Q, ⁅D, D⁆⁆ ≤ Q ⊓ centralizer (D : Set X) :=
  (prime_natCard_K_and_natCard_map_mk'_Q_and_commutator_le h hQ0).2.2

end IsPrimeFixedSectionSetup

end CFSG.FeitThompson
