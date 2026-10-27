module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique
open scoped commutatorElement

section Aut

variable {L : Type} [Group L]

@[expose] def fixedSubgroup (α : L ≃* L) : Subgroup L where
  carrier := {x | α x = x}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  one_mem' := by simp
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_inv, ha]

theorem mem_fixedSubgroup {α : L ≃* L} {x : L} : x ∈ fixedSubgroup α ↔ α x = x := Iff.rfl

@[expose] def IsInnerAut (α : L ≃* L) : Prop :=
  ∃ l : L, ∀ x : L, α x = l⁻¹ * x * l

@[expose] def IsTwoCentralInnerAut (α : L ≃* L) : Prop :=
  ∃ l : L, (∀ x : L, α x = l⁻¹ * x * l) ∧ (∃ x : L, α x ≠ x) ∧
    ∃ P : Sylow 2 L, ∀ p ∈ (P : Subgroup L), ⁅p, l⁆ ∈ Subgroup.center L

@[expose] def PermAction {n : ℕ} (α : L ≃* L)
    (φ : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin n)) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ x : L, ((φ (QuotientGroup.mk (α x)) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
    σ⁻¹ * ((φ (QuotientGroup.mk x) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) * σ

end Aut

section Datum

variable (L : Type) [Group L]

@[expose] def InvCaseA (α : L ≃* L) : Prop :=
  IsSimpleGroup L ∧ Lemma115LieCharTwo L ∧ IsInnerAut α

@[expose] def InvCaseB (α : L ≃* L) : Prop :=
  Subgroup.center L ≠ ⊥ ∧ Subgroup.center L = CFSG.pCore 2 L ∧
    IsL34OrG24 (L ⧸ CFSG.pCore 2 L) ∧ IsInnerAut α

@[expose] def InvCaseC (α : L ≃* L) : Prop :=
  ∃ (φ : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin 6)) (σ : Equiv.Perm (Fin 6)),
    (Nat.card (Subgroup.center L) = 1 ∨ Nat.card (Subgroup.center L) = 3) ∧ σ.IsSwap ∧
      PermAction α φ σ

@[expose] def InvCaseD (α : L ≃* L) : Prop :=
  ∃ (φ : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin 7)) (σ : Equiv.Perm (Fin 7)),
    (Nat.card (Subgroup.center L) = 1 ∨ Nat.card (Subgroup.center L) = 3) ∧
      σ.cycleType = {2, 2, 2} ∧ PermAction α φ σ

@[expose] def InvCaseE (α : L ≃* L) : Prop :=
  (StatedClassicalModel L .PSL 3 3 1 ∨
    ∃ p : ℕ, IsFermatOrMersennePrime p ∧ StatedClassicalModel L .PSL 2 p 1) ∧ IsInnerAut α

@[expose] def InvCaseF (α : L ≃* L) : Prop :=
  (∃ s : TauCeti.SporadicName, IsLemma115SporadicName s ∧
    Nonempty ((L ⧸ CFSG.pCore 2 L) ≃* NativeSporadic.Carrier s)) ∧ IsTwoCentralInnerAut α

@[expose] def InvCases (α : L ≃* L) : Prop :=
  InvCaseA L α ∨ InvCaseB L α ∨ InvCaseC L α ∨ InvCaseD L α ∨ InvCaseE L α ∨ InvCaseF L α

end Datum

structure InvDatum (L : Type) [Group L] [Finite L] (α : L ≃* L) : Prop where
  quasisimple : CFSG.IsQuasisimple L
  involutory : ∀ x : L, α (α x) = x
  nontrivial : ∃ x : L, x⁻¹ * α x ∉ Subgroup.center L
  sylow : ∃ P : Sylow 2 L, ∀ t ∈ (P : Subgroup L), α t = t
  inverts : ∀ y ∈ Subgroup.center L, Odd (orderOf y) → α y = y⁻¹
  charTwo : CharTwo (fixedSubgroup α)

section Translate

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}

theorem isSylowTwoOf_map_subtype (P : Sylow 2 L) :
    IsSylowTwoOf ((P : Subgroup L).map L.subtype) L := by
  refine ⟨Subgroup.map_subtype_le _, (P.isPGroup').map L.subtype, ?_⟩
  have h : ((P : Subgroup L).map L.subtype).subgroupOf L = (P : Subgroup L) :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  rw [h]
  exact P.not_dvd_index

variable {α : ↥L ≃* ↥L} (hα : ∀ y : L, ((α y : L) : G) = z⁻¹ * (y : G) * z)

omit [Finite G] in
include hα in
theorem inducesInner_of_isInnerAut (h : IsInnerAut α) : InducesInner z L := by
  obtain ⟨l, hl⟩ := h
  refine ⟨l, l.2, fun x hx => ?_⟩
  rw [← hα ⟨x, hx⟩, hl ⟨x, hx⟩]
  rfl

include hα in
theorem inducesTwoCentralInner_of_isTwoCentralInnerAut (h : IsTwoCentralInnerAut α) :
    InducesTwoCentralInner z L := by
  obtain ⟨l, hl, ⟨x, hx⟩, P, hP⟩ := h
  refine ⟨l, l.2, fun y hy => ?_, ⟨x, x.2, fun hxz => hx (Subtype.ext ?_)⟩, _,
    isSylowTwoOf_map_subtype P, ?_⟩
  · rw [← hα ⟨y, hy⟩, hl ⟨y, hy⟩]
    rfl
  · rw [hα x]
    exact hxz
  · rintro _ ⟨q, hq, rfl⟩ y hy
    have h1 := Subgroup.mem_center_iff.mp (hP q hq) ⟨y, hy⟩
    have h2 := congrArg Subtype.val h1
    simpa [commutatorElement_def] using h2

omit [Finite G] in
include hα in
theorem inducesPermAction_of_permAction {n : ℕ}
    {φ : (↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin n)} {σ : Equiv.Perm (Fin n)}
    (h : PermAction α φ σ) : InducesPermAction z L φ σ := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · have := (α ⟨x, hx⟩).2
    rwa [hα ⟨x, hx⟩] at this
  · have hyα : y = α x := Subtype.ext (by rw [hα x]; exact hy)
    rw [hyα]
    exact h x

include hα in
theorem Lemma115Cases.of_invCases (h : InvCases ↥L α) : Lemma115Cases L z := by
  rcases h with ⟨hs, hm, hi⟩ | ⟨hc, hcp, hm, hi⟩ | ⟨φ, σ, hZ, hσ, hp⟩ | ⟨φ, σ, hZ, hσ, hp⟩ |
    ⟨hm, hi⟩ | ⟨hm, hi⟩
  · exact Or.inl ⟨hs, hm, inducesInner_of_isInnerAut hα hi⟩
  · exact Or.inr (Or.inl ⟨hc, hcp, hm, inducesInner_of_isInnerAut hα hi⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨φ, σ, hZ, hσ, inducesPermAction_of_permAction hα hp⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨φ, σ, hZ, hσ, inducesPermAction_of_permAction hα hp⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hm, inducesInner_of_isInnerAut hα hi⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hm, inducesTwoCentralInner_of_isTwoCentralInnerAut hα hi⟩))))

end Translate

section Generic

variable {L : Type} [Group L] [Finite L] {α : L ≃* L}

omit [Finite L] in
theorem isPGroup_two_of_forall_odd_orderOf {C : Subgroup L}
    (h : ∀ y ∈ C, Odd (orderOf y) → y = 1) [Finite C] : IsPGroup 2 C := by
  apply IsPGroup.of_card (n := (Nat.card C).primeFactorsList.length)
  apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
  intro prime hprime hdvd
  by_contra hne
  have : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' prime hdvd
  have hyodd : Odd (orderOf (y : L)) := by
    rw [Subgroup.orderOf_coe, hy]
    exact hprime.odd_of_ne_two hne
  have hy1 : (y : L) = 1 := h y y.2 hyodd
  have horder : orderOf y = 1 := by
    rw [← Subgroup.orderOf_coe y, hy1, orderOf_one]
  exact hprime.ne_one (hy.symm.trans horder)

namespace InvDatum

theorem perfect (h : InvDatum L α) : Group.IsPerfect L := h.quasisimple.1

theorem simple_quotient (h : InvDatum L α) : IsSimpleGroup (L ⧸ Subgroup.center L) :=
  h.quasisimple.2.1

omit [Finite L] in
theorem eq_one_of_odd_center_of_inner {α : L ≃* L}
    (hinv : ∀ y ∈ Subgroup.center L, Odd (orderOf y) → α y = y⁻¹) (hi : IsInnerAut α) :
    ∀ y ∈ Subgroup.center L, Odd (orderOf y) → y = 1 := by
  obtain ⟨l, hl⟩ := hi
  intro y hy hodd
  have h1 : α y = y := by
    rw [hl y, mul_assoc, ← Subgroup.mem_center_iff.mp hy l, inv_mul_cancel_left]
  have h2 : y = y⁻¹ := by rw [← hinv y hy hodd, h1]
  have h3 : y ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [h2]
    exact inv_mul_cancel y
  have h4 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one h3
  rcases (Nat.dvd_prime Nat.prime_two).mp h4 with h5 | h5
  · exact orderOf_eq_one_iff.mp h5
  · rw [h5] at hodd
    exact absurd hodd (by decide)

theorem isPGroup_center_of_inner (h : InvDatum L α) (hi : IsInnerAut α) :
    IsPGroup 2 (Subgroup.center L) :=
  isPGroup_two_of_forall_odd_orderOf (eq_one_of_odd_center_of_inner h.inverts hi)

end InvDatum

theorem pCore_eq_center_of_isPGroup_center (hq : CFSG.IsQuasisimple L)
    (h2 : IsPGroup 2 (Subgroup.center L)) : CFSG.pCore 2 L = Subgroup.center L := by
  apply le_antisymm
  · rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq
      (N := CFSG.pCore 2 L) inferInstance with htop | hle
    · exfalso
      have hp : IsPGroup 2 L := by
        have := (CFSG.pCore_isPGroup (p := 2) (G := L))
        rw [htop] at this
        exact this.of_equiv Subgroup.topEquiv
      have hpq : IsPGroup 2 (L ⧸ Subgroup.center L) := hp.to_quotient _
      have hnil : Group.IsNilpotent (L ⧸ Subgroup.center L) := hpq.isNilpotent
      have hs := hq.2.1
      obtain ⟨a, b, hab⟩ := hq.2.2
      have hctr : Subgroup.center (L ⧸ Subgroup.center L) = ⊤ :=
        (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (L ⧸ Subgroup.center L))).resolve_left
          (Group.IsNilpotent.center_ne_bot _)
      exact hab ((Subgroup.mem_center_iff.mp (hctr ▸ Subgroup.mem_top a)) b).symm
    · exact hle
  · exact le_sSup ⟨inferInstance, h2⟩

namespace InvDatum

theorem isTwoCentralInnerAut_of_inner (h : InvDatum L α) (hi : IsInnerAut α) :
    IsTwoCentralInnerAut α := by
  obtain ⟨l, hl⟩ := hi
  obtain ⟨P, hP⟩ := h.sylow
  obtain ⟨x, hx⟩ := h.nontrivial
  refine ⟨l, hl, ⟨x, fun hxx => hx ?_⟩, P, fun p hp => ?_⟩
  · rw [hxx, inv_mul_cancel]
    exact Subgroup.one_mem _
  · have h1 : l⁻¹ * p * l = p := by rw [← hl p, hP p hp]
    have h2 : p * l = l * p := by
      calc p * l = l * (l⁻¹ * p * l) := by group
        _ = l * p := by rw [h1]
    rw [commutatorElement_eq_one_iff_mul_comm.mpr h2]
    exact Subgroup.one_mem _

end InvDatum

omit [Finite L] in
@[expose] noncomputable def quotAut (α : L ≃* L) :
    (L ⧸ Subgroup.center L) ≃* (L ⧸ Subgroup.center L) :=
  CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient α

omit [Finite L] in
@[simp] theorem quotAut_mk (α : L ≃* L) (x : L) :
    quotAut α (QuotientGroup.mk x) = QuotientGroup.mk (α x) :=
  CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk α x

namespace InvDatum

theorem quotAut_involutory (h : InvDatum L α) (y : L ⧸ Subgroup.center L) :
    quotAut α (quotAut α y) = y := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  rw [quotAut_mk, quotAut_mk, h.involutory]

theorem quotAut_nontrivial (h : InvDatum L α) : ∃ y : L ⧸ Subgroup.center L, quotAut α y ≠ y := by
  obtain ⟨x, hx⟩ := h.nontrivial
  refine ⟨QuotientGroup.mk x, fun hxx => hx ?_⟩
  rw [quotAut_mk, QuotientGroup.eq] at hxx
  simpa using Subgroup.inv_mem _ hxx

theorem quotAut_sylow (h : InvDatum L α) :
    ∃ P : Sylow 2 (L ⧸ Subgroup.center L), ∀ t ∈ (P : Subgroup (L ⧸ Subgroup.center L)),
      quotAut α t = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := h.sylow
  refine ⟨P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center L)), ?_⟩
  rw [Sylow.coe_mapSurjective]
  rintro _ ⟨t, ht, rfl⟩
  change quotAut α (QuotientGroup.mk t) = QuotientGroup.mk t
  rw [quotAut_mk, hP t ht]

theorem isInnerAut_of_quotAut_inner (h : InvDatum L α) (hk : IsInnerAut (quotAut α)) :
    IsInnerAut α := by
  have := h.perfect
  obtain ⟨k, hk⟩ := hk
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective k
  refine ⟨l, ?_⟩
  let β : L →* L := (MulAut.conj l).toMonoidHom.comp α.toMonoidHom
  have hcentral : ∀ x : L, x⁻¹ * β x ∈ Subgroup.center L := by
    intro x
    have h1 := hk (QuotientGroup.mk x)
    rw [quotAut_mk] at h1
    have h2 : (QuotientGroup.mk (x⁻¹ * (l * α x * l⁻¹)) : L ⧸ Subgroup.center L) = 1 := by
      have : (QuotientGroup.mk (l * α x * l⁻¹) : L ⧸ Subgroup.center L) = QuotientGroup.mk x := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1]
        group
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, this, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h2
  have hid : β = MonoidHom.id L :=
    CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement β hcentral
  intro x
  have h1 : l * α x * l⁻¹ = x := congrArg (fun f : L →* L => f x) hid
  calc α x = l⁻¹ * (l * α x * l⁻¹) * l := by group
    _ = l⁻¹ * x * l := by rw [h1]

end InvDatum

end Generic

end CFSG.QuasithinUnique.Ch1
