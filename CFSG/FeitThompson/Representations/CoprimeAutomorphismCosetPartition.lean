module

public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import CFSG.FeitThompson.Representations.CanonicalPiSetComponent
import Mathlib.Tactic.Group

open Pointwise

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CoprimeComponent

variable {G : Type*} [Group G] {H : Subgroup G} {a x h : G}

theorem mem_conjAct_smul_set_iff {S : Set G} :
    x ∈ ConjAct.toConjAct h • S ↔ h⁻¹ * x * h ∈ S := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, ← map_inv, ConjAct.toConjAct_smul, inv_inv]

theorem conjAct_smul_set_eq_conj_image (g : G) (S : Set G) :
    ConjAct.toConjAct g • S = MulAut.conj g '' S := by
  rw [← Set.image_smul]; rfl

theorem mem_normalizer_iff_conjAct_smul_eq {S : Set G} :
    h ∈ Subgroup.normalizer S ↔ ConjAct.toConjAct h • S = S := by
  rw [Subgroup.mem_normalizer_iff_conj_image_eq, conjAct_smul_set_eq_conj_image]

def centralizerCoset (H : Subgroup G) (a : G) : Set G :=
  ((H ⊓ Subgroup.centralizer {a} : Subgroup G) : Set G) * {a}

theorem mem_centralizerCoset_iff :
    x ∈ centralizerCoset H a ↔ x * a⁻¹ ∈ H ⊓ Subgroup.centralizer {a} := by
  simp only [centralizerCoset, Set.mul_singleton, Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨c, hc, rfl⟩; simpa using hc
  · exact fun hx => ⟨x * a⁻¹, hx, by group⟩

theorem self_mem_centralizerCoset (H : Subgroup G) (a : G) : a ∈ centralizerCoset H a := by
  simp [mem_centralizerCoset_iff]

theorem natCard_centralizerCoset (H : Subgroup G) (a : G) :
    Nat.card (centralizerCoset H a) = Nat.card (H ⊓ Subgroup.centralizer {a} : Subgroup G) := by
  rw [centralizerCoset, Set.mul_singleton, Nat.card_image_of_injective (mul_left_injective a)]
  rfl

private theorem finite_coe_inf_centralizer [Finite H] :
    (((H ⊓ Subgroup.centralizer {a} : Subgroup G) : Set G)).Finite :=
  Set.Finite.subset (Set.toFinite (H : Set G))
    (by exact_mod_cast inf_le_left (a := H) (b := Subgroup.centralizer {a}))

theorem finite_centralizerCoset [Finite H] : (centralizerCoset H a).Finite := by
  rw [centralizerCoset, Set.mul_singleton]
  exact Set.Finite.image _ finite_coe_inf_centralizer

theorem piComponent_eq_of_mem_centralizerCoset [Finite H]
    (hcop : (Nat.card H).Coprime (orderOf a)) (hfin : IsOfFinOrder a)
    (hx : x ∈ centralizerCoset H a) : piComponent {p : ℕ | p ∣ orderOf a} x = a := by
  set pi : Set ℕ := {p : ℕ | p ∣ orderOf a} with hpi
  rw [mem_centralizerCoset_iff] at hx
  obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.1 hx
  have hcomm : Commute a (x * a⁻¹) := (Subgroup.mem_centralizer_singleton_iff.1 hxC).symm
  have hxa : a * (x * a⁻¹) = x := by rw [hcomm.eq]; group
  have hA : IsPiNumber pi (orderOf a) :=
    isPiNumber_iff_forall_prime.2 ⟨hfin.orderOf_pos, fun _ _ hpd => hpd⟩
  have hdvd : orderOf (x * a⁻¹) ∣ Nat.card H := H.orderOf_dvd_natCard hxH
  have hC : IsPiPrimeNumber pi (orderOf (x * a⁻¹)) := by
    refine isPiPrimeNumber_iff_forall_prime.2 ⟨Nat.pos_of_ne_zero fun h0 => ?_,
      fun p hp hpd hppi => ?_⟩
    · rw [h0] at hdvd
      exact Nat.card_pos.ne' (Nat.eq_zero_of_zero_dvd hdvd)
    · have hg : p ∣ Nat.gcd (Nat.card H) (orderOf a) := Nat.dvd_gcd (hpd.trans hdvd) hppi
      rw [hcop] at hg
      exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one hg)
  rw [← hxa]
  exact piComponent_eq_of_commute hcomm hA hC

theorem mem_centralizer_of_not_disjoint [Finite H] (hcop : (Nat.card H).Coprime (orderOf a))
    (hfin : IsOfFinOrder a)
    (hd : ¬ Disjoint (ConjAct.toConjAct h • centralizerCoset H a) (centralizerCoset H a)) :
    h ∈ Subgroup.centralizer {a} := by
  obtain ⟨y, hy1, hy2⟩ := Set.not_disjoint_iff.1 hd
  rw [mem_conjAct_smul_set_iff] at hy1
  have e1 := piComponent_eq_of_mem_centralizerCoset hcop hfin hy1
  have e2 := piComponent_eq_of_mem_centralizerCoset hcop hfin hy2
  have key := piComponent_conj {p : ℕ | p ∣ orderOf a} h⁻¹ y
  rw [inv_inv, e1, e2] at key
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc h * a = h * (h⁻¹ * a * h) := by rw [← key]
    _ = a * h := by group

theorem smul_centralizerCoset_of_mem (hh : h ∈ H ⊓ Subgroup.centralizer {a}) :
    ConjAct.toConjAct h • centralizerCoset H a = centralizerCoset H a := by
  set C := H ⊓ Subgroup.centralizer {a} with hC
  have hcomm : Commute h a := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hh).2
  have hia : h * a⁻¹ = a⁻¹ * h := hcomm.inv_right.eq
  ext y
  rw [mem_conjAct_smul_set_iff, mem_centralizerCoset_iff, mem_centralizerCoset_iff, ← hC]
  have key : h⁻¹ * y * h * a⁻¹ = h⁻¹ * (y * a⁻¹) * h := by
    rw [mul_assoc (h⁻¹ * y) h a⁻¹, hia]; group
  rw [key]
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · simpa [mul_assoc] using C.mul_mem (C.mul_mem hh hz) (C.inv_mem hh)
  · simpa [mul_assoc] using C.mul_mem (C.mul_mem (C.inv_mem hh) hz) hh

theorem smul_centralizerCoset_eq_iff [Finite H] (hcop : (Nat.card H).Coprime (orderOf a))
    (hfin : IsOfFinOrder a) (hh : h ∈ H) :
    ConjAct.toConjAct h • centralizerCoset H a = centralizerCoset H a ↔
      h ∈ H ⊓ Subgroup.centralizer {a} := by
  refine ⟨fun heq => Subgroup.mem_inf.2 ⟨hh, ?_⟩, smul_centralizerCoset_of_mem⟩
  refine mem_centralizer_of_not_disjoint hcop hfin ?_
  rw [heq]
  exact Set.not_disjoint_iff.2 ⟨a, self_mem_centralizerCoset H a, self_mem_centralizerCoset H a⟩

theorem inf_normalizer_centralizerCoset [Finite H] (hcop : (Nat.card H).Coprime (orderOf a))
    (hfin : IsOfFinOrder a) :
    H ⊓ Subgroup.normalizer (centralizerCoset H a) = H ⊓ Subgroup.centralizer {a} := by
  ext g
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  refine ⟨fun ⟨hg, hn⟩ => ⟨hg, ?_⟩, fun ⟨hg, hc⟩ => ⟨hg, ?_⟩⟩
  · exact (Subgroup.mem_inf.1 ((smul_centralizerCoset_eq_iff hcop hfin hg).1
      (mem_normalizer_iff_conjAct_smul_eq.1 hn))).2
  · exact mem_normalizer_iff_conjAct_smul_eq.2
      (smul_centralizerCoset_of_mem (Subgroup.mem_inf.2 ⟨hg, hc⟩))

def centralizerCosetConjugates (H : Subgroup G) (a : G) : Set (Set G) :=
  Set.range fun g : H => ConjAct.toConjAct (g : G) • centralizerCoset H a

theorem mem_centralizerCosetConjugates_iff {S : Set G} :
    S ∈ centralizerCosetConjugates H a ↔
      ∃ g ∈ H, ConjAct.toConjAct g • centralizerCoset H a = S := by
  simp only [centralizerCosetConjugates, Set.mem_range, Subtype.exists, exists_prop]

theorem self_mem_centralizerCosetConjugates (H : Subgroup G) (a : G) :
    centralizerCoset H a ∈ centralizerCosetConjugates H a :=
  mem_centralizerCosetConjugates_iff.2 ⟨1, H.one_mem, by simp⟩

theorem finite_centralizerCosetConjugates [Finite H] :
    (centralizerCosetConjugates H a).Finite :=
  Set.finite_range _

theorem natCard_of_mem_centralizerCosetConjugates {S : Set G}
    (hS : S ∈ centralizerCosetConjugates H a) :
    Nat.card S = Nat.card (H ⊓ Subgroup.centralizer {a} : Subgroup G) := by
  obtain ⟨g, -, rfl⟩ := mem_centralizerCosetConjugates_iff.1 hS
  rw [Set.natCard_smul_set, natCard_centralizerCoset]

theorem nonempty_of_mem_centralizerCosetConjugates {S : Set G}
    (hS : S ∈ centralizerCosetConjugates H a) : S.Nonempty := by
  obtain ⟨g, -, rfl⟩ := mem_centralizerCosetConjugates_iff.1 hS
  exact ⟨_, Set.smul_mem_smul_set (self_mem_centralizerCoset H a)⟩

theorem finite_of_mem_centralizerCosetConjugates [Finite H] {S : Set G}
    (hS : S ∈ centralizerCosetConjugates H a) : S.Finite := by
  obtain ⟨g, -, rfl⟩ := mem_centralizerCosetConjugates_iff.1 hS
  exact Set.Finite.smul_set finite_centralizerCoset

theorem smul_centralizerCoset_eq_of_not_disjoint [Finite H]
    (hcop : (Nat.card H).Coprime (orderOf a)) (hfin : IsOfFinOrder a) {g₁ g₂ : G}
    (hg₁ : g₁ ∈ H) (hg₂ : g₂ ∈ H)
    (hd : ¬ Disjoint (ConjAct.toConjAct g₁ • centralizerCoset H a)
      (ConjAct.toConjAct g₂ • centralizerCoset H a)) :
    ConjAct.toConjAct g₁ • centralizerCoset H a
      = ConjAct.toConjAct g₂ • centralizerCoset H a := by
  obtain ⟨y, hy1, hy2⟩ := Set.not_disjoint_iff.1 hd
  rw [mem_conjAct_smul_set_iff] at hy1 hy2
  have hnd : ¬ Disjoint (ConjAct.toConjAct (g₂⁻¹ * g₁) • centralizerCoset H a)
      (centralizerCoset H a) := by
    rw [Set.not_disjoint_iff]
    refine ⟨g₂⁻¹ * g₁ * (g₁⁻¹ * y * g₁) * (g₂⁻¹ * g₁)⁻¹, ?_, ?_⟩
    · rw [mem_conjAct_smul_set_iff]; simpa [mul_assoc] using hy1
    · convert hy2 using 1; group
  have hmem : g₂⁻¹ * g₁ ∈ H ⊓ Subgroup.centralizer {a} :=
    Subgroup.mem_inf.2 ⟨H.mul_mem (H.inv_mem hg₂) hg₁,
      mem_centralizer_of_not_disjoint hcop hfin hnd⟩
  have hEq := smul_centralizerCoset_of_mem hmem
  rw [map_mul, map_inv, mul_smul, inv_smul_eq_iff] at hEq
  exact hEq

theorem pairwiseDisjoint_centralizerCosetConjugates [Finite H]
    (hcop : (Nat.card H).Coprime (orderOf a)) (hfin : IsOfFinOrder a) :
    (centralizerCosetConjugates H a).PairwiseDisjoint id := by
  intro S hS T hT hST
  obtain ⟨g₁, hg₁, rfl⟩ := mem_centralizerCosetConjugates_iff.1 hS
  obtain ⟨g₂, hg₂, rfl⟩ := mem_centralizerCosetConjugates_iff.1 hT
  refine not_not.1 fun hd => hST ?_
  exact smul_centralizerCoset_eq_of_not_disjoint hcop hfin hg₁ hg₂ hd

theorem natCard_centralizerCosetConjugates [Finite H]
    (hcop : (Nat.card H).Coprime (orderOf a)) (hfin : IsOfFinOrder a) :
    Nat.card (centralizerCosetConjugates H a) = (Subgroup.centralizer {a}).relIndex H := by
  set C := H ⊓ Subgroup.centralizer {a} with hCdef
  set f : H → Set G := fun g => ConjAct.toConjAct (g : G) • centralizerCoset H a with hf
  have hker : ∀ g₁ g₂ : H, Setoid.ker f g₁ g₂ ↔ QuotientGroup.leftRel (C.subgroupOf H) g₁ g₂ := by
    intro g₁ g₂
    rw [Setoid.ker_def, QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    have hmul : ((g₁⁻¹ * g₂ : H) : G) = (g₁ : G)⁻¹ * (g₂ : G) := by push_cast; rfl
    rw [hmul, ← smul_centralizerCoset_eq_iff (a := a) hcop hfin
      (H.mul_mem (H.inv_mem g₁.2) g₂.2), map_mul, map_inv, mul_smul, inv_smul_eq_iff]
    exact ⟨fun hE => hE.symm, fun hE => hE.symm⟩
  calc Nat.card (centralizerCosetConjugates H a) = Nat.card (Quotient (Setoid.ker f)) :=
        (Nat.card_congr (Setoid.quotientKerEquivRange f)).symm
    _ = Nat.card (Quotient (QuotientGroup.leftRel (C.subgroupOf H))) :=
        Nat.card_congr (Quotient.congrRight hker)
    _ = (C.subgroupOf H).index := (Subgroup.index_eq_card _).symm
    _ = (Subgroup.centralizer {a}).relIndex H := by
        rw [hCdef, Subgroup.inf_subgroupOf_left]; rfl

theorem natCard_sUnion_of_pairwiseDisjoint {α : Type*} {T : Set (Set α)} (hT : T.Finite)
    (hfin : ∀ S ∈ T, (S : Set α).Finite) (hd : T.PairwiseDisjoint id) {c : ℕ}
    (hc : ∀ S ∈ T, Nat.card S = c) : Nat.card (⋃₀ T : Set α) = Nat.card T * c := by
  classical
  have hd' : T.PairwiseDisjoint (fun S : Set α => S) := hd
  rw [Set.sUnion_eq_biUnion, Nat.card_congr (Set.biUnionEqSigmaOfDisjoint hd')]
  have : Fintype T := hT.fintype
  have : ∀ S : T, Finite (S : Set α) := fun S => (hfin S.1 S.2).to_subtype
  rw [Nat.card_sigma, Finset.sum_congr rfl fun S _ => hc S.1 S.2]
  simp [Nat.card_eq_fintype_card]

theorem relIndex_centralizer_mul_natCard_inf (H : Subgroup G) (a : G) :
    (Subgroup.centralizer {a}).relIndex H
      * Nat.card (H ⊓ Subgroup.centralizer {a} : Subgroup G) = Nat.card H := by
  have h1 : Nat.card ((H ⊓ Subgroup.centralizer {a}).subgroupOf H)
      = Nat.card (H ⊓ Subgroup.centralizer {a} : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : _ ≤ H)).toEquiv
  have h2 := Subgroup.index_mul_card ((H ⊓ Subgroup.centralizer {a}).subgroupOf H)
  rw [h1] at h2
  rw [← h2, Subgroup.inf_subgroupOf_left]
  rfl

theorem natCard_coe_mul_singleton (H : Subgroup G) (a : G) :
    Nat.card ((H : Set G) * ({a} : Set G)) = Nat.card H := by
  rw [Set.mul_singleton, Nat.card_image_of_injective (mul_left_injective a)]
  rfl

theorem finite_coe_mul_singleton [Finite H] : ((H : Set G) * ({a} : Set G)).Finite := by
  rw [Set.mul_singleton]
  exact Set.Finite.image _ (Set.toFinite (H : Set G))

theorem subset_of_mem_centralizerCosetConjugates (ha : a ∈ Subgroup.normalizer (H : Set G))
    {S : Set G} (hS : S ∈ centralizerCosetConjugates H a) : S ⊆ (H : Set G) * {a} := by
  obtain ⟨g, hg, rfl⟩ := mem_centralizerCosetConjugates_iff.1 hS
  intro y hy
  rw [mem_conjAct_smul_set_iff] at hy
  have hc : g⁻¹ * y * g * a⁻¹ ∈ H := (Subgroup.mem_inf.1 (mem_centralizerCoset_iff.1 hy)).1
  rw [Set.mul_singleton]
  refine ⟨y * a⁻¹, ?_, by group⟩
  have h2 : a * g⁻¹ * a⁻¹ ∈ H := by
    simpa [mul_assoc] using (Subgroup.mem_normalizer_iff.1 ha g⁻¹).1 (H.inv_mem hg)
  simpa [mul_assoc] using H.mul_mem (H.mul_mem hg hc) h2

theorem sUnion_centralizerCosetConjugates [Finite H]
    (hcop : (Nat.card H).Coprime (orderOf a)) (hfin : IsOfFinOrder a)
    (ha : a ∈ Subgroup.normalizer (H : Set G)) :
    ⋃₀ centralizerCosetConjugates H a = (H : Set G) * {a} := by
  have hsub : ⋃₀ centralizerCosetConjugates H a ⊆ (H : Set G) * {a} :=
    Set.sUnion_subset fun _ hS => subset_of_mem_centralizerCosetConjugates ha hS
  refine Set.eq_of_subset_of_ncard_le hsub ?_ finite_coe_mul_singleton
  have hcount : Nat.card (⋃₀ centralizerCosetConjugates H a) = Nat.card H := by
    rw [natCard_sUnion_of_pairwiseDisjoint finite_centralizerCosetConjugates
        (fun _ hS => finite_of_mem_centralizerCosetConjugates hS)
        (pairwiseDisjoint_centralizerCosetConjugates hcop hfin)
        (fun _ hS => natCard_of_mem_centralizerCosetConjugates hS),
      natCard_centralizerCosetConjugates hcop hfin, relIndex_centralizer_mul_natCard_inf]
  have : ((H : Set G) * {a}).ncard = Nat.card H := natCard_coe_mul_singleton H a
  rw [this]
  exact hcount.ge

theorem existsUnique_mem_centralizerCosetConjugates [Finite H]
    (hcop : (Nat.card H).Coprime (orderOf a)) (hfin : IsOfFinOrder a)
    (ha : a ∈ Subgroup.normalizer (H : Set G)) (hx : x ∈ (H : Set G) * {a}) :
    ∃! S, S ∈ centralizerCosetConjugates H a ∧ x ∈ S := by
  rw [← sUnion_centralizerCosetConjugates hcop hfin ha, Set.mem_sUnion] at hx
  obtain ⟨S, hS, hxS⟩ := hx
  refine ⟨S, ⟨hS, hxS⟩, fun T ⟨hT, hxT⟩ => ?_⟩
  by_contra hne
  exact Set.disjoint_left.1
    (pairwiseDisjoint_centralizerCosetConjugates hcop hfin hT hS hne) hxT hxS

end

end CFSG.FeitThompson
