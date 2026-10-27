module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductDefs
public import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.FieldCaseSylow
public import CFSG.Quasithin.H13.J4Core

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.SignalizerFunctorTheorem (sectionAction sectionAction_mk coe_sectionConjAut
  sectionAction_mk_eq_iff)
open scoped commutatorElement

namespace ProductToolboxAux.Core

section Abstract

variable {E : Type*} [Group E] [Finite E] [CFSG.IsElementaryAbelian 2 E]

theorem inv_eq_self (x : E) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_isElementaryAbelian_two x)

@[expose] def fixSub (α : MulAut E) : Subgroup E where
  carrier := {x | α x = x}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  one_mem' := map_one α
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

theorem mem_fixSub {α : MulAut E} {x : E} : x ∈ fixSub α ↔ α x = x := Iff.rfl

@[expose] def coboundary (α : MulAut E) : E →* E :=
  MonoidHom.mk' (fun x => x⁻¹ * α x) (inv_mul_apply_mul α)

theorem coboundary_apply (α : MulAut E) (x : E) : coboundary α x = x⁻¹ * α x := rfl

theorem ker_coboundary (α : MulAut E) : (coboundary α).ker = fixSub α := by
  ext x
  rw [MonoidHom.mem_ker, coboundary_apply, inv_mul_eq_one, eq_comm]
  rfl

theorem range_coboundary_le (α : MulAut E) (hα : ∀ x, α (α x) = x) :
    (coboundary α).range ≤ fixSub α := by
  rintro _ ⟨x, rfl⟩
  rw [mem_fixSub, coboundary_apply, map_mul, map_inv, hα, inv_eq_self (α x), inv_eq_self x,
    mul_comm' (α x) x]

theorem card_eq_card_fixSub_mul (α : MulAut E) :
    Nat.card E = Nat.card (fixSub α) * Nat.card (coboundary α).range := by
  rw [← ker_coboundary α, ← card_mul_index (coboundary α).ker, index_ker]

theorem card_le_card_fixSub_sq (α : MulAut E) (hα : ∀ x, α (α x) = x) :
    Nat.card E ≤ Nat.card (fixSub α) ^ 2 := by
  rw [card_eq_card_fixSub_mul α, sq]
  exact Nat.mul_le_mul_left _ (card_le_of_le (range_coboundary_le α hα))

theorem card_eq_card_fixSub_sq_iff (α : MulAut E) (hα : ∀ x, α (α x) = x) :
    Nat.card E = Nat.card (fixSub α) ^ 2 ↔ fixSub α ≤ (coboundary α).range := by
  have hpos : 0 < Nat.card (fixSub α) := Nat.card_pos
  rw [card_eq_card_fixSub_mul α, sq]
  constructor
  · intro h
    have h2 : Nat.card (coboundary α).range = Nat.card (fixSub α) :=
      Nat.eq_of_mul_eq_mul_left hpos h
    exact (eq_of_le_of_card_ge (range_coboundary_le α hα) h2.ge).ge
  · intro h
    have h2 := le_antisymm (range_coboundary_le α hα) h
    rw [h2]

end Abstract

end ProductToolboxAux.Core

section Generic

variable {Γ : Type*} [Group Γ] [Finite Γ]

structure IsElemSection (A B : Subgroup Γ) : Prop where
  le : B ≤ A
  mul_self_mem : ∀ x ∈ A, x * x ∈ B
  commutator_mem : ∀ x ∈ A, ∀ y ∈ A, x * y * x⁻¹ * y⁻¹ ∈ B

@[expose] def H1Zero (τ : Γ) (N : Subgroup Γ) : Prop :=
  ∀ n ∈ N, n * (τ * n * τ⁻¹) = 1 → ∃ m ∈ N, n = m⁻¹ * (τ * m * τ⁻¹)

@[expose] def H1ZeroSec (τ : Γ) (N M : Subgroup Γ) : Prop :=
  ∀ n ∈ N, n * (τ * n * τ⁻¹) ∈ M → ∃ m ∈ N, m * n * (τ * m * τ⁻¹)⁻¹ ∈ M

namespace ProductToolboxAux.Core

section Sec

variable {A B : Subgroup Γ}

theorem normal_subgroupOf (hAB : IsElemSection A B) : (B.subgroupOf A).Normal where
  conj_mem n hn g := by
    rw [mem_subgroupOf] at hn ⊢
    have h1 := mul_mem (hAB.commutator_mem g.1 g.2 n.1 n.2) hn
    have e : ((g * n * g⁻¹ : A) : Γ) = (g : Γ) * n * (g : Γ)⁻¹ * (n : Γ)⁻¹ * n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [e]
    exact h1

theorem isElementaryAbelian_section (hAB : IsElemSection A B) [(B.subgroupOf A).Normal] :
    CFSG.IsElementaryAbelian 2 (A ⧸ B.subgroupOf A) where
  is_comm := ⟨fun u v => by
    induction u using QuotientGroup.induction_on with | H x => ?_
    induction v using QuotientGroup.induction_on with | H y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
    have := hAB.commutator_mem (y : Γ)⁻¹ (inv_mem y.2) (x : Γ)⁻¹ (inv_mem x.2)
    simpa [mul_assoc] using this⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun u => by
    induction u using QuotientGroup.induction_on with | H x => ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf, pow_two]
    exact hAB.mul_self_mem x x.2

theorem le_normalizer (hAB : IsElemSection A B) : A ≤ normalizer (B : Set Γ) :=
  (normal_subgroupOf_iff_le_normalizer hAB.le).1 (normal_subgroupOf hAB)

variable {τ : Γ}

theorem eq_one_or_eq_of_mem_zpowers (hτ : τ * τ = 1) {b : Γ} (hb : b ∈ zpowers τ) :
    b = 1 ∨ b = τ := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul, zpow_two, hτ, one_zpow]
  · right
    rw [hm, zpow_add_one, zpow_mul, zpow_two, hτ, one_zpow, one_mul]

theorem mem_centralizerMod_zpowers_iff (hAB : IsElemSection A B) (hτ : τ * τ = 1)
    (hτB : τ ∈ normalizer (B : Set Γ)) {a : Γ} (ha : a ∈ A) :
    a ∈ centralizerMod B (zpowers τ) ↔ a⁻¹ * (τ * a * τ⁻¹) ∈ B := by
  have haN : a ∈ normalizer (B : Set Γ) := le_normalizer hAB ha
  rw [mem_centralizerMod_iff]
  constructor
  · rintro ⟨-, h⟩
    have h1 := h τ (mem_zpowers τ) hτB
    have h2 := (mem_normalizer_iff.1 (inv_mem haN) _).1 (inv_mem h1)
    rwa [show a⁻¹ * (a * τ * a⁻¹ * τ⁻¹)⁻¹ * a⁻¹⁻¹ = a⁻¹ * (τ * a * τ⁻¹) by group] at h2
  · intro h
    refine ⟨haN, fun b hb hbN => ?_⟩
    rcases eq_one_or_eq_of_mem_zpowers hτ hb with rfl | rfl
    · simpa using one_mem B
    · have h1 := (mem_normalizer_iff.1 haN _).1 (inv_mem h)
      rwa [show a * (a⁻¹ * (b * a * b⁻¹))⁻¹ * a⁻¹ = a * b * a⁻¹ * b⁻¹ by group] at h1

theorem mem_inf_centralizerMod_zpowers_iff (hAB : IsElemSection A B) (hτ : τ * τ = 1)
    (hτB : τ ∈ normalizer (B : Set Γ)) {a : Γ} :
    a ∈ A ⊓ centralizerMod B (zpowers τ) ↔ a ∈ A ∧ a⁻¹ * (τ * a * τ⁻¹) ∈ B := by
  rw [mem_inf]
  exact and_congr_right fun ha => mem_centralizerMod_zpowers_iff hAB hτ hτB ha

theorem le_inf_centralizerMod_zpowers (hAB : IsElemSection A B) (hτ : τ * τ = 1)
    (hτB : τ ∈ normalizer (B : Set Γ)) : B ≤ A ⊓ centralizerMod B (zpowers τ) := fun b hb =>
  (mem_inf_centralizerMod_zpowers_iff hAB hτ hτB).2 ⟨hAB.le hb,
    mul_mem (inv_mem hb) ((mem_normalizer_iff.1 hτB b).1 hb)⟩

end Sec

section Bridge

variable {A B : Subgroup Γ} {τ : Γ}

theorem card_section (A B : Subgroup Γ) : Nat.card (A ⧸ B.subgroupOf A) = B.relIndex A := rfl

theorem alpha_alpha [(B.subgroupOf A).Normal] (hτ : τ * τ = 1)
    (hτA : τ ∈ normalizer (A : Set Γ)) (hτB : τ ∈ normalizer (B : Set Γ))
    (q : A ⧸ B.subgroupOf A) :
    sectionRightConj hτA hτB (sectionRightConj hτA hτB q) = q := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  let k' : A := ⟨τ⁻¹ * k * τ, inv_mul_mul_mem_of_mem_normalizer hτA k.2⟩
  rw [sectionRightConj_mk hτA hτB k k' rfl, sectionRightConj_mk hτA hτB k' k ?_]
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  change (k : Γ) = τ⁻¹ * (τ⁻¹ * k * τ) * τ
  rw [hτi]
  calc (k : Γ) = (τ * τ) * k * (τ * τ) := by rw [hτ, one_mul, mul_one]
    _ = τ * (τ * k * τ) * τ := by group

theorem alpha_fixed_iff [(B.subgroupOf A).Normal]
    (hτA : τ ∈ normalizer (A : Set Γ)) (hτB : τ ∈ normalizer (B : Set Γ)) (k : A) :
    sectionRightConj hτA hτB (QuotientGroup.mk k) = (QuotientGroup.mk k : A ⧸ B.subgroupOf A) ↔
      (k : Γ)⁻¹ * (τ * k * τ⁻¹) ∈ B := by
  rw [sectionRightConj_mk_eq_iff]
  have e : τ * (τ⁻¹ * (k : Γ)⁻¹ * τ * k) * τ⁻¹ = (k : Γ)⁻¹ * (τ * k * τ⁻¹) := by group
  rw [← e]
  exact mem_normalizer_iff.1 hτB _

theorem card_fixSub [(B.subgroupOf A).Normal] [CFSG.IsElementaryAbelian 2 (A ⧸ B.subgroupOf A)]
    (hAB : IsElemSection A B) (hτ : τ * τ = 1) (hτA : τ ∈ normalizer (A : Set Γ))
    (hτB : τ ∈ normalizer (B : Set Γ)) :
    Nat.card (fixSub (sectionRightConj hτA hτB)) =
      B.relIndex (A ⊓ centralizerMod B (zpowers τ)) := by
  set C := A ⊓ centralizerMod B (zpowers τ) with hC
  have hCA : C ≤ A := inf_le_left
  let ψ : C.subgroupOf A →* A ⧸ B.subgroupOf A :=
    (QuotientGroup.mk' (B.subgroupOf A)).comp (C.subgroupOf A).subtype
  have hrange : ψ.range = fixSub (sectionRightConj hτA hτB) := by
    ext q
    constructor
    · rintro ⟨c, rfl⟩
      show sectionRightConj hτA hτB (QuotientGroup.mk (c : A)) = QuotientGroup.mk (c : A)
      rw [alpha_fixed_iff hτA hτB]
      exact ((mem_inf_centralizerMod_zpowers_iff hAB hτ hτB).1 (mem_subgroupOf.1 c.2)).2
    · intro hq
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
      have hk := (alpha_fixed_iff hτA hτB k).1 hq
      exact ⟨⟨k, mem_subgroupOf.2 ((mem_inf_centralizerMod_zpowers_iff hAB hτ hτB).2
        ⟨k.2, hk⟩)⟩, rfl⟩
  have hker : ψ.ker = (B.subgroupOf A).subgroupOf (C.subgroupOf A) := by
    ext c
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    show (QuotientGroup.mk (c : A) : A ⧸ B.subgroupOf A) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
  rw [← hrange, ← index_ker, hker]
  exact relIndex_subgroupOf hCA

theorem isFreeSection_iff [(B.subgroupOf A).Normal]
    [CFSG.IsElementaryAbelian 2 (A ⧸ B.subgroupOf A)]
    (hAB : IsElemSection A B) (hτ : τ * τ = 1) (hτA : τ ∈ normalizer (A : Set Γ))
    (hτB : τ ∈ normalizer (B : Set Γ)) :
    IsFreeSection τ A B ↔ Nat.card (A ⧸ B.subgroupOf A) =
      Nat.card (fixSub (sectionRightConj hτA hτB)) ^ 2 := by
  rw [IsFreeSection, card_section, card_fixSub hAB hτ hτA hτB]

theorem alpha_mk [(B.subgroupOf A).Normal] (hτ : τ * τ = 1)
    (hτA : τ ∈ normalizer (A : Set Γ)) (hτB : τ ∈ normalizer (B : Set Γ)) {k : Γ} (hk : k ∈ A)
    (hk' : τ * k * τ⁻¹ ∈ A) :
    sectionRightConj hτA hτB (QuotientGroup.mk (⟨k, hk⟩ : A)) =
      (QuotientGroup.mk (⟨τ * k * τ⁻¹, hk'⟩ : A) : A ⧸ B.subgroupOf A) := by
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  exact sectionRightConj_mk hτA hτB ⟨k, hk⟩ ⟨τ * k * τ⁻¹, hk'⟩ (by simp only [hτi])

end Bridge

section Ext

variable {A A' B : Subgroup Γ} {τ : Γ}

theorem lift_sec (hAB : IsElemSection A B) (hτ : τ * τ = 1) (hτB : τ ∈ normalizer (B : Set Γ))
    (hH1 : H1ZeroSec τ A' B) (hA'A : A' ≤ A) :
    ∀ a ∈ A, a⁻¹ * (τ * a * τ⁻¹) ∈ A' → a ∈ (A ⊓ centralizerMod B (zpowers τ)) ⊔ A' := by
  intro a ha hn
  have hτi : τ⁻¹ * τ⁻¹ = 1 := by rw [← mul_inv_rev, hτ, inv_one]
  have h1 : a⁻¹ * (τ * a * τ⁻¹) * (τ * (a⁻¹ * (τ * a * τ⁻¹)) * τ⁻¹) = 1 := by
    calc a⁻¹ * (τ * a * τ⁻¹) * (τ * (a⁻¹ * (τ * a * τ⁻¹)) * τ⁻¹)
        = a⁻¹ * (τ * τ) * a * (τ⁻¹ * τ⁻¹) := by group
      _ = 1 := by rw [hτ, hτi]; group
  obtain ⟨m, hm, hmB⟩ := hH1 _ hn (by rw [h1]; exact one_mem B)
  have hc : a * m⁻¹ ∈ A ⊓ centralizerMod B (zpowers τ) := by
    refine (mem_inf_centralizerMod_zpowers_iff hAB hτ hτB).2 ⟨mul_mem ha (inv_mem (hA'A hm)), ?_⟩
    have e : (a * m⁻¹)⁻¹ * (τ * (a * m⁻¹) * τ⁻¹) =
        m * (a⁻¹ * (τ * a * τ⁻¹)) * (τ * m * τ⁻¹)⁻¹ := by group
    rw [e]
    exact hmB
  have e : a = (a * m⁻¹) * m := by group
  rw [e]
  exact mul_mem_sup hc hm

theorem relIndex_sup_eq {X : Subgroup Γ} (hXA : X ≤ A) (hA'A : A' ≤ A)
    (hA' : (A'.subgroupOf A).Normal) : A'.relIndex (X ⊔ A') = (A' ⊓ X).relIndex X := by
  have h := relIndex_sup_right (H := X.subgroupOf A) (K := A'.subgroupOf A)
  rw [← subgroupOf_sup hXA hA'A, relIndex_subgroupOf (sup_le hXA hA'A),
    relIndex_subgroupOf hXA] at h
  rw [h, inf_relIndex_right]

end Ext

section Maschke

variable {A B J : Subgroup Γ}

theorem mem_centralizerMod_iff_of_le (hAB : IsElemSection A B) (hJB : J ≤ normalizer (B : Set Γ))
    {a : Γ} (ha : a ∈ A) :
    a ∈ centralizerMod B J ↔ ∀ j ∈ J, a⁻¹ * (j * a * j⁻¹) ∈ B := by
  have haN : a ∈ normalizer (B : Set Γ) := le_normalizer hAB ha
  rw [mem_centralizerMod_iff]
  constructor
  · rintro ⟨-, h⟩ j hj
    have h1 := h j hj (hJB hj)
    have h2 := (mem_normalizer_iff.1 (inv_mem haN) _).1 (inv_mem h1)
    rwa [show a⁻¹ * (a * j * a⁻¹ * j⁻¹)⁻¹ * a⁻¹⁻¹ = a⁻¹ * (j * a * j⁻¹) by group] at h2
  · intro h
    refine ⟨haN, fun b hb hbN => ?_⟩
    have h1 := (mem_normalizer_iff.1 haN _).1 (inv_mem (h b hb))
    rwa [show a * (a⁻¹ * (b * a * b⁻¹))⁻¹ * a⁻¹ = a * b * a⁻¹ * b⁻¹ by group] at h1

theorem mem_inf_centralizerMod_iff_of_le (hAB : IsElemSection A B)
    (hJB : J ≤ normalizer (B : Set Γ)) {a : Γ} :
    a ∈ A ⊓ centralizerMod B J ↔ a ∈ A ∧ ∀ j ∈ J, a⁻¹ * (j * a * j⁻¹) ∈ B := by
  rw [mem_inf]
  exact and_congr_right fun ha => mem_centralizerMod_iff_of_le hAB hJB ha

theorem sectionAction_apply_mk [(B.subgroupOf A).Normal] (hJA : J ≤ normalizer (A : Set Γ))
    (hJB : J ≤ normalizer (B : Set Γ)) (j : J) {k : Γ} (hk : k ∈ A)
    (hk' : (j : Γ) * k * (j : Γ)⁻¹ ∈ A) :
    sectionAction hJA hJB j (QuotientGroup.mk (⟨k, hk⟩ : A)) =
      (QuotientGroup.mk (⟨(j : Γ) * k * (j : Γ)⁻¹, hk'⟩ : A) : A ⧸ B.subgroupOf A) := by
  rw [sectionAction_mk]
  congr 1
  exact Subtype.ext (coe_sectionConjAut hJA j ⟨k, hk⟩)

theorem maschke_section (hAB : IsElemSection A B) (hJA : J ≤ normalizer (A : Set Γ))
    (hJB : J ≤ normalizer (B : Set Γ)) (hJ : Odd (Nat.card J)) :
    A = (A ⊓ centralizerMod B J) ⊔ (⁅A, J⁆ ⊔ B) ∧
      (A ⊓ centralizerMod B J) ⊓ (⁅A, J⁆ ⊔ B) = B := by
  haveI := normal_subgroupOf hAB
  haveI := isElementaryAbelian_section hAB
  letI : MulDistribMulAction ↥J (A ⧸ B.subgroupOf A) :=
    MulDistribMulAction.compHom (A ⧸ B.subgroupOf A) (sectionAction hJA hJB)
  have hcop : (Nat.card J).Coprime (Nat.card (A ⧸ B.subgroupOf A)) := by
    obtain ⟨n, hn⟩ := (CFSG.IsElementaryAbelian.isPGroup 2 (A ⧸ B.subgroupOf A)).exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n (Nat.coprime_two_right.2 hJ)
  have hcompl :=
    CFSG.isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := A ⧸ B.subgroupOf A) (A := ↥J) inferInstance hcop inferInstance
  set S := ⁅A, J⁆ ⊔ B with hS
  have hconj : ∀ (j : J) {k : Γ}, k ∈ A → (j : Γ) * k * (j : Γ)⁻¹ ∈ A := fun j k hk =>
    (mem_normalizer_iff.1 (hJA j.2) k).1 hk
  have hBS : B ≤ S := le_sup_right
  have hfix : ∀ k : A, (QuotientGroup.mk k : A ⧸ B.subgroupOf A) ∈
      CFSG.fixedPointSubgroup ↥J (A ⧸ B.subgroupOf A) ↔ (k : Γ) ∈ A ⊓ centralizerMod B J := by
    intro k
    rw [mem_inf_centralizerMod_iff_of_le hAB hJB]
    simp only [CFSG.fixedPointSubgroup, FixedPoints.mem_subgroup]
    constructor
    · intro h
      exact ⟨k.2, fun j hj => (sectionAction_mk_eq_iff hJA hJB ⟨j, hj⟩ k).1 (h ⟨j, hj⟩)⟩
    · rintro ⟨-, h⟩ j
      exact (sectionAction_mk_eq_iff hJA hJB j k).2 (h j j.2)
  have hcom1 : S ≤ ((CFSG.commutatorAction ↥J (A ⧸ B.subgroupOf A)).comap
      (QuotientGroup.mk' (B.subgroupOf A))).map A.subtype := by
    refine sup_le (Subgroup.commutator_le.2 fun a ha j hj => ?_) (fun b hb => ?_)
    · have hja : (j : Γ) * a⁻¹ * (j : Γ)⁻¹ ∈ A := hconj ⟨j, hj⟩ (inv_mem ha)
      have he : (⁅a, j⁆ : Γ) = a * ((j : Γ) * a⁻¹ * (j : Γ)⁻¹) := by
        simp only [commutatorElement_def]; group
      have hk : (⁅a, j⁆ : Γ) ∈ A := by rw [he]; exact mul_mem ha hja
      refine ⟨⟨⁅a, j⁆, hk⟩, ?_, rfl⟩
      have hgen : (QuotientGroup.mk (⟨a⁻¹, inv_mem ha⟩ : A) : A ⧸ B.subgroupOf A)⁻¹ *
          ((⟨j, hj⟩ : J) • (QuotientGroup.mk (⟨a⁻¹, inv_mem ha⟩ : A) : A ⧸ B.subgroupOf A)) ∈
          CFSG.commutatorAction ↥J (A ⧸ B.subgroupOf A) :=
        Subgroup.subset_closure ⟨⟨j, hj⟩, _, mem_top _, rfl⟩
      have hsm : (⟨j, hj⟩ : J) • (QuotientGroup.mk (⟨a⁻¹, inv_mem ha⟩ : A) :
          A ⧸ B.subgroupOf A) = QuotientGroup.mk ⟨(j : Γ) * a⁻¹ * (j : Γ)⁻¹, hja⟩ :=
        sectionAction_apply_mk hJA hJB ⟨j, hj⟩ (inv_mem ha) hja
      rw [hsm, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] at hgen
      have e2 : (⟨a⁻¹, inv_mem ha⟩ : A)⁻¹ * ⟨(j : Γ) * a⁻¹ * (j : Γ)⁻¹, hja⟩ = ⟨⁅a, j⁆, hk⟩ :=
        Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]; rw [he])
      rw [e2] at hgen
      exact hgen
    · refine ⟨⟨b, hAB.le hb⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_comap, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff (N := B.subgroupOf A) (⟨b, hAB.le hb⟩ : A)).2
          (mem_subgroupOf.2 hb)]
      exact one_mem _
  have hcom2 : ∀ k : A, (QuotientGroup.mk k : A ⧸ B.subgroupOf A) ∈
      CFSG.commutatorAction ↥J (A ⧸ B.subgroupOf A) → (k : Γ) ∈ S := by
    intro k hk
    have hle : CFSG.commutatorAction ↥J (A ⧸ B.subgroupOf A) ≤
        (S.subgroupOf A).map (QuotientGroup.mk' (B.subgroupOf A)) := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨j, x, -, rfl⟩
      obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective x
      have hk'' : (j : Γ) * k' * (j : Γ)⁻¹ ∈ A := hconj j k'.2
      have hsm : j • (QuotientGroup.mk k' : A ⧸ B.subgroupOf A) =
          QuotientGroup.mk ⟨(j : Γ) * k' * (j : Γ)⁻¹, hk''⟩ :=
        sectionAction_apply_mk hJA hJB j k'.2 hk''
      refine ⟨k'⁻¹ * ⟨(j : Γ) * k' * (j : Γ)⁻¹, hk''⟩, ?_, ?_⟩
      · rw [SetLike.mem_coe, mem_subgroupOf]
        have he : (⁅(k' : Γ)⁻¹, (j : Γ)⁆ : Γ) = (k' : Γ)⁻¹ * ((j : Γ) * k' * (j : Γ)⁻¹) := by
          simp only [commutatorElement_def]; group
        have hm : (⁅(k' : Γ)⁻¹, (j : Γ)⁆ : Γ) ∈ ⁅A, J⁆ :=
          Subgroup.commutator_mem_commutator (inv_mem k'.2) j.2
        have : ((k'⁻¹ * ⟨(j : Γ) * k' * (j : Γ)⁻¹, hk''⟩ : A) : Γ) =
            (k' : Γ)⁻¹ * ((j : Γ) * k' * (j : Γ)⁻¹) := rfl
        rw [this, ← he]
        exact mem_sup_left hm
      · rw [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hsm]
    obtain ⟨k₂, hk₂, hkk₂⟩ := hle hk
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf] at hkk₂
    have hk₂' : (k₂ : Γ) ∈ S := mem_subgroupOf.1 hk₂
    have e : (k : Γ) = (k₂ : Γ) * (((k₂ : Γ))⁻¹ * k) := by group
    rw [e]
    exact mul_mem hk₂' (hBS (by simpa using hkk₂))
  have hSA : S ≤ A := sup_le (Subgroup.commutator_le.2 fun a ha j hj => by
    have hja : (j : Γ) * a⁻¹ * (j : Γ)⁻¹ ∈ A := hconj ⟨j, hj⟩ (inv_mem ha)
    have he : (⁅a, j⁆ : Γ) = a * ((j : Γ) * a⁻¹ * (j : Γ)⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [he]; exact mul_mem ha hja) hAB.le
  have hBC : B ≤ A ⊓ centralizerMod B J := fun b hb =>
    (mem_inf_centralizerMod_iff_of_le hAB hJB).2 ⟨hAB.le hb, fun j hj =>
      mul_mem (inv_mem hb) ((mem_normalizer_iff.1 (hJB hj) b).1 hb)⟩
  refine ⟨le_antisymm (fun a ha => ?_) (sup_le inf_le_left hSA), ?_⟩
  · have h1 : (QuotientGroup.mk (⟨a, ha⟩ : A) : A ⧸ B.subgroupOf A) ∈
        CFSG.fixedPointSubgroup ↥J (A ⧸ B.subgroupOf A) ⊔
          CFSG.commutatorAction ↥J (A ⧸ B.subgroupOf A) := by
      rw [hcompl.sup_eq_top]; exact mem_top _
    obtain ⟨fq, hf, cq, hc, hfc⟩ := mem_sup_of_normal_right.1 h1
    obtain ⟨f', rfl⟩ := QuotientGroup.mk_surjective fq
    obtain ⟨c', rfl⟩ := QuotientGroup.mk_surjective cq
    have hf' : (f' : Γ) ∈ A ⊓ centralizerMod B J := (hfix f').1 hf
    have hc' : (c' : Γ) ∈ S := hcom2 c' hc
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf] at hfc
    have e : a = ((f' : Γ) * c') * (((f' : Γ) * c')⁻¹ * a) := by group
    rw [e]
    exact mul_mem (mul_mem (mem_sup_left hf') (mem_sup_right hc'))
      (mem_sup_right (hBS (by simpa using hfc)))
  · refine le_antisymm (fun x hx => ?_) (le_inf hBC hBS)
    obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
    have hxA : x ∈ A := hSA hx2
    have h1 : (QuotientGroup.mk (⟨x, hxA⟩ : A) : A ⧸ B.subgroupOf A) ∈
        CFSG.fixedPointSubgroup ↥J (A ⧸ B.subgroupOf A) ⊓
          CFSG.commutatorAction ↥J (A ⧸ B.subgroupOf A) := by
      refine ⟨(hfix ⟨x, hxA⟩).2 hx1, ?_⟩
      obtain ⟨k, hk, hkx⟩ := hcom1 hx2
      have : k = ⟨x, hxA⟩ := Subtype.ext hkx
      rw [this] at hk
      exact hk
    rw [hcompl.disjoint.eq_bot, mem_bot] at h1
    exact mem_subgroupOf.1 ((QuotientGroup.eq_one_iff (N := B.subgroupOf A) (⟨x, hxA⟩ : A)).1 h1)

theorem le_inf_centralizerMod_of_le (hAB : IsElemSection A B) (hJB : J ≤ normalizer (B : Set Γ)) :
    B ≤ A ⊓ centralizerMod B J := fun b hb =>
  (mem_inf_centralizerMod_iff_of_le hAB hJB).2 ⟨hAB.le hb, fun j hj =>
    mul_mem (inv_mem hb) ((mem_normalizer_iff.1 (hJB hj) b).1 hb)⟩

theorem commutator_sup_le (hAB : IsElemSection A B) (hJA : J ≤ normalizer (A : Set Γ)) :
    ⁅A, J⁆ ⊔ B ≤ A := sup_le (Subgroup.commutator_le.2 fun a ha j hj => by
  have hja : j * a⁻¹ * j⁻¹ ∈ A := (mem_normalizer_iff.1 (hJA hj) _).1 (inv_mem ha)
  have he : (⁅a, j⁆ : Γ) = a * (j * a⁻¹ * j⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [he]; exact mul_mem ha hja) hAB.le

theorem isElemSection_sub {X : Subgroup Γ} (hAB : IsElemSection A B) (hBX : B ≤ X)
    (hXA : X ≤ A) : IsElemSection X B :=
  ⟨hBX, fun x hx => hAB.mul_self_mem x (hXA hx),
    fun x hx y hy => hAB.commutator_mem x (hXA hx) y (hXA hy)⟩

theorem isElemSection_quot {A' : Subgroup Γ} (hAB : IsElemSection A B) (hBA' : B ≤ A')
    (hA'A : A' ≤ A) : IsElemSection A A' :=
  ⟨hA'A, fun x hx => hBA' (hAB.mul_self_mem x hx),
    fun x hx y hy => hBA' (hAB.commutator_mem x hx y hy)⟩

theorem relIndex_eq_mul {U V : Subgroup Γ} (hAB : IsElemSection A B) (hBV : B ≤ V)
    (hUA : U ≤ A) (hVA : V ≤ A) (hsup : U ⊔ V = A) (hinf : U ⊓ V = B) :
    B.relIndex A = B.relIndex U * B.relIndex V := by
  have h := relIndex_sup_eq hUA hVA (normal_subgroupOf (isElemSection_quot hAB hBV hVA))
  rw [hsup, inf_comm, hinf] at h
  rw [← relIndex_mul_relIndex B V A hBV hVA, h, mul_comm]

section Comm

variable {A B J : Subgroup Γ} {τ : Γ}

theorem mem_normalizer_inf_centralizerMod (hAB : IsElemSection A B)
    (hJB : J ≤ normalizer (B : Set Γ)) (hτA : τ ∈ normalizer (A : Set Γ))
    (hτB : τ ∈ normalizer (B : Set Γ)) (hJτ : J ≤ centralizer ({τ} : Set Γ)) :
    τ ∈ normalizer ((A ⊓ centralizerMod B J : Subgroup Γ) : Set Γ) := by
  refine mem_normalizer_fintype fun x hx => ?_
  obtain ⟨hxA, hxJ⟩ := (mem_inf_centralizerMod_iff_of_le hAB hJB).1 hx
  refine (mem_inf_centralizerMod_iff_of_le hAB hJB).2 ⟨(mem_normalizer_iff.1 hτA x).1 hxA,
    fun j hj => ?_⟩
  have hjτ : j * τ = τ * j := mem_centralizer_singleton_iff.1 (hJτ hj)
  have e : j * (τ * x * τ⁻¹) * j⁻¹ = τ * (j * x * j⁻¹) * τ⁻¹ := by
    calc j * (τ * x * τ⁻¹) * j⁻¹ = (j * τ) * x * (j * τ)⁻¹ := by group
      _ = (τ * j) * x * (τ * j)⁻¹ := by rw [hjτ]
      _ = τ * (j * x * j⁻¹) * τ⁻¹ := by group
  have e2 : (τ * x * τ⁻¹)⁻¹ * (j * (τ * x * τ⁻¹) * j⁻¹) = τ * (x⁻¹ * (j * x * j⁻¹)) * τ⁻¹ := by
    rw [e]; group
  rw [e2]
  exact (mem_normalizer_iff.1 hτB _).1 (hxJ j hj)

theorem mem_normalizer_commutator_sup (hτA : τ ∈ normalizer (A : Set Γ))
    (hτB : τ ∈ normalizer (B : Set Γ)) (hJτ : J ≤ centralizer ({τ} : Set Γ)) :
    τ ∈ normalizer ((⁅A, J⁆ ⊔ B : Subgroup Γ) : Set Γ) := by
  refine mem_normalizer_fintype fun x hx => ?_
  have hle : ⁅A, J⁆ ⊔ B ≤ (⁅A, J⁆ ⊔ B).comap (MulAut.conj τ).toMonoidHom := by
    refine sup_le (Subgroup.commutator_le.2 fun a ha j hj => ?_) (fun b hb => ?_)
    · have hjτ : τ * j * τ⁻¹ = j := by
        have := mem_centralizer_singleton_iff.1 (hJτ hj)
        rw [← this]; group
      have e : τ * (⁅a, j⁆ : Γ) * τ⁻¹ = ⁅τ * a * τ⁻¹, j⁆ := by
        calc τ * (⁅a, j⁆ : Γ) * τ⁻¹ = (τ * a * τ⁻¹) * (τ * j * τ⁻¹) * (τ * a * τ⁻¹)⁻¹ *
              (τ * j * τ⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
          _ = ⁅τ * a * τ⁻¹, j⁆ := by rw [hjτ]; simp only [commutatorElement_def]
      rw [mem_comap]
      show τ * (⁅a, j⁆ : Γ) * τ⁻¹ ∈ _
      rw [e]
      exact mem_sup_left (Subgroup.commutator_mem_commutator ((mem_normalizer_iff.1 hτA a).1 ha) hj)
    · rw [mem_comap]
      exact mem_sup_right ((mem_normalizer_iff.1 hτB b).1 hb)
  exact hle hx

end Comm

end Maschke

end ProductToolboxAux.Core

open ProductToolboxAux.Core

theorem T1_card_le {A B : Subgroup Γ} (hAB : IsElemSection A B) {τ : Γ} (hτ : τ * τ = 1)
    (hτA : τ ∈ normalizer (A : Set Γ)) (hτB : τ ∈ normalizer (B : Set Γ)) :
    B.relIndex A ≤ (B.relIndex (A ⊓ centralizerMod B (zpowers τ))) ^ 2 := by
  haveI := normal_subgroupOf hAB
  haveI := isElementaryAbelian_section hAB
  rw [← card_section, ← card_fixSub hAB hτ hτA hτB]
  exact card_le_card_fixSub_sq _ (alpha_alpha hτ hτA hτB)

theorem T1_h1_zero {A B : Subgroup Γ} (hAB : IsElemSection A B) {τ : Γ} (hτ : τ * τ = 1)
    (hτA : τ ∈ normalizer (A : Set Γ)) (hτB : τ ∈ normalizer (B : Set Γ))
    (hfree : IsFreeSection τ A B) : H1ZeroSec τ A B := by
  haveI := normal_subgroupOf hAB
  haveI := isElementaryAbelian_section hAB
  have hα := alpha_alpha hτ hτA hτB
  have hle := (card_eq_card_fixSub_sq_iff _ hα).1
    ((isFreeSection_iff hAB hτ hτA hτB).1 hfree)
  intro n hn hnB
  have hn' : τ * n * τ⁻¹ ∈ A := (mem_normalizer_iff.1 hτA n).1 hn
  have hq : (QuotientGroup.mk (⟨n, hn⟩ : A) : A ⧸ B.subgroupOf A) ∈
      fixSub (sectionRightConj hτA hτB) := by
    rw [mem_fixSub, alpha_fixed_iff hτA hτB]
    have h1 := mul_mem (inv_mem (hAB.mul_self_mem n hn)) hnB
    rwa [show (n * n)⁻¹ * (n * (τ * n * τ⁻¹)) = n⁻¹ * (τ * n * τ⁻¹) by group] at h1
  obtain ⟨y, hy⟩ := hle hq
  obtain ⟨⟨m, hm⟩, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨m, hm, ?_⟩
  have hm' : τ * m * τ⁻¹ ∈ A := (mem_normalizer_iff.1 hτA m).1 hm
  have hy' : (QuotientGroup.mk (⟨m, hm⟩ : A) : A ⧸ B.subgroupOf A)⁻¹ *
      QuotientGroup.mk (⟨τ * m * τ⁻¹, hm'⟩ : A) = QuotientGroup.mk (⟨n, hn⟩ : A) := by
    rw [← alpha_mk hτ hτA hτB hm hm']
    exact hy
  have h1 : (QuotientGroup.mk ((⟨m, hm⟩ : A) * ⟨n, hn⟩ * (⟨τ * m * τ⁻¹, hm'⟩ : A)⁻¹) :
      A ⧸ B.subgroupOf A) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hy']
    group
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
  exact h1

theorem T1_extension {A A' B : Subgroup Γ} (hAB : IsElemSection A B) (hA'B : B ≤ A')
    (hAA' : A' ≤ A) {τ : Γ} (hτ : τ * τ = 1) (hτA : τ ∈ normalizer (A : Set Γ))
    (hτA' : τ ∈ normalizer (A' : Set Γ)) (hτB : τ ∈ normalizer (B : Set Γ))
    (h₁ : IsFreeSection τ A' B) (h₂ : IsFreeSection τ A A') : IsFreeSection τ A B := by
  have hA'B' : IsElemSection A' B := ⟨hA'B, fun x hx => hAB.mul_self_mem x (hAA' hx),
    fun x hx y hy => hAB.commutator_mem x (hAA' hx) y (hAA' hy)⟩
  have hAA'' : IsElemSection A A' := ⟨hAA', fun x hx => hA'B (hAB.mul_self_mem x hx),
    fun x hx y hy => hA'B (hAB.commutator_mem x hx y hy)⟩
  have hH1 := T1_h1_zero hA'B' hτ hτA' hτB h₁
  set X := A ⊓ centralizerMod B (zpowers τ) with hX
  set Y := A' ⊓ centralizerMod B (zpowers τ) with hY
  set Z := A ⊓ centralizerMod A' (zpowers τ) with hZ
  have hXA : X ≤ A := inf_le_left
  have hYX : Y ≤ X := inf_le_inf_right _ hAA'
  have hBY : B ≤ Y := le_inf_centralizerMod_zpowers hA'B' hτ hτB
  have hZ' : Z = X ⊔ A' := by
    refine le_antisymm (fun z hz => ?_) (sup_le (fun x hx => ?_) (fun a' ha' => ?_))
    · obtain ⟨hzA, hzc⟩ := (mem_inf_centralizerMod_zpowers_iff hAA'' hτ hτA').1 hz
      exact lift_sec hAB hτ hτB hH1 hAA' z hzA hzc
    · obtain ⟨hxA, hxc⟩ := (mem_inf_centralizerMod_zpowers_iff hAB hτ hτB).1 hx
      exact (mem_inf_centralizerMod_zpowers_iff hAA'' hτ hτA').2 ⟨hxA, hA'B hxc⟩
    · exact (mem_inf_centralizerMod_zpowers_iff hAA'' hτ hτA').2 ⟨hAA' ha',
        mul_mem (inv_mem ha') ((mem_normalizer_iff.1 hτA' a').1 ha')⟩
  have hYX' : Y = A' ⊓ X := by
    ext x
    simp only [hY, hX, mem_inf]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, hAA' h1, h2⟩, fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩⟩
  have hsec : B.relIndex X = B.relIndex Y * A'.relIndex Z := by
    rw [← relIndex_mul_relIndex B Y X hBY hYX, hZ', relIndex_sup_eq hXA hAA'
      (normal_subgroupOf hAA''), hYX']
  have h1 : B.relIndex A' = (B.relIndex Y) ^ 2 := h₁
  have h2 : A'.relIndex A = (A'.relIndex Z) ^ 2 := h₂
  show B.relIndex A = (B.relIndex X) ^ 2
  rw [← relIndex_mul_relIndex B A' A hA'B hAA', h1, h2, hsec]
  ring

theorem T2_lift {A N : Subgroup Γ} {τ : Γ} (hτ : τ * τ = 1) (hNA : N ≤ A)
    (hAN : A ≤ normalizer (N : Set Γ)) (hτA : τ ∈ normalizer (A : Set Γ))
    (hτN : τ ∈ normalizer (N : Set Γ)) (hH1 : H1Zero τ N) :
    ∀ a ∈ A, a⁻¹ * (τ * a * τ⁻¹) ∈ N → a ∈ (A ⊓ centralizer ({τ} : Set Γ)) ⊔ N := by
  intro a ha hn
  have hτi : τ⁻¹ * τ⁻¹ = 1 := by rw [← mul_inv_rev, hτ, inv_one]
  have h1 : a⁻¹ * (τ * a * τ⁻¹) * (τ * (a⁻¹ * (τ * a * τ⁻¹)) * τ⁻¹) = 1 := by
    calc a⁻¹ * (τ * a * τ⁻¹) * (τ * (a⁻¹ * (τ * a * τ⁻¹)) * τ⁻¹)
        = a⁻¹ * (τ * τ) * a * (τ⁻¹ * τ⁻¹) := by group
      _ = 1 := by rw [hτ, hτi]; group
  obtain ⟨m, hm, hmn⟩ := hH1 _ hn h1
  have h2 : τ * a = a * m⁻¹ * τ * m := by
    calc τ * a = a * (a⁻¹ * (τ * a * τ⁻¹)) * τ := by group
      _ = a * (m⁻¹ * (τ * m * τ⁻¹)) * τ := by rw [hmn]
      _ = a * m⁻¹ * τ * m := by group
  have hc : a * m⁻¹ ∈ A ⊓ centralizer ({τ} : Set Γ) := by
    refine mem_inf.2 ⟨mul_mem ha (inv_mem (hNA hm)), ?_⟩
    rw [mem_centralizer_singleton_iff]
    symm
    calc τ * (a * m⁻¹) = (τ * a) * m⁻¹ := by group
      _ = (a * m⁻¹ * τ * m) * m⁻¹ := by rw [h2]
      _ = a * m⁻¹ * τ := by group
  have e : a = (a * m⁻¹) * m := by group
  rw [e]
  exact mul_mem_sup hc hm

theorem T2_h1_zero {N M : Subgroup Γ} {τ : Γ} (hτ : τ * τ = 1) (hMN : M ≤ N)
    (hNM : N ≤ normalizer (M : Set Γ)) (hτN : τ ∈ normalizer (N : Set Γ))
    (hτM : τ ∈ normalizer (M : Set Γ)) (hM : H1Zero τ M) (hNM' : H1ZeroSec τ N M) :
    H1Zero τ N := by
  intro n hn hn1
  have hτi : τ⁻¹ * τ⁻¹ = 1 := by rw [← mul_inv_rev, hτ, inv_one]
  obtain ⟨m, hm, hmM⟩ := hNM' n hn (by rw [hn1]; exact one_mem M)
  have h1 : (m * n * (τ * m * τ⁻¹)⁻¹) * (τ * (m * n * (τ * m * τ⁻¹)⁻¹) * τ⁻¹) = 1 := by
    calc (m * n * (τ * m * τ⁻¹)⁻¹) * (τ * (m * n * (τ * m * τ⁻¹)⁻¹) * τ⁻¹)
        = m * (n * (τ * n * τ⁻¹)) * (τ * τ) * m⁻¹ * (τ⁻¹ * τ⁻¹) := by group
      _ = 1 := by rw [hn1, hτ, hτi]; group
  obtain ⟨k, hk, hkn⟩ := hM _ hmM h1
  refine ⟨k * m, mul_mem (hMN hk) hm, ?_⟩
  calc n = m⁻¹ * (m * n * (τ * m * τ⁻¹)⁻¹) * (τ * m * τ⁻¹) := by group
    _ = m⁻¹ * (k⁻¹ * (τ * k * τ⁻¹)) * (τ * m * τ⁻¹) := by rw [hkn]
    _ = (k * m)⁻¹ * (τ * (k * m) * τ⁻¹) := by group

theorem T3_fixed {A B J : Subgroup Γ} (hAB : IsElemSection A B) {τ : Γ} (hτ : τ * τ = 1)
    (hτA : τ ∈ normalizer (A : Set Γ)) (hτB : τ ∈ normalizer (B : Set Γ))
    (hfree : IsFreeSection τ A B) (hJ : Odd (Nat.card J)) (hJτ : J ≤ centralizer ({τ} : Set Γ))
    (hJA : J ≤ normalizer (A : Set Γ)) (hJB : J ≤ normalizer (B : Set Γ)) :
    A = (A ⊓ centralizerMod B J) ⊔ (⁅A, J⁆ ⊔ B) ∧
      (A ⊓ centralizerMod B J) ⊓ (⁅A, J⁆ ⊔ B) = B ∧ IsFreeSection τ (A ⊓ centralizerMod B J) B := by
  obtain ⟨hsup, hinf⟩ := maschke_section hAB hJA hJB hJ
  refine ⟨hsup, hinf, ?_⟩
  set C := A ⊓ centralizerMod B J with hC
  set S := ⁅A, J⁆ ⊔ B with hS
  set Zt := centralizerMod B (zpowers τ) with hZt
  set XA := A ⊓ Zt with hXA
  set XC := C ⊓ Zt with hXC
  set XS := S ⊓ Zt with hXS
  have hBC : B ≤ C := le_inf_centralizerMod_of_le hAB hJB
  have hBS : B ≤ S := le_sup_right
  have hSA : S ≤ A := commutator_sup_le hAB hJA
  have hCA : C ≤ A := inf_le_left
  have hBXA : B ≤ XA := le_inf_centralizerMod_zpowers hAB hτ hτB
  have hBZ : B ≤ Zt := hBXA.trans inf_le_right
  have hAC : IsElemSection C B := isElemSection_sub hAB hBC hCA
  have hAS : IsElemSection S B := isElemSection_sub hAB hBS hSA
  have hAX : IsElemSection XA B := isElemSection_sub hAB hBXA inf_le_left
  have hτC := mem_normalizer_inf_centralizerMod hAB hJB hτA hτB hJτ
  have hτS := mem_normalizer_commutator_sup (J := J) hτA hτB hJτ
  have hJX : J ≤ normalizer (XA : Set Γ) := by
    intro j hj
    refine mem_normalizer_fintype fun x hx => ?_
    obtain ⟨hxA, hxZ⟩ := (mem_inf_centralizerMod_zpowers_iff hAB hτ hτB).1 hx
    refine (mem_inf_centralizerMod_zpowers_iff hAB hτ hτB).2
      ⟨(mem_normalizer_iff.1 (hJA hj) x).1 hxA, ?_⟩
    have hjτ : j * τ = τ * j := mem_centralizer_singleton_iff.1 (hJτ hj)
    have e1 : τ * (j * x * j⁻¹) * τ⁻¹ = j * (τ * x * τ⁻¹) * j⁻¹ := by
      calc τ * (j * x * j⁻¹) * τ⁻¹ = (τ * j) * x * (τ * j)⁻¹ := by group
        _ = (j * τ) * x * (j * τ)⁻¹ := by rw [hjτ]
        _ = j * (τ * x * τ⁻¹) * j⁻¹ := by group
    have e : (j * x * j⁻¹)⁻¹ * (τ * (j * x * j⁻¹) * τ⁻¹) = j * (x⁻¹ * (τ * x * τ⁻¹)) * j⁻¹ := by
      rw [e1]; group
    rw [e]
    exact (mem_normalizer_iff.1 (hJB hj) _).1 hxZ
  obtain ⟨hXsup, -⟩ := maschke_section hAX hJX hJB hJ
  have hXAdec : XA = XC ⊔ XS := by
    refine le_antisymm ?_ (sup_le (inf_le_inf_right _ hCA) (inf_le_inf_right _ hSA))
    have hXJ : ⁅XA, J⁆ ⊔ B ≤ XA := commutator_sup_le hAX hJX
    calc XA = (XA ⊓ centralizerMod B J) ⊔ (⁅XA, J⁆ ⊔ B) := hXsup
      _ ≤ XC ⊔ XS := by
        refine sup_le_sup (fun x hx => ?_) (sup_le (le_inf ((commutator_mono_left inf_le_left).trans
          le_sup_left) ((le_sup_left.trans hXJ).trans inf_le_right)) (le_inf hBS hBZ))
        obtain ⟨⟨hxA, hxZ⟩, hxJ⟩ := mem_inf.1 hx
        exact ⟨mem_inf.2 ⟨hxA, hxJ⟩, hxZ⟩
  have hXinf : XC ⊓ XS = B :=
    le_antisymm ((inf_le_inf inf_le_left inf_le_left).trans hinf.le)
      (le_inf (le_inf hBC hBZ) (le_inf hBS hBZ))
  have h1 : B.relIndex A = B.relIndex C * B.relIndex S :=
    relIndex_eq_mul hAB hBS hCA hSA hsup.symm hinf
  have h2 : B.relIndex XA = B.relIndex XC * B.relIndex XS :=
    relIndex_eq_mul hAX (le_inf hBS hBZ) (inf_le_inf_right _ hCA) (inf_le_inf_right _ hSA)
      hXAdec.symm hXinf
  have hc1 : B.relIndex C ≤ (B.relIndex XC) ^ 2 := T1_card_le hAC hτ hτC hτB
  have hc2 : B.relIndex S ≤ (B.relIndex XS) ^ 2 := T1_card_le hAS hτ hτS hτB
  have hf : B.relIndex A = (B.relIndex XA) ^ 2 := hfree
  have hbpos : 0 < B.relIndex S := by rw [← card_section]; exact Nat.card_pos
  show B.relIndex C = (B.relIndex XC) ^ 2
  by_contra hne
  have hlt : B.relIndex C < (B.relIndex XC) ^ 2 := lt_of_le_of_ne hc1 hne
  have h3 : B.relIndex C * B.relIndex S < (B.relIndex XC) ^ 2 * B.relIndex S :=
    Nat.mul_lt_mul_of_pos_right hlt hbpos
  have h4 : (B.relIndex XC) ^ 2 * B.relIndex S ≤ (B.relIndex XC) ^ 2 * (B.relIndex XS) ^ 2 :=
    Nat.mul_le_mul_left _ hc2
  have h5 : B.relIndex C * B.relIndex S = (B.relIndex XC * B.relIndex XS) ^ 2 := by
    rw [← h1, hf, h2]
  rw [mul_pow] at h5
  omega

end Generic

section P03

open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

set_option hygiene false in
local macro "layer_ctx_P03" : tactic => `(tactic| (
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  have h59e := h.yamadaY₂_eq d hlay
  have h520 := h.yamada_5_20 d hlay
  have h5221 := h.yamada_5_22_1 d hlay
  have h521 := h.yamada_5_21 d hlay))

namespace ProductToolboxAux.P03

theorem leviShort_le_of_normalized {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)
    {N : Subgroup X} (hN : ∀ g ∈ d.leviShort, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hx : d.x₁ 1 ∈ N) :
    d.leviShort ≤ N := by
  have := d.finite
  set φ := d.leviShortEquiv
  have hNn : (N.subgroupOf d.leviShort).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hN g g.2 n hn⟩
  set K := (N.subgroupOf d.leviShort).comap φ.symm.toMonoidHom
  have hKn : K.Normal := hNn.comap _
  have hq2 := d.two_le_q
  have hcard : 8 ≤ Nat.card d.Γ := by
    rw [d.card_Γ]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq2 3
  have hQ := CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 2 d.Γ
    le_rfl (Or.inr (by omega)) (Or.inr (by omega))
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hKn with htop | hcen
  · intro g hg
    have h1 : φ ⟨g, hg⟩ ∈ K := htop ▸ mem_top _
    have h2 : φ.symm (φ ⟨g, hg⟩) ∈ N.subgroupOf d.leviShort := h1
    rwa [MulEquiv.symm_apply_apply, mem_subgroupOf] at h2
  · exfalso
    have h1 : φ ⟨d.x₁ 1, d.x₁_mem_leviShort 1⟩ ∈ K := by
      show φ.symm (φ ⟨d.x₁ 1, d.x₁_mem_leviShort 1⟩) ∈ N.subgroupOf d.leviShort
      rw [MulEquiv.symm_apply_apply, mem_subgroupOf]
      exact hx
    have h2 := hcen h1
    rw [TrialityD4Data.center_SL_two_eq_bot_D4, mem_bot] at h2
    have h3 : (⟨d.x₁ 1, d.x₁_mem_leviShort 1⟩ : d.leviShort) = 1 :=
      φ.injective (h2.trans (map_one φ).symm)
    have h4 : d.x₁ 1 = d.x₁ 0 := (congrArg Subtype.val h3).trans d.x₁_zero.symm
    exact one_ne_zero (d.x₁_injective h4)

theorem M₁_le_M₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaM₁ d t ≤ yamadaM₂ d t := by
  layer_ctx_P03
  intro x hx
  obtain ⟨hxL₂, hxS₁⟩ := mem_inf.1 hx
  have hV₁S₁ : yamadaV₁ d t ≤ centralizer (yamadaS₁ d t : Set G) := by
    rw [← h.yamada_5_7 d hlay]
    exact inf_le_right
  have hxC : x ∈ centralizer (yamadaV₁ d t : Set G) := le_centralizer_iff.1 hV₁S₁ hxS₁
  have hM₂C : yamadaM₂ d t ≤ centralizer (yamadaV₁ d t : Set G) := by
    rw [h.yamadaM₂_eq_inf_centralizer d h591 h592]
    exact inf_le_right.trans (Subgroup.centralizer_le (le_sup_left : yamadaV₁ d t ≤ yamadaY₂ d t))
  have htM₂ : t ∈ normalizer (yamadaM₂ d t : Set G) :=
    Common.mem_normalizer_sup (h.t_mem_normalizer_map_D1 d.M) (h.t_mem_normalizer_yamadaY₂_D1 d)
  rw [h591.1, h.mem_sup_zpowers_iff_of_normalizer htM₂] at hxL₂
  rcases hxL₂ with h1 | h1
  · exact h1
  · exfalso
    have := mul_mem (hM₂C h1) (inv_mem hxC)
    rw [mul_inv_cancel_right] at this
    exact h.t_not_mem_centralizer_yamadaV₁ d hlay this

theorem M₃_commutator (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    ⁅yamadaM₃ d t, yamadaM₃ d t⁆ = yamadaW₂ d t := by
  layer_ctx_P03
  have hM₃L₃ : yamadaM₃ d t ≤ yamadaL₃ d t := inf_le_left
  have hMM₃ := h.yamadaM_map_le_yamadaM₃_R5 d hlay
  have hle : ⁅yamadaM₃ d t, yamadaM₃ d t⁆ ≤ yamadaW₂ d t :=
    (Subgroup.commutator_mono hM₃L₃ hM₃L₃).trans (h.yamada_5_18 d hlay).le
  have hW : d.W.map L.subtype ≤ ⁅yamadaM₃ d t, yamadaM₃ d t⁆ := by
    rw [← d.commutator_M_eq, Subgroup.map_commutator]
    exact Subgroup.commutator_mono hMM₃ hMM₃
  have hne : ¬ ⁅yamadaM₃ d t, yamadaM₃ d t⁆ ≤ d.W.map L.subtype := by
    intro hc
    have hWM₁ : d.W.map L.subtype ≤ yamadaM₁ d t :=
      le_inf ((map_mono (d.W_le_F.trans d.F_le_M)).trans (le_sup_left.trans (h.tM_le_yamadaL₂ d)))
        ((map_mono (d.W_le_F.trans (d.F_le_M.trans d.M_le_S))).trans le_sup_left)
    have hM₁M₃ : yamadaM₁ d t ≤ yamadaM₃ d t :=
      (M₁_le_M₂ h d hlay).trans (h.yamadaM₂_le_yamadaM₃ d hlay)
    have hM₃N : yamadaM₃ d t ≤ normalizer (yamadaM₁ d t : Set G) := fun x hx =>
      mem_normalizer_fintype fun m hm => by
        have hcm : x * m * x⁻¹ * m⁻¹ ∈ yamadaM₁ d t :=
          hWM₁ (hc (Subgroup.commutator_mem_commutator hx (hM₁M₃ hm)))
        have := mul_mem hcm hm
        rwa [inv_mul_cancel_right] at this
    have hM₃R₅ : yamadaM₃ d t ≤ yamadaR₅ d t :=
      hM₃L₃.trans ((h.yamadaL₃_le_yamadaR₃_D3 d hlay).trans inf_le_left)
    have hM₃R₂ : yamadaM₃ d t ≤ yamadaR₂ d t := by
      rw [← (h.yamada_5_15 d hNH h561 h562 h591 h592 h593).2]
      exact le_inf hM₃R₅ hM₃N
    have hcard := Subgroup.card_le_of_le hM₃R₂
    rw [h.card_yamadaM₃ d hlay, (h.card_yamadaL₂_and d).2] at hcard
    have h2f : 2 ≤ 2 ^ f := d.two_le_q
    have hpos : 0 < (2 ^ f) ^ 14 := by positivity
    have h4 : 2 < (2 ^ f) ^ 2 := by nlinarith
    have : 2 * (2 ^ f) ^ 14 < (2 ^ f) ^ 16 := by
      calc 2 * (2 ^ f) ^ 14 < (2 ^ f) ^ 2 * (2 ^ f) ^ 14 := Nat.mul_lt_mul_of_pos_right h4 hpos
        _ = (2 ^ f) ^ 16 := by ring
    omega
  refine h.eq_yamadaW₂_of_le d hlay hW hle hne (fun g hg => ?_)
  exact mem_normalizer_commutator_D4 (mem_normalizer_inf_D4
    (h.leviLong_map_le_normalizer_yamadaL₃ d hg)
    (mem_normalizer_centralizer_D4 (h.leviLong_map_le_normalizer_yamadaY₂ d hlay hg)))

theorem S₂_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaS₂ d t = yamadaD₁ d t ⊔ yamadaM₂ d t := by
  have hD₁ := h.yamadaD₁_eq_sup_D1 d hlay
  apply le_antisymm
  · refine sup_le ?_ (le_sup_right.trans le_sup_right)
    rw [d.S_eq_sup, Subgroup.map_sup]
    exact sup_le ((map_mono d.U₁_le_M).trans (le_sup_left.trans le_sup_right))
      ((D_le_yamadaD₁ d t).trans le_sup_left)
  · refine sup_le ?_ ?_
    · rw [hD₁]
      exact sup_le (le_sup_left.trans le_sup_right) ((map_mono d.D_le_S).trans le_sup_left)
    · exact sup_le ((map_mono d.M_le_S).trans le_sup_left) le_sup_right

theorem mem_yamadaR₃_of_mem_normalizer_M₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} (hxR₄ : x ∈ yamadaR₄ d t)
    (hxM₂ : x ∈ normalizer (yamadaM₂ d t : Set G)) : x ∈ yamadaR₃ d t := by
  layer_ctx_P03
  have h514 := h.yamada_5_14 d hNH h561 h562 h591 h592 h593
  have hxR₅ : x ∈ yamadaR₅ d t := (inf_le_left : yamadaR₄ d t ≤ yamadaR₅ d t) hxR₄
  have hxD₁ : x ∈ normalizer (yamadaD₁ d t : Set G) :=
    hNH.1 (h.yamadaR₅_le_normalizer_yamadaC₁ d hxR₅)
  have hxS₂ : x ∈ normalizer (yamadaS₂ d t : Set G) := by
    rw [S₂_eq h d hlay]
    exact Common.mem_normalizer_sup hxD₁ hxM₂
  have htS₂ : t ∈ normalizer (yamadaS₂ d t : Set G) :=
    Common.mem_normalizer_sup (h.t_mem_normalizer_map_D1 d.S) (h.t_mem_normalizer_yamadaY₂_D1 d)
  obtain ⟨w, hwF₁, hw⟩ := h514.2.1.1 x hxR₄
  have hwS₂ : w ∈ yamadaS₂ d t :=
    h.yamadaS₁_le_yamadaS₂_S4C d hlay ((le_sup_right : yamadaD₁ d t ≤ yamadaS₁ d t)
      ((inf_le_right : yamadaF₁ d t ≤ yamadaD₁ d t) hwF₁))
  have hgt : x * t * x⁻¹ ∈ yamadaS₂ d t ⊔ zpowers t := by
    rw [hw]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hwS₂)
  have hxR₂ : x ∈ normalizer (yamadaR₂ d t : Set G) := by
    rw [h591.2.2.1]
    exact h.mem_normalizer_sup_zpowers_D3 htS₂ hxS₂ hgt
  have hxV₂ := (mem_inf.1 (Setup.normalizer_yamadaR₂_le d h592 h5101 h5102 hxR₂)).1
  exact (h.mem_yamadaR₃_iff_of_mem_yamadaR₄ d hNH h561 h562 h591 h592 h593 hxR₄).2
    ((le_sup_left : d.W.map L.subtype ≤ yamadaW₁ d t) (h.crossed_mem_W d h562 h592 hxV₂))

theorem not_M₄_le_normalizer_M₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : ¬ yamadaM₄ d t ≤ normalizer (yamadaM₂ d t : Set G) := by
  layer_ctx_P03
  intro hM
  have h524 := h.yamada_5_24 d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221
  have hM₄R₃ : yamadaM₄ d t ≤ yamadaR₃ d t := fun x hx =>
    mem_yamadaR₃_of_mem_normalizer_M₂ h d hlay
      ((inf_le_left : yamadaM₄ d t ≤ yamadaR₄ d t) hx) (hM hx)
  have htL₃ : t ∈ yamadaL₃ d t := by
    rw [h.yamadaL₃_eq_sup d hlay]
    exact mem_sup_right (mem_zpowers t)
  have htR₃ : t ∈ yamadaR₃ d t := h.yamadaL₃_le_yamadaR₃_D3 d hlay htL₃
  have hR₄R₃ : yamadaR₄ d t ≤ yamadaR₃ d t := by
    rw [h524.2.1.1, h524.1.1]
    exact sup_le (sup_le hM₄R₃ ((zpowers_le).2 htR₃)) le_rfl
  obtain ⟨x, hx, hxn⟩ := h.exists_mem_yamadaR₄_not_mem_yamadaR₃ d hNH h561 h562 h591 h592 h593
  exact hxn (hR₄R₃ hx)

theorem J_mem_normalizer_M₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {j : L} (hj : j ∈ d.J) :
    (j : G) ∈ normalizer (yamadaM₆ d t : Set G) := by
  have hjC : (j : G) ∈ centralizer ({t} : Set G) ⊓
      normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) :=
    mem_inf.2 ⟨h.L_le_centralizer j.2, Setup.coe_mem_normalizer_map (d.J_le_normalizer_Y hj)⟩
  exact mem_normalizer_inf_D4 (le_normalizer_yamadaL₆ d t
    ⟨h.centralizer_inf_normalizer_Y_le_normalizer_yamadaL₃ d hjC,
      h.centralizer_inf_normalizer_Y_le_normalizer_yamadaM₃ d hlay hjC⟩)
    (Setup.mem_normalizer_centralizer_C8
      (h.centralizer_inf_normalizer_Y_le_normalizer_yamadaY₂_L6 d hlay hjC))

theorem commutator_M₆_le (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : ⁅yamadaM₆ d t, yamadaM₆ d t⁆ ≤ yamadaW₃ d t := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact h.commutator_mem_yamadaW₃_of_mem_yamadaM₆ d hlay ha hb

theorem W₃_le_commutator (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaW₃ d t ≤ ⁅yamadaM₆ d t, yamadaM₆ d t⁆ := by
  layer_ctx_P03
  have hM₃M₆ : yamadaM₃ d t ≤ yamadaM₆ d t := inf_le_inf_right _ (h.yamadaL₃_le_yamadaL₆ d hlay)
  have hW₂P : yamadaW₂ d t ≤ ⁅yamadaM₆ d t, yamadaM₆ d t⁆ := by
    rw [← M₃_commutator h d hlay]
    exact Subgroup.commutator_mono hM₃M₆ hM₃M₆
  have hPW₃ := commutator_M₆_le h d hlay
  have hW₃L₃ : yamadaW₃ d t ≤ yamadaL₃ d t := inf_le_left
  have hL₃V := h.yamadaL₃_le_normalizer_yamadaV₂ d hNH h561 h562 h591 h592 h593 h5101 h5102
  have hW₃Y₂ : yamadaW₃ d t ≤ centralizer (yamadaY₂ d t : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t))
  have hL₂W₃ : yamadaL₂ d t ⊓ yamadaW₃ d t ≤ yamadaW₂ d t := by
    rintro x ⟨hxL₂, hxW₃⟩
    rw [← h.yamadaM₂_inf_yamadaW₃ d hlay]
    refine ⟨?_, hxW₃⟩
    rw [h.yamadaM₂_eq_inf_centralizer d h591 h592]
    exact ⟨hxL₂, hW₃Y₂ hxW₃⟩
  have hY : ∀ z ∈ yamadaW₃ d t, t * z * t * z⁻¹ ∈ d.Y.map L.subtype → z ∈ yamadaW₂ d t :=
    fun z hz hκ => hL₂W₃ ⟨yamadaL₃_inf_le d t ⟨hW₃L₃ hz,
      (h.crossed_mem_Y_iff d hNH h561 h562 h591 h592 h593 h5101 h5102 (hL₃V (hW₃L₃ hz))).1 hκ⟩,
      hz⟩
  by_cases hcase : ∀ r ∈ ⁅yamadaM₆ d t, yamadaM₆ d t⁆, t * r * t * r⁻¹ ∈ d.Y.map L.subtype
  ·
    exfalso
    have hPW₂ : ⁅yamadaM₆ d t, yamadaM₆ d t⁆ ≤ yamadaW₂ d t := fun r hr =>
      hY r (hPW₃ hr) (hcase r hr)
    have hM₂M₆ : yamadaM₂ d t ≤ yamadaM₆ d t := (h.yamadaM₂_le_yamadaM₃ d hlay).trans hM₃M₆
    have hW₂M₂ : yamadaW₂ d t ≤ yamadaM₂ d t :=
      sup_le_sup (map_mono (d.W_le_F.trans d.F_le_M)) le_rfl
    have hM₆N : yamadaM₆ d t ≤ normalizer (yamadaM₂ d t : Set G) := fun x hx =>
      mem_normalizer_fintype fun m hm => by
        have hc : x * m * x⁻¹ * m⁻¹ ∈ yamadaM₂ d t :=
          hW₂M₂ (hPW₂ (Subgroup.commutator_mem_commutator hx (hM₂M₆ hm)))
        have := mul_mem hc hm
        rwa [inv_mul_cancel_right] at this
    exact not_M₄_le_normalizer_M₂ h d hlay (fun x hx => hM₆N (h.yamadaM₄_le_yamadaM₆ d hlay hx))
  · push Not at hcase
    obtain ⟨r₀, hr₀, hκr₀⟩ := hcase
    obtain ⟨w₀, hw₀, hw₀e⟩ := h.crossed_mem_W d h562 h592 (hL₃V (hW₃L₃ (hPW₃ hr₀)))
    obtain ⟨a₀, n₀, hn₀, rfl⟩ := d.mem_W_iff.1 hw₀
    have ha₀ : d.x₄ a₀ ≠ 1 := fun e => hκr₀ (by
      rw [← hw₀e, e, one_mul]
      exact ⟨n₀, hn₀, rfl⟩)
    intro z hz
    obtain ⟨wz, hwz, hwze⟩ := h.crossed_mem_W d h562 h592 (hL₃V (hW₃L₃ hz))
    obtain ⟨b, n, hn, rfl⟩ := d.mem_W_iff.1 hwz
    by_cases hb : d.x₄ b = 1
    · refine hW₂P (hY z hz ?_)
      rw [← hwze, hb, one_mul]
      exact ⟨n, hn, rfl⟩
    obtain ⟨j, ⟨hj, hjx⟩, -⟩ := (d.yamada_three_five_five.2.2.1).2 _ (d.x₄_mem_U₄ a₀) ha₀ _
      (d.x₄_mem_U₄ b) hb
    have hjJ : j ∈ d.J := (inf_le_left : d.J₂ ≤ d.J) hj
    have hjP : (j : G) ∈ normalizer ((⁅yamadaM₆ d t, yamadaM₆ d t⁆ : Subgroup G) : Set G) :=
      mem_normalizer_commutator_D4 (J_mem_normalizer_M₆ h d hlay hjJ)
    have hjt : (j : G) * t = t * j := mem_centralizer_singleton_iff.1 (h.L_le_centralizer j.2)
    have hjt' : (j : G)⁻¹ * t * j = t := by rw [mul_assoc, ← hjt, inv_mul_cancel_left]
    have hrP : (j : G) * r₀ * (j : G)⁻¹ ∈ ⁅yamadaM₆ d t, yamadaM₆ d t⁆ :=
      (mem_normalizer_iff.1 hjP r₀).1 hr₀
    have hκr : t * ((j : G) * r₀ * (j : G)⁻¹) * t * ((j : G) * r₀ * (j : G)⁻¹)⁻¹ =
        (j : G) * (t * r₀ * t * r₀⁻¹) * (j : G)⁻¹ := by
      calc t * ((j : G) * r₀ * (j : G)⁻¹) * t * ((j : G) * r₀ * (j : G)⁻¹)⁻¹ =
            t * j * r₀ * ((j : G)⁻¹ * t * j) * r₀⁻¹ * (j : G)⁻¹ := by group
        _ = j * t * r₀ * t * r₀⁻¹ * (j : G)⁻¹ := by rw [hjt', ← hjt]
        _ = (j : G) * (t * r₀ * t * r₀⁻¹) * (j : G)⁻¹ := by group
    have hjn₀ : (j : G) * (n₀ : G) * (j : G)⁻¹ ∈ d.Y.map L.subtype :=
      ⟨j * n₀ * j⁻¹, (mem_normalizer_iff.1 (d.J_le_normalizer_Y hjJ) n₀).1 hn₀, rfl⟩
    have hjx' : (j : G) * (d.x₄ a₀ : G) * (j : G)⁻¹ = (d.x₄ b : G) := congrArg Subtype.val hjx
    have e : t * ((j : G) * r₀ * (j : G)⁻¹) * t * ((j : G) * r₀ * (j : G)⁻¹)⁻¹ =
        t * z * t * z⁻¹ * ((n : G)⁻¹ * ((j : G) * n₀ * (j : G)⁻¹)) := by
      rw [hκr, ← hw₀e, ← hwze]
      calc (j : G) * L.subtype (d.x₄ a₀ * n₀) * (j : G)⁻¹ =
            ((j : G) * (d.x₄ a₀ : G) * (j : G)⁻¹) * ((j : G) * (n₀ : G) * (j : G)⁻¹) := by
            rw [map_mul, Subgroup.coe_subtype]
            group
        _ = (d.x₄ b : G) * ((j : G) * (n₀ : G) * (j : G)⁻¹) := by rw [hjx']
        _ = L.subtype (d.x₄ b * n) * ((n : G)⁻¹ * ((j : G) * n₀ * (j : G)⁻¹)) := by
            rw [map_mul, Subgroup.coe_subtype]
            group
    have hrW₃ : (j : G) * r₀ * (j : G)⁻¹ ∈ yamadaW₃ d t := hPW₃ hrP
    have hc := h.inv_mul_mem_normalizer_tY d hNH h561 h562 h591 h592 h593 h5101 h5102
      (hL₃V (hW₃L₃ hrW₃)) (hL₃V (hW₃L₃ hz)) (mul_mem (inv_mem ⟨n, hn, rfl⟩) hjn₀) e
    have hpz : ((j : G) * r₀ * (j : G)⁻¹)⁻¹ * z ∈ yamadaW₃ d t := mul_mem (inv_mem hrW₃) hz
    have hpzW₂ : ((j : G) * r₀ * (j : G)⁻¹)⁻¹ * z ∈ yamadaW₂ d t :=
      hL₂W₃ ⟨yamadaL₃_inf_le d t ⟨hW₃L₃ hpz, hc⟩, hpz⟩
    have := mul_mem hrP (hW₂P hpzW₂)
    rwa [mul_inv_cancel_left] at this

end ProductToolboxAux.P03

theorem ProductToolboxAux.P03.u_centralizes (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : uG d ∈ centralizer (yamadaV₁ d t : Set G) := by
  have hN : ∀ g ∈ d.leviShort, ((g : L) : G) ∈ normalizer (yamadaV₁ d t : Set G) := fun g hg =>
    normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t
      (h.map_normalizer_V_le_normalizer_yamadaD₁ d ⟨g, d.leviShort_le_normalizer_V hg, rfl⟩)
  have hle := ProductToolboxAux.P03.leviShort_le_of_normalized d
    (N := (centralizer (yamadaV₁ d t : Set G)).comap L.subtype)
    (fun g hg n hn => by
      rw [mem_comap] at hn ⊢
      rw [mem_centralizer_iff] at hn ⊢
      intro v hv
      have hv' : ((g : L) : G)⁻¹ * v * ((g : L) : G) ∈ yamadaV₁ d t :=
        (mem_normalizer_iff''.1 (hN g hg) v).1 hv
      have h1 := hn _ hv'
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at h1 ⊢
      calc v * ((g : G) * (n : G) * (g : G)⁻¹)
          = (g : G) * (((g : G)⁻¹ * v * (g : G)) * (n : G)) * (g : G)⁻¹ := by group
        _ = (g : G) * ((n : G) * ((g : G)⁻¹ * v * (g : G))) * (g : G)⁻¹ := by rw [h1]
        _ = (g : G) * (n : G) * (g : G)⁻¹ * v := by group)
    (h.x₁_mem_centralizer_yamadaV₁ d hlay 1)
  exact hle d.u_mem_leviShort

theorem ProductToolboxAux.P03.commutator (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : ⁅yamadaM₆ d t, yamadaM₆ d t⁆ = yamadaW₃ d t :=
  le_antisymm (ProductToolboxAux.P03.commutator_M₆_le h d hlay)
    (ProductToolboxAux.P03.W₃_le_commutator h d hlay)

end P03

section Inputs

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section P02

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

namespace ProductToolboxAux.P02

section Abstract

variable {H : Type*} [Group H]

theorem kappa_comm {t j x k : H} {F S Q : Subgroup H}
    (hjt : j * t = t * j) (hxt : x * t * x⁻¹ = t * k)
    (hxQ : x ∈ Q) (hjQ : j ∈ normalizer (Q : Set H))
    (hkS : k ∈ S) (hxS : x ∈ normalizer (S : Set H)) (hSF : S ≤ normalizer (F : Set H))
    (hQ : ∀ g ∈ Q, ∀ s ∈ S, g * s * g⁻¹ * s⁻¹ ∈ F) :
    ∃ c ∈ F, (j * x * j⁻¹ * x⁻¹) * t * (j * x * j⁻¹ * x⁻¹)⁻¹ =
      t * ((j * k * j⁻¹ * k⁻¹) * c) := by
  have huQ : j * x * j⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hjQ x).1 hxQ
  have hzS : x⁻¹ * k⁻¹ * x ∈ S := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hxS) k⁻¹).1 (inv_mem hkS)
    rwa [inv_inv] at this
  have hkN : k ∈ normalizer (F : Set H) := hSF hkS
  have hA : (j * x * j⁻¹) * (x⁻¹ * k⁻¹ * x) * (j * x * j⁻¹)⁻¹ * (x⁻¹ * k⁻¹ * x)⁻¹ ∈ F :=
    hQ _ huQ _ hzS
  have hB : x⁻¹ * k⁻¹ * x⁻¹⁻¹ * k⁻¹⁻¹ ∈ F := hQ _ (inv_mem hxQ) _ (inv_mem hkS)
  refine ⟨k * ((j * x * j⁻¹) * (x⁻¹ * k⁻¹ * x) * (j * x * j⁻¹)⁻¹ * (x⁻¹ * k⁻¹ * x)⁻¹) * k⁻¹ *
    (k * (x⁻¹ * k⁻¹ * x⁻¹⁻¹ * k⁻¹⁻¹) * k⁻¹), mul_mem ((Subgroup.mem_normalizer_iff.1 hkN _).1 hA)
    ((Subgroup.mem_normalizer_iff.1 hkN _).1 hB), ?_⟩
  have E1' : x⁻¹ * t * x = t * (x⁻¹ * k⁻¹ * x) := by
    have h1 : x * t = t * k * x := by
      calc x * t = (x * t * x⁻¹) * x := by group
        _ = t * k * x := by rw [hxt]
    calc x⁻¹ * t * x = x⁻¹ * (t * k * x) * (x⁻¹ * k⁻¹ * x) := by group
      _ = x⁻¹ * (x * t) * (x⁻¹ * k⁻¹ * x) := by rw [h1]
      _ = t * (x⁻¹ * k⁻¹ * x) := by group
  have E2' : j⁻¹ * t * j = t := by
    rw [mul_assoc, ← hjt, inv_mul_cancel_left]
  have E2'' : j * t * j⁻¹ = t := by
    rw [hjt, mul_assoc, mul_inv_cancel, mul_one]
  calc (j * x * j⁻¹ * x⁻¹) * t * (j * x * j⁻¹ * x⁻¹)⁻¹
      = j * x * j⁻¹ * (x⁻¹ * t * x) * (j * x * j⁻¹)⁻¹ := by group
    _ = j * x * j⁻¹ * (t * (x⁻¹ * k⁻¹ * x)) * (j * x * j⁻¹)⁻¹ := by rw [E1']
    _ = j * x * (j⁻¹ * t * j) * (j⁻¹ * (x⁻¹ * k⁻¹ * x) * j) * x⁻¹ * j⁻¹ := by group
    _ = j * x * t * (j⁻¹ * (x⁻¹ * k⁻¹ * x) * j) * x⁻¹ * j⁻¹ := by rw [E2']
    _ = j * (x * t * x⁻¹) * (x * (j⁻¹ * (x⁻¹ * k⁻¹ * x) * j) * x⁻¹) * j⁻¹ := by group
    _ = j * (t * k) * (x * (j⁻¹ * (x⁻¹ * k⁻¹ * x) * j) * x⁻¹) * j⁻¹ := by rw [hxt]
    _ = (j * t * j⁻¹) * (j * k * j⁻¹) * ((j * x * j⁻¹) * (x⁻¹ * k⁻¹ * x) * (j * x * j⁻¹)⁻¹) := by
        group
    _ = t * (j * k * j⁻¹) * ((j * x * j⁻¹) * (x⁻¹ * k⁻¹ * x) * (j * x * j⁻¹)⁻¹) := by rw [E2'']
    _ = _ := by group

theorem key_abstract {t j : H} {Q R₄ R₅ R₆ F S M D Nrm : Subgroup H}
    (hjt : j * t = t * j)
    (hQR : ∀ x ∈ Q, ∃ a ∈ R₅, ∃ b ∈ R₆, x = a * b)
    (hR₄₅ : R₄ ≤ R₅) (hR₄₆ : R₄ ≤ R₆) (hR₅Q : R₅ ≤ Q) (hR₆Q : R₆ ≤ Q)
    (hQR₄ : Q ≤ normalizer (R₄ : Set H)) (hQ' : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ R₄)
    (hQS : Q ≤ normalizer (S : Set H)) (hSF : S ≤ normalizer (F : Set H))
    (hQ : ∀ g ∈ Q, ∀ s ∈ S, g * s * g⁻¹ * s⁻¹ ∈ F)
    (hker : ∀ y ∈ Q, ∀ c ∈ F, y * t * y⁻¹ = t * c → y ∈ R₄)
    (h5 : ∀ a ∈ R₅, ∃ k ∈ D, a * t * a⁻¹ = t * k)
    (h6 : ∀ b ∈ R₆, ∃ k ∈ M, b * t * b⁻¹ = t * k)
    (h4 : ∀ r ∈ R₄, ∃ c ∈ F, r * t * r⁻¹ = t * c)
    (hDS : D ≤ S) (hMS : M ≤ S)
    (hjQ : j ∈ normalizer (Q : Set H)) (hjR₆ : j ∈ normalizer (R₆ : Set H)) (hjN : j ∈ Nrm)
    (hJ₂ : ∀ δ ∈ D, j * δ * j⁻¹ * δ⁻¹ ∈ F)
    (hJ₃ : ∀ m ∈ M, j * m * j⁻¹ * m⁻¹ ∈ F → m ∈ F)
    (hN₅ : ∀ a ∈ R₅, a ∈ Nrm → a ∈ R₄) (hN₆ : ∀ b ∈ R₆, b ∈ Nrm → b ∈ R₄) :
    ∀ x ∈ Q, x ∈ Nrm → x ∈ R₄ := by
  intro x hxQ hxN
  obtain ⟨a, ha, b, hb, rfl⟩ := hQR x hxQ
  have haQ := hR₅Q ha
  have hbQ := hR₆Q hb
  have hQR₆ : ∀ g ∈ Q, ∀ r ∈ R₆, g * r * g⁻¹ ∈ R₆ := by
    intro g hg r hr
    have h1 := mul_mem (hR₄₆ (hQ' g hg r (hR₆Q hr))) hr
    rwa [show g * r * g⁻¹ * r⁻¹ * r = g * r * g⁻¹ by group] at h1
  have ha₀ : j * a * j⁻¹ * a⁻¹ ∈ R₄ := by
    obtain ⟨k, hkD, hak⟩ := h5 a ha
    obtain ⟨c, hcF, hc⟩ := kappa_comm hjt hak haQ hjQ (hDS hkD) (hQS haQ) hSF hQ
    refine hker _ (mul_mem ((Subgroup.mem_normalizer_iff.1 hjQ a).1 haQ) (inv_mem haQ))
      (j * k * j⁻¹ * k⁻¹ * c) (mul_mem (hJ₂ k hkD) hcF) ?_
    rw [hc]
  have hb₀ : j * b * j⁻¹ * b⁻¹ ∈ R₆ :=
    mul_mem ((Subgroup.mem_normalizer_iff.1 hjR₆ b).1 hb) (inv_mem hb)
  have hy : j * (a * b) * j⁻¹ * (a * b)⁻¹ =
      (j * a * j⁻¹ * a⁻¹) * (a * (j * b * j⁻¹ * b⁻¹) * a⁻¹) := by group
  have hyR₆ : j * (a * b) * j⁻¹ * (a * b)⁻¹ ∈ R₆ := by
    rw [hy]
    exact mul_mem (hR₄₆ ha₀) (hQR₆ a haQ _ hb₀)
  have hyN : j * (a * b) * j⁻¹ * (a * b)⁻¹ ∈ Nrm :=
    mul_mem (mul_mem (mul_mem hjN hxN) (inv_mem hjN)) (inv_mem hxN)
  have hyR₄ := hN₆ _ hyR₆ hyN
  have hb₀R₄ : j * b * j⁻¹ * b⁻¹ ∈ R₄ := by
    have h1 : a * (j * b * j⁻¹ * b⁻¹) * a⁻¹ ∈ R₄ := by
      have := mul_mem (inv_mem ha₀) hyR₄
      rwa [hy, ← mul_assoc, inv_mul_cancel, one_mul] at this
    have h2 := (Subgroup.mem_normalizer_iff.1 (hQR₄ (inv_mem haQ)) _).1 h1
    rwa [show a⁻¹ * (a * (j * b * j⁻¹ * b⁻¹) * a⁻¹) * a⁻¹⁻¹ = j * b * j⁻¹ * b⁻¹ by group] at h2
  have hbR₄ : b ∈ R₄ := by
    obtain ⟨k, hkM, hbk⟩ := h6 b hb
    obtain ⟨c, hcF, hc⟩ := kappa_comm hjt hbk hbQ hjQ (hMS hkM) (hQS hbQ) hSF hQ
    obtain ⟨c', hc'F, hc'⟩ := h4 _ hb₀R₄
    have hcc : j * k * j⁻¹ * k⁻¹ * c = c' := mul_left_cancel (hc.symm.trans hc')
    have hjk : j * k * j⁻¹ * k⁻¹ ∈ F := by
      have := mul_mem hc'F (inv_mem hcF)
      rwa [← hcc, mul_inv_cancel_right] at this
    exact hker b hbQ k (hJ₃ k hkM hjk) hbk
  exact hN₅ _ (mul_mem ha (hR₄₅ hbR₄)) hxN

end Abstract

section Torus

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem exists_torus_j :
    ∃ j ∈ d.J, (∀ s ∈ d.D, j * s * j⁻¹ * s⁻¹ ∈ d.F) ∧
      ∀ m ∈ d.M, j * m * j⁻¹ * m⁻¹ ∈ d.F → m ∈ d.F := by
  obtain ⟨γ, hγ⟩ := d.exists_σ_ne
  have hγ0 : γ ≠ 0 := fun h0 => hγ (by rw [h0, map_zero])
  have hγ1 : γ ≠ 1 := fun h1 => hγ (by rw [h1, map_one])
  have hjx₁ : ∀ a, d.torus (1, Units.mk0 γ hγ0) * d.x₁ a * (d.torus (1, Units.mk0 γ hγ0))⁻¹ =
      d.x₁ (γ * a) := fun a => by
    rw [d.torus_x₁]
    rfl
  have hjx₂ : ∀ a, d.torus (1, Units.mk0 γ hγ0) * d.x₂ a * (d.torus (1, Units.mk0 γ hγ0))⁻¹ =
      d.x₂ a := fun a => by
    rw [d.torus_x₂]
    simp
  have hjF : ∀ n ∈ d.F, d.torus (1, Units.mk0 γ hγ0) * n * (d.torus (1, Units.mk0 γ hγ0))⁻¹ ∈ d.F :=
    fun n hn => (Subgroup.mem_normalizer_iff.1 (d.J_le_normalizer_F (d.torus_mem_J _)) n).1 hn
  generalize hj : d.torus (1, Units.mk0 γ hγ0) = j at hjx₁ hjx₂ hjF
  refine ⟨j, hj ▸ d.torus_mem_J _, ?_, ?_⟩
  · intro s hs
    obtain ⟨a, n, hn, rfl⟩ := d.mem_D_iff.1 hs
    have e : j * (d.x₂ a * n) * j⁻¹ * (d.x₂ a * n)⁻¹ =
        d.x₂ a * (j * n * j⁻¹ * n⁻¹) * (d.x₂ a)⁻¹ := by
      calc j * (d.x₂ a * n) * j⁻¹ * (d.x₂ a * n)⁻¹
          = (j * d.x₂ a * j⁻¹) * (j * n * j⁻¹) * n⁻¹ * (d.x₂ a)⁻¹ := by group
        _ = d.x₂ a * (j * n * j⁻¹) * n⁻¹ * (d.x₂ a)⁻¹ := by rw [hjx₂]
        _ = _ := by group
    rw [e]
    have hx₂N : d.x₂ a ∈ normalizer (d.F : Set X) :=
      d.S_le_normalizer_F (d.U₂_le_S (d.x₂_mem_U₂ a))
    exact (Subgroup.mem_normalizer_iff.1 hx₂N _).1 (mul_mem (hjF n hn) (inv_mem hn))
  · intro m hm hc
    obtain ⟨c, n, hn, rfl⟩ := d.mem_M_iff.1 hm
    have hn'' : j * n * j⁻¹ * n⁻¹ ∈ d.F := mul_mem (hjF n hn) (inv_mem hn)
    have e : j * (d.x₁ c * n) * j⁻¹ * (d.x₁ c * n)⁻¹ =
        (d.x₁ (γ * c) * (j * n * j⁻¹ * n⁻¹)) * d.x₁ c := by
      calc j * (d.x₁ c * n) * j⁻¹ * (d.x₁ c * n)⁻¹
          = (j * d.x₁ c * j⁻¹) * (j * n * j⁻¹) * n⁻¹ * (d.x₁ c)⁻¹ := by group
        _ = d.x₁ (γ * c) * (j * n * j⁻¹) * n⁻¹ * d.x₁ c := by rw [hjx₁, d.x₁_inv]
        _ = _ := by group
    have hS₁ : d.x₁ (γ * c) * (j * n * j⁻¹ * n⁻¹) ∈ d.S :=
      mul_mem (d.U₁_le_S (d.x₁_mem_U₁ _)) (d.F_le_S hn'')
    have hS₂ : d.x₁ c ∈ d.S := d.U₁_le_S (d.x₁_mem_U₁ c)
    have h1 := d.nfc_fst_mul hS₁ hS₂
    rw [← e, d.nfc_x₁_mul (d.F_le_D hn'')] at h1
    have h2 : (d.nfc (d.x₁ c)).1 = c := by
      simpa using d.nfc_x₁_mul (a := c) (n := 1) (one_mem _)
    rw [h2, d.nfc_fst_of_mem_D (d.F_le_D hc)] at h1
    have h3 : (γ + 1) * c = 0 := by rw [add_mul, one_mul]; exact h1.symm
    have hc0 : c = 0 := by
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd (CharTwo.add_eq_zero.1 h4) hγ1
      · exact h4
    rw [hc0, d.x₁_zero, one_mul]
    exact hn

end Torus

section Concrete

theorem R₄_le_R₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaR₄ d t ≤ yamadaR₆ d t := by
  rw [h.yamadaR₄_eq_sup_yamadaL₄_L6T d hlay]
  exact sup_le_sup_right ((h.yamadaL₄_le_yamadaT₆ d hlay).trans (h.yamadaT₆_le_yamadaL₆ d hlay)) _

theorem Q_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaP d t ⊔ zpowers t = yamadaR₅ d t ⊔ yamadaR₆ d t :=
  (h.yamada_5_32_of_layerHyp d hlay).2.2.2.2.2.1

theorem R₅_le_Q (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaR₅ d t ≤ yamadaP d t ⊔ zpowers t := by
  rw [Q_eq h d hlay]
  exact le_sup_left

theorem R₆_le_Q (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaR₆ d t ≤ yamadaP d t ⊔ zpowers t := by
  rw [Q_eq h d hlay]
  exact le_sup_right

theorem Q_le_normalizer_R₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaP d t ⊔ zpowers t ≤ normalizer (yamadaR₄ d t : Set G) :=
  h.yamadaP_sup_zpowers_le_normalizer_yamadaR₄_PA d hlay

theorem Q_le_normalizer_S₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaP d t ⊔ zpowers t ≤ normalizer (yamadaS₄ d t : Set G) := fun _ hx =>
  (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (h.normalizer_yamadaR₄_le_of_layerHyp d hlay
    (Q_le_normalizer_R₄ h d hlay hx))).1).1

theorem S₄_le_normalizer_F₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaS₄ d t ≤ normalizer (yamadaF₄ d t : Set G) := fun _ hu =>
  (Subgroup.mem_inf.1 (h.normalizer_yamadaR₄_le_normalizer_yamadaF₄ d hlay
    (Subgroup.le_normalizer ((inf_le_left : yamadaS₄ d t ≤ yamadaR₄ d t) hu)))).2

theorem mem_R₄_of_conj_t (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d)
    {y c : G} (hyQ : y ∈ yamadaP d t ⊔ zpowers t) (hc : c ∈ yamadaF₄ d t)
    (hyt : y * t * y⁻¹ = t * c) : y ∈ yamadaR₄ d t := by
  have hker := (h.yamada_5_32_of_layerHyp d hlay).2.2.2.2.2.2.1
  have hyN : y ∈ normalizer (yamadaF₄ d t : Set G) :=
    (Subgroup.mem_inf.1 (h.normalizer_yamadaR₄_le_normalizer_yamadaF₄ d hlay
      (Q_le_normalizer_R₄ h d hlay hyQ))).2
  have hyN' : y ∈ normalizer ((yamadaF₄ d t ⊔ zpowers t : Subgroup G) : Set G) :=
    h.mem_normalizer_sup_zpowers_D3 (h.t_mem_normalizer_yamadaF₄ d hlay) hyN (by
      rw [hyt]
      exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)) (Subgroup.mem_sup_left hc))
  rw [← hker]
  exact Subgroup.mem_inf.2 ⟨hyQ, hyN'⟩

theorem mem_R₄_of_mem_normalizer_R₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {a : G} (haQ : a ∈ yamadaP d t ⊔ zpowers t)
    (ha : a ∈ normalizer (yamadaR₃ d t : Set G)) : a ∈ yamadaR₄ d t := by
  have hker := (h.yamada_5_32_of_layerHyp d hlay).2.2.2.2.2.2.1
  have hNCS := h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₄ d hlay
  have hmem : a ∈ ((yamadaR₄ d t ⊔ (centralizer ({t} : Set G) ⊓
      normalizer ((d.S.map L.subtype : Subgroup G) : Set G)) : Subgroup G) : Set G) := by
    rw [← h.yamada_5_27_3 d hlay]
    exact ha
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hNCS, Set.mem_mul] at hmem
  obtain ⟨r, hr, c, hc, rfl⟩ := hmem
  have hrQ : r ∈ yamadaP d t ⊔ zpowers t :=
    R₅_le_Q h d hlay ((inf_le_left : yamadaR₄ d t ≤ yamadaR₅ d t) (SetLike.mem_coe.1 hr))
  have hcQ : c ∈ yamadaP d t ⊔ zpowers t := by
    have := mul_mem (inv_mem hrQ) haQ
    rwa [inv_mul_cancel_left] at this
  have hcF : c ∈ normalizer (yamadaF₄ d t : Set G) :=
    (Subgroup.mem_inf.1 (h.normalizer_yamadaR₄_le_normalizer_yamadaF₄ d hlay (hNCS hc))).2
  have hcN : c ∈ normalizer ((yamadaF₄ d t ⊔ zpowers t : Subgroup G) : Set G) :=
    Common.mem_normalizer_sup hcF
      (mem_normalizer_zpowers_of_comm_D4 (Subgroup.mem_centralizer_singleton_iff.1 hc.1))
  have hcR₄ : c ∈ yamadaR₄ d t := by
    rw [← hker]
    exact Subgroup.mem_inf.2 ⟨hcQ, hcN⟩
  exact mul_mem (SetLike.mem_coe.1 hr) hcR₄

theorem R₃_eq_sup_L₃_S₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaR₃ d t = yamadaL₃ d t ⊔ yamadaS₃ d t := by
  have hy := h.l6Hyps d hlay
  have h5172 := (h.yamada_5_17_2 d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593 hy.h5101
    hy.h5102).2
  have hSS₃ : d.S.map L.subtype ≤ yamadaS₃ d t :=
    le_inf (by rw [h5172]; exact le_sup_right) (h.S_map_le_centralizer_yamadaV₁ d hlay)
  refine le_antisymm ?_ (sup_le (h.yamadaL₃_le_yamadaR₃_D3 d hlay) inf_le_left)
  rw [h5172]
  exact sup_le_sup_left hSS₃ _

theorem R₆_le_normalizer_L₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    yamadaR₆ d t ≤ normalizer (yamadaL₃ d t : Set G) :=
  sup_le (fun _ hx => (Subgroup.mem_inf.1 (yamadaL₆_le d t hx)).1) (h.S_le_normalizer_yamadaL₃ d)

theorem mem_R₄_of_mem_R₆_of_mem_normalizer_S₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {b : G} (hb : b ∈ yamadaR₆ d t)
    (hbN : b ∈ normalizer (yamadaS₃ d t : Set G)) : b ∈ yamadaR₄ d t := by
  have hbR₃ : b ∈ normalizer (yamadaR₃ d t : Set G) := by
    rw [R₃_eq_sup_L₃_S₃ h d hlay]
    exact Common.mem_normalizer_sup (R₆_le_normalizer_L₃ h d hb) hbN
  exact mem_R₄_of_mem_normalizer_R₃ h d hlay (R₆_le_Q h d hlay hb) hbR₃

theorem conj_t_of_mem_R₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d)
    {a : G} (ha : a ∈ yamadaR₅ d t) : ∃ δ ∈ yamadaD₁ d t, a * t * a⁻¹ = t * δ := by
  have hy := h.l6Hyps d hlay
  have h512 := h.yamada_5_12 d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593
  have hSN : d.S.map L.subtype ≤ normalizer (yamadaC₅ d t : Set G) := fun s hs =>
    le_normalizer_yamadaC₅ d t (h.S_le_normalizer_yamadaC₁ d hs)
  have ha' : a ∈ ((yamadaC₅ d t ⊔ d.S.map L.subtype : Subgroup G) : Set G) := ha
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hSN, Set.mem_mul] at ha'
  obtain ⟨c, hc, s, hs, rfl⟩ := ha'
  obtain ⟨δ, hδ, hcδ⟩ := h512.2.1.1 c hc
  refine ⟨δ, hδ, ?_⟩
  have hst : s * t = t * s := Subgroup.mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs)
  calc c * s * t * (c * s)⁻¹ = c * (s * t * s⁻¹) * c⁻¹ := by group
    _ = c * t * c⁻¹ := by rw [show s * t * s⁻¹ = t by rw [hst]; group]
    _ = t * δ := hcδ

theorem mem_R₄_of_mem_R₅_of_mem_normalizer_S₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {a : G} (ha : a ∈ yamadaR₅ d t)
    (haN : a ∈ normalizer (yamadaS₃ d t : Set G)) : a ∈ yamadaR₄ d t := by
  have hy := h.l6Hyps d hlay
  obtain ⟨δ, hδ, hat⟩ := conj_t_of_mem_R₅ h d hlay ha
  have hδS₃ : δ ∈ yamadaS₃ d t :=
    (inf_le_left : yamadaD₃ d t ≤ yamadaS₃ d t)
      (h.yamadaD₁_le_yamadaD₃_C9 d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593 hδ)
  have haR₃ : a ∈ normalizer (yamadaR₃ d t : Set G) := by
    rw [(h.yamada_5_20 d hlay).2.2.2.2.2.2.1]
    exact h.mem_normalizer_sup_zpowers_D3 (h.t_mem_normalizer_yamadaS₃ d hlay) haN (by
      rw [hat]
      exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)) (Subgroup.mem_sup_left hδS₃))
  exact mem_R₄_of_mem_normalizer_R₃ h d hlay (R₅_le_Q h d hlay ha) haR₃

theorem conj_t_of_mem_R₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d)
    {b : G} (hb : b ∈ yamadaR₆ d t) : ∃ m ∈ yamadaM₃ d t, b * t * b⁻¹ = t * m := by
  have hSN : d.S.map L.subtype ≤ normalizer (yamadaL₆ d t : Set G) := fun s hs =>
    h.centralizer_inf_normalizer_S_le_normalizer_yamadaL₆ d hlay
      (h.S_map_le_centralizer_inf_normalizer_L6T d hs)
  have hb' : b ∈ ((yamadaL₆ d t ⊔ d.S.map L.subtype : Subgroup G) : Set G) := hb
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hSN, Set.mem_mul] at hb'
  obtain ⟨l, hl, s, hs, rfl⟩ := hb'
  obtain ⟨m, hm, hlm⟩ := h.conj_t_mem_of_mem_yamadaL₆ d hlay hl
  refine ⟨m, hm, ?_⟩
  have hst : s * t = t * s := Subgroup.mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs)
  calc l * s * t * (l * s)⁻¹ = l * (s * t * s⁻¹) * l⁻¹ := by group
    _ = l * t * l⁻¹ := by rw [show s * t * s⁻¹ = t by rw [hst]; group]
    _ = t * m := hlm

theorem conj_t_of_mem_R₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d)
    {r : G} (hr : r ∈ yamadaR₄ d t) : ∃ c ∈ yamadaF₄ d t, r * t * r⁻¹ = t * c := by
  have hy := h.l6Hyps d hlay
  have h514 := h.yamada_5_14 d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593
  obtain ⟨w, hwF₁, hw⟩ := h514.2.1.1 r hr
  exact ⟨w, h.yamadaF₁_le_yamadaF₄_P d hlay hwF₁, hw⟩

theorem torus_transfer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d)
    {j₀ : L} (hj₀ : j₀ ∈ d.J) (hJ₂ : ∀ s ∈ d.D, j₀ * s * j₀⁻¹ * s⁻¹ ∈ d.F)
    (hJ₃ : ∀ m ∈ d.M, j₀ * m * j₀⁻¹ * m⁻¹ ∈ d.F → m ∈ d.F) :
    (∀ δ ∈ yamadaD₄ d t, (j₀ : G) * δ * (j₀ : G)⁻¹ * δ⁻¹ ∈ yamadaF₄ d t) ∧
      ∀ m ∈ yamadaM₄ d t, (j₀ : G) * m * (j₀ : G)⁻¹ * m⁻¹ ∈ yamadaF₄ d t → m ∈ yamadaF₄ d t := by
  have hjNCS : (j₀ : G) ∈ centralizer ({t} : Set G) ⊓
      normalizer ((d.S.map L.subtype : Subgroup G) : Set G) :=
    ⟨h.L_le_centralizer j₀.2, Setup.coe_mem_normalizer_map (d.J_le_normalizer_S hj₀)⟩
  have hjF : (j₀ : G) ∈ normalizer (yamadaF₄ d t : Set G) :=
    (Subgroup.mem_inf.1 (h.normalizer_yamadaR₄_le_normalizer_yamadaF₄ d hlay
      (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₄ d hlay hjNCS))).2
  have hcoe : ∀ a b : L, ((a * b * a⁻¹ * b⁻¹ : L) : G) = (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ :=
    fun a b => by simp
  have hsplit : ∀ δ₀ g : G, (j₀ : G) * (δ₀ * g) * (j₀ : G)⁻¹ * (δ₀ * g)⁻¹ =
      ((j₀ : G) * δ₀ * (j₀ : G)⁻¹ * δ₀⁻¹) *
        (δ₀ * ((j₀ : G) * g * (j₀ : G)⁻¹ * g⁻¹) * δ₀⁻¹) := fun δ₀ g => by group
  constructor
  · intro δ hδ
    have hD₄ := h.yamadaD₄_eq_sup d hlay
    have hDD₄ : d.D.map L.subtype ≤ yamadaD₄ d t := by
      rw [hD₄]
      exact le_sup_left
    have hDN : d.D.map L.subtype ≤ normalizer (yamadaF₄ d t : Set G) := fun δ' hδ' =>
      h.yamadaD₄_le_normalizer_yamadaF₄_R5 d hlay (hDD₄ hδ')
    have hδ' : δ ∈ ((d.D.map L.subtype ⊔ yamadaF₄ d t : Subgroup G) : Set G) := by
      rw [← hD₄]
      exact hδ
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hDN, Set.mem_mul] at hδ'
    obtain ⟨δ₀, hδ₀, g, hg, rfl⟩ := hδ'
    obtain ⟨s₀, hs₀, rfl⟩ := hδ₀
    rw [hsplit]
    have h1 : (j₀ : G) * (s₀ : G) * (j₀ : G)⁻¹ * (s₀ : G)⁻¹ ∈ yamadaF₄ d t := by
      rw [← hcoe]
      exact h.F_map_le_yamadaF₄_S4C d hlay ⟨_, hJ₂ s₀ hs₀, rfl⟩
    have h2 : (j₀ : G) * g * (j₀ : G)⁻¹ * g⁻¹ ∈ yamadaF₄ d t :=
      mul_mem ((Subgroup.mem_normalizer_iff.1 hjF g).1 hg) (inv_mem hg)
    exact mul_mem h1 ((Subgroup.mem_normalizer_iff.1 (hDN ⟨s₀, hs₀, rfl⟩) _).1 h2)
  · intro m hm hc
    have hM₄ := h.yamadaM₄_eq_sup d hlay
    have hMM₄ : d.M.map L.subtype ≤ yamadaM₄ d t := by
      rw [hM₄]
      exact le_sup_left
    have hMN : d.M.map L.subtype ≤ normalizer (yamadaF₄ d t : Set G) := fun μ hμ =>
      h.yamadaM₄_le_normalizer_yamadaF₄_R5 d hlay (hMM₄ hμ)
    have hm' : m ∈ ((d.M.map L.subtype ⊔ yamadaF₄ d t : Subgroup G) : Set G) := by
      rw [← hM₄]
      exact hm
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hMN, Set.mem_mul] at hm'
    obtain ⟨μ₀, hμ₀, g, hg, rfl⟩ := hm'
    obtain ⟨s₀, hs₀, rfl⟩ := hμ₀
    rw [hsplit] at hc
    have h2 : (j₀ : G) * g * (j₀ : G)⁻¹ * g⁻¹ ∈ yamadaF₄ d t :=
      mul_mem ((Subgroup.mem_normalizer_iff.1 hjF g).1 hg) (inv_mem hg)
    have h3 : (j₀ : G) * (s₀ : G) * (j₀ : G)⁻¹ * (s₀ : G)⁻¹ ∈ yamadaF₄ d t := by
      have := mul_mem hc (inv_mem ((Subgroup.mem_normalizer_iff.1 (hMN ⟨s₀, hs₀, rfl⟩) _).1 h2))
      rwa [mul_inv_cancel_right] at this
    have h4 : (j₀ * s₀ * j₀⁻¹ * s₀⁻¹ : L) ∈ d.S :=
      mul_mem ((Subgroup.mem_normalizer_iff.1 (d.J_le_normalizer_S hj₀) s₀).1 (d.M_le_S hs₀))
        (inv_mem (d.M_le_S hs₀))
    have h5 : ((j₀ * s₀ * j₀⁻¹ * s₀⁻¹ : L) : G) ∈ d.F.map L.subtype := by
      rw [← h.S_map_inf_yamadaF₄ d hlay]
      exact ⟨⟨_, h4, rfl⟩, by rw [hcoe]; exact h3⟩
    obtain ⟨y, hy, hye⟩ := h5
    have h6 : s₀ ∈ d.F := hJ₃ s₀ hs₀ (by rw [← Subtype.ext hye]; exact hy)
    exact mul_mem (h.F_map_le_yamadaF₄_S4C d hlay ⟨s₀, h6, rfl⟩) hg

theorem Q_decomp (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) {x : G}
    (hx : x ∈ yamadaP d t ⊔ zpowers t) : ∃ a ∈ yamadaR₅ d t, ∃ b ∈ yamadaR₆ d t, x = a * b := by
  have hR₅N : yamadaR₅ d t ≤ normalizer (yamadaR₆ d t : Set G) := by
    intro a ha
    refine Subgroup.mem_normalizer_fintype fun r hr => ?_
    have haQ := R₅_le_Q h d hlay ha
    have hrQ := R₆_le_Q h d hlay (SetLike.mem_coe.1 hr)
    have h1 := mul_mem (R₄_le_R₆ h d hlay
      (h.commutator_mem_yamadaR₄_of_mem_sup_PA d hlay haQ hrQ)) (SetLike.mem_coe.1 hr)
    rw [show a * r * a⁻¹ * r⁻¹ * r = a * r * a⁻¹ by group] at h1
    exact h1
  have hx' : x ∈ ((yamadaR₅ d t ⊔ yamadaR₆ d t : Subgroup G) : Set G) := by
    rw [← Q_eq h d hlay]
    exact hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hR₅N, Set.mem_mul] at hx'
  obtain ⟨a, ha, b, hb, hab⟩ := hx'
  exact ⟨a, ha, b, hb, hab.symm⟩

theorem NCS_le_normalizer_Q (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) ≤
      normalizer ((yamadaP d t ⊔ zpowers t : Subgroup G) : Set G) := by
  intro c hc
  rw [Q_eq h d hlay]
  exact Common.mem_normalizer_sup (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₅ d hc)
    (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₆ d hlay hc)

theorem NCS_le_normalizer_S₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaS₃ d t : Set G) := fun c hc =>
  Common.mem_normalizer_inf (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₃ d hlay hc)
    (Setup.mem_normalizer_centralizer_C8 (Subgroup.mem_inf.1 (h.normalizer_yamadaS₄_le_two d hlay
      (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (h.normalizer_yamadaR₄_le_of_layerHyp d hlay
        (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₄ d hlay hc))).1).1)).1)

theorem D₄_le_S₄ (d : TrialityD4Data L (2 ^ f)) : yamadaD₄ d t ≤ yamadaS₄ d t :=
  inf_le_inf_left _ (inf_le_right : yamadaD₅ d t ≤ centralizer (yamadaV₁ d t : Set G))

theorem mem_S₄_of_mem_P_of_mem_normalizer_S₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} (hxP : x ∈ yamadaP d t)
    (hxN : x ∈ normalizer (yamadaS₃ d t : Set G)) : x ∈ yamadaS₄ d t := by
  obtain ⟨j₀, hj₀, hJ₂, hJ₃⟩ := exists_torus_j d
  obtain ⟨hJ₂', hJ₃'⟩ := torus_transfer h d hlay hj₀ hJ₂ hJ₃
  have hjNCS : (j₀ : G) ∈ centralizer ({t} : Set G) ⊓
      normalizer ((d.S.map L.subtype : Subgroup G) : Set G) :=
    ⟨h.L_le_centralizer j₀.2, Setup.coe_mem_normalizer_map (d.J_le_normalizer_S hj₀)⟩
  have hxR₄ : x ∈ yamadaR₄ d t :=
    key_abstract (t := t) (j := (j₀ : G)) (Q := yamadaP d t ⊔ zpowers t) (R₄ := yamadaR₄ d t)
      (R₅ := yamadaR₅ d t) (R₆ := yamadaR₆ d t) (F := yamadaF₄ d t) (S := yamadaS₄ d t)
      (M := yamadaM₄ d t) (D := yamadaD₄ d t) (Nrm := normalizer (yamadaS₃ d t : Set G))
      (Subgroup.mem_centralizer_singleton_iff.1 hjNCS.1) (fun _ hx => Q_decomp h d hlay hx)
      inf_le_left (R₄_le_R₆ h d hlay) (R₅_le_Q h d hlay) (R₆_le_Q h d hlay)
      (Q_le_normalizer_R₄ h d hlay)
      (fun _ hx _ hy => h.commutator_mem_yamadaR₄_of_mem_sup_PA d hlay hx hy)
      (Q_le_normalizer_S₄ h d hlay) (S₄_le_normalizer_F₄ h d hlay)
      (h.yamada_5_32_of_layerHyp d hlay).2.2.2.2.2.2.2
      (fun _ hy _ hc hyt => mem_R₄_of_conj_t h d hlay hy hc hyt)
      (fun _ ha => by
        obtain ⟨δ, hδ, e⟩ := conj_t_of_mem_R₅ h d hlay ha
        exact ⟨δ, h.yamadaD₁_le_yamadaD₄_S4C d hlay hδ, e⟩)
      (fun _ hb => by
        obtain ⟨m, hm, e⟩ := conj_t_of_mem_R₆ h d hlay hb
        exact ⟨m, h.yamadaM₃_le_yamadaM₄_R5 d hlay hm, e⟩)
      (fun _ hr => conj_t_of_mem_R₄ h d hlay hr) (D₄_le_S₄ d) (Setup.yamadaM₄_le_yamadaS₄_R4 d t)
      (NCS_le_normalizer_Q h d hlay hjNCS)
      (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₆ d hlay hjNCS)
      (NCS_le_normalizer_S₃ h d hlay hjNCS) hJ₂' hJ₃'
      (fun _ ha haN => mem_R₄_of_mem_R₅_of_mem_normalizer_S₃ h d hlay ha haN)
      (fun _ hb hbN => mem_R₄_of_mem_R₆_of_mem_normalizer_S₃ h d hlay hb hbN)
      x (Subgroup.mem_sup_left hxP) hxN
  exact Subgroup.mem_inf.2 ⟨hxR₄, yamadaP_le_centralizer_yamadaV₁ d t hxP⟩

theorem Y₂_le_W₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaY₂ d t ≤ yamadaW₃ d t :=
  (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t).trans (h.yamadaW₂_le_yamadaW₃_S4C d hlay)

theorem V₁_le_W₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaV₁ d t ≤ yamadaW₃ d t :=
  (Setup.yamadaV₁_le_yamadaY₂ (t := t) d).trans (Y₂_le_W₃ h d hlay)

theorem W₃_le_S₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaW₃ d t ≤ yamadaS₃ d t :=
  le_inf ((inf_le_left : yamadaW₃ d t ≤ yamadaL₃ d t).trans (h.yamadaL₃_le_yamadaR₃_D3 d hlay))
    ((h.yamadaW₃_le_yamadaD₅_PA d hlay).trans inf_le_right)

theorem S₄_le_P (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaS₄ d t ≤ yamadaP d t := by
  rw [h.yamadaS₄_eq_sup_yamadaD₄ d hlay]
  exact sup_le ((h.yamadaM₄_le_yamadaM₆ d hlay).trans (yamadaM₆_le_yamadaP d t))
    ((inf_le_right : yamadaD₄ d t ≤ yamadaD₅ d t).trans (yamadaD₅_le_yamadaP d t))

theorem S₃_le_S₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaS₃ d t ≤ yamadaS₄ d t :=
  inf_le_inf_right _ (h.yamadaR₃_le_yamadaR₄_R5 d hlay)

theorem commutator_V₁_P (d : TrialityD4Data L (2 ^ f)) {x y : G} (hx : x ∈ yamadaV₁ d t)
    (hy : y ∈ yamadaP d t) : x * y * x⁻¹ * y⁻¹ ∈ (⊥ : Subgroup G) := by
  rw [Subgroup.mem_bot, show x * y = y * x from Subgroup.mem_centralizer_iff.1
    (yamadaP_le_centralizer_yamadaV₁ d t hy) x hx]
  group

theorem commutator_Y₂_P (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d)
    {x y : G} (hx : x ∈ yamadaY₂ d t) (hy : y ∈ yamadaP d t) :
    x * y * x⁻¹ * y⁻¹ ∈ yamadaV₁ d t := by
  have hD₅Y₂ : yamadaY₂ d t ≤ yamadaD₅ d t :=
    (Y₂_le_W₃ h d hlay).trans (h.yamadaW₃_le_yamadaD₅_PA d hlay)
  have hV₁N : ∀ g ∈ yamadaP d t, g ∈ normalizer (yamadaV₁ d t : Set G) := fun g hg =>
    Subgroup.centralizer_le_normalizer _ (yamadaP_le_centralizer_yamadaV₁ d t hg)
  have hle : yamadaP d t ≤ modCentralizerSub (yamadaY₂ d t) (yamadaV₁ d t) := by
    refine sup_le (fun y hy => ⟨hV₁N y (yamadaD₅_le_yamadaP d t hy), fun a ha => ?_⟩)
      (fun y hy => ⟨hV₁N y (yamadaM₆_le_yamadaP d t hy), fun a ha => ?_⟩)
    · exact h.commutator_mem_yamadaV₁_of_mem_yamadaD₅_PA d hlay hy (hD₅Y₂ ha)
    · have hmC : y ∈ centralizer (yamadaY₂ d t : Set G) :=
        (inf_le_right : yamadaM₆ d t ≤ centralizer (yamadaY₂ d t : Set G)) hy
      have e : y * a * y⁻¹ * a⁻¹ = 1 := by
        rw [← Subgroup.mem_centralizer_iff.1 hmC a ha]
        group
      rw [e]
      exact one_mem _
  exact comm_swap_mem_R4 ((mem_modCentralizerSub.1 (hle hy)).2 x hx)

theorem commutator_W₃_P (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d)
    {x y : G} (hx : x ∈ yamadaW₃ d t) (hy : y ∈ yamadaP d t) :
    x * y * x⁻¹ * y⁻¹ ∈ yamadaY₂ d t :=
  comm_swap_mem_R4 (h.commutator_mem_yamadaY₂_of_mem_yamadaP d hlay y hy x hx)

theorem commutator_F₄_P (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d)
    {x y : G} (hx : x ∈ yamadaF₄ d t) (hy : y ∈ yamadaP d t) :
    x * y * x⁻¹ * y⁻¹ ∈ yamadaW₃ d t := by
  have hle : yamadaP d t ≤ modCentralizerSub (yamadaF₄ d t) (yamadaW₃ d t) := by
    refine sup_le (fun y hy => ⟨h.yamadaP_le_normalizer_yamadaW₃_PA d hlay
      (yamadaD₅_le_yamadaP d t hy), fun a ha => ?_⟩)
      (fun y hy => ⟨h.yamadaP_le_normalizer_yamadaW₃_PA d hlay (yamadaM₆_le_yamadaP d t hy),
        fun a ha => ?_⟩)
    · exact V₁_le_W₃ h d hlay (h.commutator_mem_yamadaV₁_of_mem_yamadaD₅_PA d hlay hy
        (Setup.yamadaF₄_le_yamadaD₅_PA d ha))
    · exact h.commutator_mem_yamadaW₃_of_mem_yamadaM₆ d hlay hy
        (h.yamadaF₄_le_yamadaM₆_PA d hlay ha)
  exact comm_swap_mem_R4 ((mem_modCentralizerSub.1 (hle hy)).2 x hx)

theorem mem_iff_of_commutator (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {A B : Subgroup G} (hAS₃ : A ≤ yamadaS₃ d t)
    (hBS₄ : B ≤ yamadaS₄ d t)
    (hB : ∀ x, x ∈ B ↔ x ∈ yamadaS₄ d t ∧ ∀ y ∈ yamadaS₄ d t, x * y * x⁻¹ * y⁻¹ ∈ A)
    (hlow : ∀ x ∈ B, ∀ y ∈ yamadaP d t, x * y * x⁻¹ * y⁻¹ ∈ A) (x : G) :
    x ∈ B ↔ x ∈ yamadaP d t ∧ ∀ y ∈ yamadaP d t, x * y * x⁻¹ * y⁻¹ ∈ A := by
  constructor
  · intro hx
    exact ⟨S₄_le_P h d hlay (hBS₄ hx), hlow x hx⟩
  · rintro ⟨hxP, hxc⟩
    have hxN : x ∈ normalizer (yamadaS₃ d t : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun s hs => ?_
      have hsP : s ∈ yamadaP d t := S₄_le_P h d hlay (S₃_le_S₄ h d hlay (SetLike.mem_coe.1 hs))
      have h1 := mul_mem (hAS₃ (hxc s hsP)) (SetLike.mem_coe.1 hs)
      rw [show x * s * x⁻¹ * s⁻¹ * s = x * s * x⁻¹ by group] at h1
      exact h1
    have hxS₄ := mem_S₄_of_mem_P_of_mem_normalizer_S₃ h d hlay hxP hxN
    exact (hB x).2 ⟨hxS₄, fun y hy => hxc y (S₄_le_P h d hlay hy)⟩

end Concrete

end ProductToolboxAux.P02

theorem ProductToolboxAux.P02.main (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    (Subgroup.upperCentralSeries ↥(yamadaP d t) 1).map (yamadaP d t).subtype = yamadaV₁ d t ∧
      (Subgroup.upperCentralSeries ↥(yamadaP d t) 2).map (yamadaP d t).subtype = yamadaY₂ d t ∧
      (Subgroup.upperCentralSeries ↥(yamadaP d t) 3).map (yamadaP d t).subtype = yamadaW₃ d t ∧
      (Subgroup.upperCentralSeries ↥(yamadaP d t) 4).map (yamadaP d t).subtype = yamadaF₄ d t := by
  have hM₄ := h.commutator_mem_yamadaY₂_of_mem_yamadaM₄ d hlay
  have hF₄ : ∀ x ∈ yamadaF₄ d t, ∀ y ∈ yamadaS₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaW₃ d t :=
    fun _ hx _ hy => h.commutator_mem_yamadaW₃_of_mem_yamadaF₄ d hlay hx hy
  have hS₄ := h.yamadaS₄_eq_yamadaF₄_sup_S d hlay
  have hV₁S₃ : yamadaV₁ d t ≤ yamadaS₃ d t := (V₁_le_W₃ h d hlay).trans (W₃_le_S₃ h d hlay)
  have hY₂S₃ : yamadaY₂ d t ≤ yamadaS₃ d t := (Y₂_le_W₃ h d hlay).trans (W₃_le_S₃ h d hlay)
  have h1 := map_upperCentralSeries_succ (map_upperCentralSeries_zero (yamadaP d t))
    (mem_iff_of_commutator h d hlay (A := ⊥) bot_le (h.yamadaV₁_le_yamadaS₄_S4C d hlay)
      (fun _ => h.mem_yamadaV₁_iff_S4C d hlay) (fun _ hx _ hy => commutator_V₁_P d hx hy))
  have h2 := map_upperCentralSeries_succ h1
    (mem_iff_of_commutator h d hlay hV₁S₃
      ((le_sup_right : yamadaY₂ d t ≤ yamadaS₂ d t).trans (h.yamadaS₂_le_yamadaS₄_S4C d hlay))
      (fun _ => h.mem_yamadaY₂_iff_S4C d hlay) (fun _ hx _ hy => commutator_Y₂_P h d hlay hx hy))
  have h3 := map_upperCentralSeries_succ h2
    (mem_iff_of_commutator h d hlay hY₂S₃ (h.yamadaW₃_le_yamadaS₄_R4 d hlay)
      (fun _ => h.mem_yamadaW₃_iff_S4C d hlay hM₄)
      (fun _ hx _ hy => commutator_W₃_P h d hlay hx hy))
  have h4 := map_upperCentralSeries_succ h3
    (mem_iff_of_commutator h d hlay (W₃_le_S₃ h d hlay) (Setup.yamadaF₄_le_yamadaS₄_S4C d t)
      (fun _ => h.mem_yamadaF₄_iff_S4C d hlay hF₄ hS₄)
      (fun _ hx _ hy => commutator_F₄_P h d hlay hx hy))
  exact ⟨h1, h2, h3, h4⟩

end P02

theorem S5_upperCentralSeries_P (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    (Subgroup.upperCentralSeries ↥(yamadaP d t) 1).map (yamadaP d t).subtype = yamadaV₁ d t ∧
      (Subgroup.upperCentralSeries ↥(yamadaP d t) 2).map (yamadaP d t).subtype = yamadaY₂ d t ∧
      (Subgroup.upperCentralSeries ↥(yamadaP d t) 3).map (yamadaP d t).subtype = yamadaW₃ d t ∧
      (Subgroup.upperCentralSeries ↥(yamadaP d t) 4).map (yamadaP d t).subtype = yamadaF₄ d t :=
  ProductToolboxAux.P02.main h d hlay

theorem S5_commutator_M₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : ⁅yamadaM₆ d t, yamadaM₆ d t⁆ = yamadaW₃ d t :=
  ProductToolboxAux.P03.commutator h d hlay

theorem S5_u_centralizes_V₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : uG d ∈ centralizer (yamadaV₁ d t : Set G) :=
  ProductToolboxAux.P03.u_centralizes h d hlay

end Inputs

section Series

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

@[expose] def jZeroG {q : ℕ} (d : TrialityD4Data L q) : Subgroup G :=
  d.J₀.map L.subtype

@[expose] def FreeLifted (t : G) (A B : Subgroup G) : Prop :=
  IsElemSection A B ∧ IsFreeSection t A B ∧
    A ⊓ centralizerMod B (zpowers t) = (A ⊓ centralizer ({t} : Set G)) ⊔ B

namespace ProductToolboxAux

open Core

theorem isFreeSection_iff_card {t : G} {A B : Subgroup G} (hAB : IsElemSection A B)
    (ht : t * t = 1) (htB : t ∈ normalizer (B : Set G)) :
    IsFreeSection t A B ↔ Nat.card A * Nat.card B =
      Nat.card (A ⊓ centralizerMod B (zpowers t) : Subgroup G) ^ 2 := by
  set X := A ⊓ centralizerMod B (zpowers t) with hX
  have hBX : B ≤ X := le_inf_centralizerMod_zpowers hAB ht htB
  have hXA : X ≤ A := inf_le_left
  have h1 := relIndex_mul_card (H := B) (K := A)
  have h2 := relIndex_mul_card (H := B) (K := X)
  rw [inf_of_le_left hAB.le] at h1
  rw [inf_of_le_left hBX] at h2
  have hpos : 0 < Nat.card B := Nat.card_pos
  rw [IsFreeSection]
  show B.relIndex A = (B.relIndex X) ^ 2 ↔ _
  rw [← h1, ← h2]
  constructor
  · intro h
    rw [h]; ring
  · intro h
    apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hpos hpos)
    nlinarith [h]

theorem h1Zero_bot (t : G) : H1Zero t ⊥ := by
  intro n hn _
  rw [mem_bot.1 hn]
  exact ⟨1, one_mem _, by simp⟩

theorem freeLifted_of_card {t : G} (ht : t * t = 1) {A B : Subgroup G} (hAB : IsElemSection A B)
    (htA : t ∈ normalizer (A : Set G)) (htB : t ∈ normalizer (B : Set G)) (hH1 : H1Zero t B)
    (hcard : Nat.card A * Nat.card (B ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2 =
      Nat.card B * Nat.card (A ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2) :
    FreeLifted t A B := by
  have hlift : A ⊓ centralizerMod B (zpowers t) = (A ⊓ centralizer ({t} : Set G)) ⊔ B := by
    refine le_antisymm (fun x hx => ?_) (sup_le (fun a ha => ?_)
      (le_inf_centralizerMod_zpowers hAB ht htB))
    · obtain ⟨hxA, hxc⟩ := (mem_inf_centralizerMod_zpowers_iff hAB ht htB).1 hx
      exact T2_lift ht hAB.le (le_normalizer hAB) htA htB hH1 x hxA hxc
    · obtain ⟨haA, haC⟩ := mem_inf.1 ha
      refine (mem_inf_centralizerMod_zpowers_iff hAB ht htB).2 ⟨haA, ?_⟩
      have h1 : t * a = a * t := (mem_centralizer_singleton_iff.1 haC).symm
      rw [h1, mul_inv_cancel_right, inv_mul_cancel]
      exact one_mem B
  refine ⟨hAB, ?_, hlift⟩
  rw [isFreeSection_iff_card hAB ht htB]
  set X := A ⊓ centralizerMod B (zpowers t) with hX
  have h1 := card_sup_mul_card_inf_eq (A := B) (B := A ⊓ centralizer ({t} : Set G))
    (fun x hx => le_normalizer hAB (mem_inf.1 hx).1)
  rw [sup_comm, ← hlift, ← inf_assoc, inf_of_le_left hAB.le] at h1
  have hd : 0 < Nat.card (B ⊓ centralizer ({t} : Set G) : Subgroup G) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right (pow_pos hd 2)
  calc Nat.card A * Nat.card B * Nat.card (B ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2
      = Nat.card B * (Nat.card A * Nat.card (B ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2) := by
        ring
    _ = Nat.card B * (Nat.card B * Nat.card (A ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2) := by
        rw [hcard]
    _ = (Nat.card B * Nat.card (A ⊓ centralizer ({t} : Set G) : Subgroup G)) ^ 2 := by ring
    _ = (Nat.card X * Nat.card (B ⊓ centralizer ({t} : Set G) : Subgroup G)) ^ 2 := by rw [h1]
    _ = Nat.card X ^ 2 * Nat.card (B ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2 := by ring

theorem h1Zero_of_freeLifted {t : G} (ht : t * t = 1) {A B : Subgroup G}
    (htA : t ∈ normalizer (A : Set G)) (htB : t ∈ normalizer (B : Set G)) (hH1 : H1Zero t B)
    (hF : FreeLifted t A B) : H1Zero t A :=
  T2_h1_zero ht hF.1.le (le_normalizer hF.1) htA htB hH1 (T1_h1_zero hF.1 ht htA htB hF.2.1)

end ProductToolboxAux

section P04

set_option hygiene false in
local macro "layer_ctx_P04" : tactic => `(tactic| (
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  have h59e := h.yamadaY₂_eq d hlay
  have h520 := h.yamada_5_20 d hlay
  have h5221 := h.yamada_5_22_1 d hlay
  have h521 := h.yamada_5_21 d hlay))

namespace ProductToolboxAux.P04

theorem V₁_inf_centralizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaV₁ d t ⊓ centralizer ({t} : Set G) = d.V.map L.subtype :=
  (h.yamada_5_6_2 d hlay).2.2.1

theorem Y₂_inf_centralizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaY₂ d t ⊓ centralizer ({t} : Set G) = d.Y.map L.subtype :=
  (h.yamada_5_9_2 d hlay).2.2.2.2

theorem W₃_inf_centralizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaW₃ d t ⊓ centralizer ({t} : Set G) = d.W.map L.subtype := by
  layer_ctx_P04
  exact h.yamadaW₃_inf_centralizer_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102

theorem F₄_inf_centralizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaF₄ d t ⊓ centralizer ({t} : Set G) = d.F.map L.subtype := by
  refine le_antisymm (fun x hx => ?_) (le_inf (h.F_map_le_yamadaF₄_S4C d hlay)
    ((map_subtype_le _).trans h.L_le_centralizer))
  obtain ⟨hxF, hxC⟩ := mem_inf.1 hx
  have hxS : x ∈ d.S.map L.subtype := by
    have : x ∈ yamadaP d t ⊓ centralizer ({t} : Set G) :=
      ⟨yamadaD₅_le_yamadaP d t (Setup.yamadaF₄_le_yamadaD₅_PA d hxF), hxC⟩
    rwa [yamadaP_inf_centralizer h d hlay] at this
  rw [← h.S_map_inf_yamadaF₄ d hlay]
  exact ⟨hxS, hxF⟩

theorem D_map_le_D₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    d.D.map L.subtype ≤ yamadaD₅ d t :=
  le_inf ((h.D_map_le_yamadaC₁ d).trans (yamadaC₁_le_yamadaC₅ d t))
    ((map_mono d.D_le_S).trans (h.S_map_le_centralizer_yamadaV₁ d hlay))

theorem D₅_inf_centralizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaD₅ d t ⊓ centralizer ({t} : Set G) = d.D.map L.subtype := by
  layer_ctx_P04
  refine le_antisymm (fun x hx => ?_) (le_inf (D_map_le_D₅ h d hlay)
    ((map_subtype_le _).trans h.L_le_centralizer))
  obtain ⟨hxD, hxC⟩ := mem_inf.1 hx
  have h1 : x ∈ d.D.map L.subtype ⊔ zpowers t := by
    rw [← (h.yamada_5_12 d hNH h561 h562 h591 h592 h593).1.2.2.2]
    exact ⟨(inf_le_left : yamadaD₅ d t ≤ yamadaC₅ d t) hxD, hxC⟩
  rcases (h.mem_sup_zpowers_iff_of_normalizer (h.t_mem_normalizer_map d.D)).1 h1 with h2 | h2
  · exact h2
  · exfalso
    have := mul_mem (D_map_le_D₅ h d hlay h2) (inv_mem hxD)
    rw [mul_inv_cancel_right] at this
    exact h.t_not_mem_yamadaP d hlay (yamadaD₅_le_yamadaP d t this)

theorem M_map_le_M₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    d.M.map L.subtype ≤ yamadaM₆ d t :=
  ((h.yamadaM₄_eq_sup d hlay ▸ le_sup_left : d.M.map L.subtype ≤ yamadaM₄ d t)).trans
    (h.yamadaM₄_le_yamadaM₆ d hlay)

theorem M₆_inf_centralizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaM₆ d t ⊓ centralizer ({t} : Set G) = d.M.map L.subtype := by
  refine le_antisymm (fun x hx => ?_) (le_inf (M_map_le_M₆ h d hlay)
    ((map_subtype_le _).trans h.L_le_centralizer))
  obtain ⟨hxM, hxC⟩ := mem_inf.1 hx
  have hxS : x ∈ d.S.map L.subtype := by
    have : x ∈ yamadaP d t ⊓ centralizer ({t} : Set G) := ⟨yamadaM₆_le_yamadaP d t hxM, hxC⟩
    rwa [yamadaP_inf_centralizer h d hlay] at this
  obtain ⟨s, hs, rfl⟩ := hxS
  have hxY₂ : (s : G) ∈ centralizer (yamadaY₂ d t : Set G) :=
    (inf_le_right : yamadaM₆ d t ≤ centralizer (yamadaY₂ d t : Set G)) hxM
  have hsY : s ∈ d.S ⊓ centralizer (d.Y : Set L) := by
    refine mem_inf.2 ⟨hs, mem_centralizer_iff.2 fun y hy => Subtype.ext ?_⟩
    exact mem_centralizer_iff.1 hxY₂ (y : G) (h.Y_map_le_yamadaY₂ d hlay ⟨y, hy, rfl⟩)
  rw [d.S_inf_centralizer_Y] at hsY
  exact ⟨s, hsY, rfl⟩

theorem P_inf_centralizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaP d t ⊓ centralizer ({t} : Set G) = d.S.map L.subtype :=
  yamadaP_inf_centralizer h d hlay

theorem t_mem_normalizer_W₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : t ∈ normalizer (yamadaW₃ d t : Set G) := by
  layer_ctx_P04
  exact h.t_mem_normalizer_yamadaW₃_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102

theorem t_mem_normalizer_M₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : t ∈ normalizer (yamadaM₆ d t : Set G) := by
  have htL₆ : t ∈ yamadaL₆ d t := by
    rw [(h.yamada_5_29_1_of_layerHyp d hlay).1]
    exact mem_sup_right (mem_zpowers t)
  exact Common.mem_normalizer_inf (Subgroup.le_normalizer htL₆)
    (Setup.mem_normalizer_centralizer_C8 (h.t_mem_normalizer_yamadaY₂ d))

theorem t_mem_normalizer_bot (t : G) : t ∈ normalizer ((⊥ : Subgroup G) : Set G) := by
  rw [normalizer_eq_top]
  exact mem_top t

theorem isElemSection_of_comm_sq {A B : Subgroup G} (hBA : B ≤ A)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hsq : ∀ x ∈ A, x * x = 1) :
    IsElemSection A B where
  le := hBA
  mul_self_mem x hx := by rw [hsq x hx]; exact one_mem B
  commutator_mem x hx y hy := by
    rw [hcomm x hx y hy, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem B

theorem isElemSection_of_isElemAbelian {A B : Subgroup G} (hBA : B ≤ A)
    (hA : IsElemAbelian 2 A) : IsElemSection A B :=
  isElemSection_of_comm_sq hBA (mul_comm_of_isMulCommutative_D4 hA.1) fun x hx => by
    rw [← pow_two]
    exact hA.2 x hx

theorem isElemSection_V₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : IsElemSection (yamadaV₁ d t) ⊥ :=
  isElemSection_of_isElemAbelian bot_le (h.yamada_5_6_2 d hlay).1

theorem isElemSection_Y₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : IsElemSection (yamadaY₂ d t) (yamadaV₁ d t) :=
  isElemSection_of_comm_sq (Setup.yamadaV₁_le_yamadaY₂ d)
    (mul_comm_of_isMulCommutative_D4 (h.yamada_5_9_2 d hlay).2.2.1)
    fun _ hx => h.mul_self_eq_one_of_mem_yamadaY₂ d hlay hx

theorem Y₂_le_W₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaY₂ d t ≤ yamadaW₃ d t :=
  (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t).trans (h.yamadaW₂_le_yamadaW₃ d hlay)

theorem isElemSection_W₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : IsElemSection (yamadaW₃ d t) (yamadaY₂ d t) :=
  isElemSection_of_isElemAbelian (Y₂_le_W₃ h d hlay) (h.yamada_5_21 d hlay).2.1

theorem isElemSection_F₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : IsElemSection (yamadaF₄ d t) (yamadaW₃ d t) where
  le := h.yamadaW₃_le_yamadaF₄_R5 d hlay
  mul_self_mem _ hx := h.mul_self_mem_yamadaW₃_of_mem_yamadaF₄_S4 d hlay hx
  commutator_mem _ hx _ hy :=
    h.commutator_mem_yamadaW₃_of_mem_yamadaF₄ d hlay hx (Setup.yamadaF₄_le_yamadaS₄ (t := t) d hy)

theorem isElemSection_D₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : IsElemSection (yamadaD₅ d t) (yamadaF₄ d t) where
  le := Setup.yamadaF₄_le_yamadaD₅_PA d
  mul_self_mem _ hx := h.yamadaV₁_le_yamadaF₄_R5 d hlay
    (h.mul_self_mem_yamadaV₁_of_mem_yamadaD₅_PA d hlay hx)
  commutator_mem _ hx _ hy := h.yamadaV₁_le_yamadaF₄_R5 d hlay
    (h.commutator_mem_yamadaV₁_of_mem_yamadaD₅_PA d hlay hx hy)

theorem isElemSection_M₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : IsElemSection (yamadaM₆ d t) (yamadaF₄ d t) where
  le := h.yamadaF₄_le_yamadaM₆_PA d hlay
  mul_self_mem _ hx := h.yamadaW₃_le_yamadaF₄_R5 d hlay
    (h.mul_self_mem_yamadaW₃_of_mem_yamadaM₆ d hlay hx)
  commutator_mem _ hx _ hy := h.yamadaW₃_le_yamadaF₄_R5 d hlay
    (h.commutator_mem_yamadaW₃_of_mem_yamadaM₆ d hlay hx hy)

theorem isElemSection_P_D₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : IsElemSection (yamadaP d t) (yamadaD₅ d t) where
  le := yamadaD₅_le_yamadaP d t
  mul_self_mem _ hx := Setup.yamadaF₄_le_yamadaD₅_PA d
    (h.mul_self_mem_yamadaF₄_of_mem_yamadaP d hlay hx)
  commutator_mem _ hx _ hy := Setup.yamadaF₄_le_yamadaD₅_PA d
    (h.commutator_mem_yamadaF₄_of_mem_yamadaP d hlay hx hy)

theorem isElemSection_P_M₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : IsElemSection (yamadaP d t) (yamadaM₆ d t) where
  le := yamadaM₆_le_yamadaP d t
  mul_self_mem _ hx := h.yamadaF₄_le_yamadaM₆_PA d hlay
    (h.mul_self_mem_yamadaF₄_of_mem_yamadaP d hlay hx)
  commutator_mem _ hx _ hy := h.yamadaF₄_le_yamadaM₆_PA d hlay
    (h.commutator_mem_yamadaF₄_of_mem_yamadaP d hlay hx hy)

theorem card_sup_eq_pow {A B : Subgroup G} (hB : B ≤ normalizer (A : Set G)) {q a b c e : ℕ}
    (hq : 0 < q) (hA : Nat.card A = q ^ a) (hB' : Nat.card B = q ^ b)
    (hAB : Nat.card (A ⊓ B : Subgroup G) = q ^ c) (h : a + b = c + e) :
    Nat.card (A ⊔ B : Subgroup G) = q ^ e := by
  have h1 := card_sup_mul_card_inf_eq hB
  rw [hA, hB', hAB, ← pow_add, h, pow_add] at h1
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hq c) (h1.trans (mul_comm _ _))

theorem card_map_conj (H : Subgroup G) (g : G) :
    Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
  card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective

theorem card_D₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    Nat.card (yamadaD₅ d t) = (2 ^ f) ^ 18 := by
  layer_ctx_P04
  obtain ⟨-, -, -, hD₅, hWu, hN, -⟩ :=
    h.yamada_5_25 d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 h521
  have hWuD : (yamadaW₃ d t).map (MulAut.conj ((d.u : L) : G)).toMonoidHom ≤ yamadaD₅ d t := by
    rw [hD₅]
    exact le_sup_right
  have := card_sup_eq_pow (hB := fun x hx => hN (hWuD hx)) (q := 2 ^ f) (a := 10) (b := 10)
    (c := 2) (e := 18) (by positivity) h521.2.2 (by rw [card_map_conj]; exact h521.2.2)
    (by rw [hWu]; exact h562.2.1) (by norm_num)
  rwa [← hD₅] at this

theorem M₆_eq_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaM₆ d t = yamadaF₄ d t ⊔
      (yamadaF₄ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom := by
  refine le_antisymm (h.yamadaM₆_le_sup_map_conj_yamadaF₄_PA d hlay)
    (sup_le (h.yamadaF₄_le_yamadaM₆_PA d hlay) ?_)
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_normalizer_iff.1 (h.v_mem_normalizer_yamadaM₆_PA d hlay) x).1
    (h.yamadaF₄_le_yamadaM₆_PA d hlay hx)

theorem F₄_inf_map_conj_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaF₄ d t ⊓ (yamadaF₄ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom =
      yamadaW₃ d t := by
  refine le_antisymm (h.yamadaF₄_inf_map_conj_le_yamadaW₃_PA d hlay)
    (le_inf (h.yamadaW₃_le_yamadaF₄_R5 d hlay) fun w hw => ?_)
  rw [mem_map_conj_iff_D4]
  exact h.yamadaW₃_le_yamadaF₄_R5 d hlay
    ((mem_normalizer_iff''.1 (h.v_mem_normalizer_yamadaW₃ d) w).1 hw)

theorem card_M₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    Nat.card (yamadaM₆ d t) = (2 ^ f) ^ 22 := by
  have hvF : (yamadaF₄ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom ≤ yamadaM₆ d t := by
    rw [M₆_eq_sup h d hlay]
    exact le_sup_right
  rw [M₆_eq_sup h d hlay]
  exact card_sup_eq_pow (A := yamadaF₄ d t)
    (B := (yamadaF₄ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom)
    (fun x hx => h.yamadaP_le_normalizer_yamadaF₄_PA d hlay
      (yamadaM₆_le_yamadaP d t (hvF hx))) (q := 2 ^ f) (a := 16) (b := 16) (c := 10) (e := 22)
    (by positivity) (h.card_yamadaF₄ d hlay) (by rw [card_map_conj]; exact h.card_yamadaF₄ d hlay)
    (by rw [F₄_inf_map_conj_eq h d hlay]; exact (h.yamada_5_21 d hlay).2.2) (by norm_num)

theorem card_P (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    Nat.card (yamadaP d t) = (2 ^ f) ^ 24 :=
  card_sup_eq_pow (A := yamadaD₅ d t) (B := yamadaM₆ d t)
    (h.yamadaM₆_le_normalizer_yamadaD₅ d hlay) (q := 2 ^ f) (a := 18) (b := 22) (c := 16)
    (e := 24) (by positivity) (card_D₅ h d hlay) (card_M₆ h d hlay)
    (by rw [h.yamadaD₅_inf_yamadaM₆_eq d hlay]; exact h.card_yamadaF₄ d hlay) (by norm_num)

theorem step {t : G} (ht : t * t = 1) {A B : Subgroup G} {E E' : Subgroup L}
    {q α β γ δ : ℕ} (hAB : IsElemSection A B) (htA : t ∈ normalizer (A : Set G))
    (htB : t ∈ normalizer (B : Set G)) (hH1 : H1Zero t B) (hA : Nat.card A = q ^ α)
    (hB : Nat.card B = q ^ β) (hAC : A ⊓ centralizer ({t} : Set G) = E.map L.subtype)
    (hBC : B ⊓ centralizer ({t} : Set G) = E'.map L.subtype) (hE : Nat.card E = q ^ γ)
    (hE' : Nat.card E' = q ^ δ) (hexp : α + 2 * δ = β + 2 * γ) :
    FreeLifted t A B ∧ H1Zero t A := by
  have hF : FreeLifted t A B := by
    refine freeLifted_of_card ht hAB htA htB hH1 ?_
    rw [hAC, hBC, card_map_of_injective L.subtype_injective,
      card_map_of_injective L.subtype_injective, hA, hB, hE, hE', ← pow_mul, ← pow_mul,
      ← pow_add, ← pow_add]
    congr 1
    omega
  exact ⟨hF, h1Zero_of_freeLifted ht htA htB hH1 hF⟩

theorem main (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    yamadaV₁ d t ⊓ centralizer ({t} : Set G) = d.V.map L.subtype ∧
      yamadaY₂ d t ⊓ centralizer ({t} : Set G) = d.Y.map L.subtype ∧
      yamadaW₃ d t ⊓ centralizer ({t} : Set G) = d.W.map L.subtype ∧
      yamadaF₄ d t ⊓ centralizer ({t} : Set G) = d.F.map L.subtype ∧
      yamadaD₅ d t ⊓ centralizer ({t} : Set G) = d.D.map L.subtype ∧
      yamadaM₆ d t ⊓ centralizer ({t} : Set G) = d.M.map L.subtype ∧
      yamadaP d t ⊓ centralizer ({t} : Set G) = d.S.map L.subtype ∧
      Nat.card (yamadaD₅ d t) = (2 ^ f) ^ 18 ∧ Nat.card (yamadaM₆ d t) = (2 ^ f) ^ 22 ∧
      Nat.card (yamadaP d t) = (2 ^ f) ^ 24 ∧
      FreeLifted t (yamadaV₁ d t) ⊥ ∧ FreeLifted t (yamadaY₂ d t) (yamadaV₁ d t) ∧
      FreeLifted t (yamadaW₃ d t) (yamadaY₂ d t) ∧ FreeLifted t (yamadaF₄ d t) (yamadaW₃ d t) ∧
      FreeLifted t (yamadaD₅ d t) (yamadaF₄ d t) ∧ FreeLifted t (yamadaP d t) (yamadaD₅ d t) ∧
      FreeLifted t (yamadaM₆ d t) (yamadaF₄ d t) ∧ FreeLifted t (yamadaP d t) (yamadaM₆ d t) := by
  have hlay := hp.layer
  have ht := h.t_mul_t
  have hV₁C := V₁_inf_centralizer h d hlay
  have hY₂C := Y₂_inf_centralizer h d hlay
  have hW₃C := W₃_inf_centralizer h d hlay
  have hF₄C := F₄_inf_centralizer h d hlay
  have hD₅C := D₅_inf_centralizer h d hlay
  have hM₆C := M₆_inf_centralizer h d hlay
  have hPC := P_inf_centralizer h d hlay
  have hcD₅ := card_D₅ h d hlay
  have hcM₆ := card_M₆ h d hlay
  have hcP := card_P h d hlay
  have hcV₁ : Nat.card (yamadaV₁ d t) = (2 ^ f) ^ 2 := (h.yamada_5_6_2 d hlay).2.1
  have hcY₂ : Nat.card (yamadaY₂ d t) = (2 ^ f) ^ 4 := (h.yamada_5_9_2 d hlay).2.1
  have hcW₃ : Nat.card (yamadaW₃ d t) = (2 ^ f) ^ 10 := (h.yamada_5_21 d hlay).2.2
  have hcF₄ : Nat.card (yamadaF₄ d t) = (2 ^ f) ^ 16 := h.card_yamadaF₄ d hlay
  have htV₁ := h.t_mem_normalizer_yamadaV₁ d
  have htY₂ := h.t_mem_normalizer_yamadaY₂ d
  have htW₃ := t_mem_normalizer_W₃ h d hlay
  have htF₄ := h.t_mem_normalizer_yamadaF₄ d hlay
  have htD₅ := h.t_mem_normalizer_yamadaD₅_C9 d
  have htM₆ := t_mem_normalizer_M₆ h d hlay
  have htP := h.t_mem_normalizer_yamadaP d hlay
  obtain ⟨f1, H1⟩ := step (L := L) (E := d.V) (E' := ⊥) (q := 2 ^ f) (α := 2) (β := 0)
    (γ := 1) (δ := 0) ht (isElemSection_V₁ h d hlay) htV₁ (t_mem_normalizer_bot t)
    (h1Zero_bot t) hcV₁ (by rw [Subgroup.card_bot, pow_zero]) hV₁C
    (by rw [bot_inf_eq, Subgroup.map_bot]) (by rw [d.card_V, pow_one])
    (by rw [Subgroup.card_bot, pow_zero]) (by norm_num)
  obtain ⟨f2, H2⟩ := step (L := L) (E := d.Y) (E' := d.V) (q := 2 ^ f) (α := 4) (β := 2)
    (γ := 2) (δ := 1) ht (isElemSection_Y₂ h d hlay) htY₂ htV₁ H1 hcY₂ hcV₁ hY₂C hV₁C d.card_Y
    (by rw [d.card_V, pow_one]) (by norm_num)
  obtain ⟨f3, H3⟩ := step (L := L) (E := d.W) (E' := d.Y) (q := 2 ^ f) (α := 10) (β := 4)
    (γ := 5) (δ := 2) ht (isElemSection_W₃ h d hlay) htW₃ htY₂ H2 hcW₃ hcY₂ hW₃C hY₂C d.card_W
    d.card_Y (by norm_num)
  obtain ⟨f4, H4⟩ := step (L := L) (E := d.F) (E' := d.W) (q := 2 ^ f) (α := 16) (β := 10)
    (γ := 8) (δ := 5) ht (isElemSection_F₄ h d hlay) htF₄ htW₃ H3 hcF₄ hcW₃ hF₄C hW₃C d.card_F
    d.card_W (by norm_num)
  obtain ⟨f5, H5⟩ := step (L := L) (E := d.D) (E' := d.F) (q := 2 ^ f) (α := 18) (β := 16)
    (γ := 9) (δ := 8) ht (isElemSection_D₅ h d hlay) htD₅ htF₄ H4 hcD₅ hcF₄ hD₅C hF₄C d.card_D
    d.card_F (by norm_num)
  obtain ⟨f6, -⟩ := step (L := L) (E := d.S) (E' := d.D) (q := 2 ^ f) (α := 24) (β := 18)
    (γ := 12) (δ := 9) ht (isElemSection_P_D₅ h d hlay) htP htD₅ H5 hcP hcD₅ hPC hD₅C d.card_S
    d.card_D (by norm_num)
  obtain ⟨f7, H7⟩ := step (L := L) (E := d.M) (E' := d.F) (q := 2 ^ f) (α := 22) (β := 16)
    (γ := 11) (δ := 8) ht (isElemSection_M₆ h d hlay) htM₆ htF₄ H4 hcM₆ hcF₄ hM₆C hF₄C d.card_M
    d.card_F (by norm_num)
  obtain ⟨f8, -⟩ := step (L := L) (E := d.S) (E' := d.M) (q := 2 ^ f) (α := 24) (β := 22)
    (γ := 12) (δ := 11) ht (isElemSection_P_M₆ h d hlay) htP htM₆ H7 hcP hcM₆ hPC hM₆C d.card_S
    d.card_M (by norm_num)
  exact ⟨hV₁C, hY₂C, hW₃C, hF₄C, hD₅C, hM₆C, hPC, hcD₅, hcM₆, hcP, f1, f2, f3, f4, f5, f6, f7, f8⟩

end ProductToolboxAux.P04

end P04

theorem T4_series_free (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    yamadaV₁ d t ⊓ centralizer ({t} : Set G) = d.V.map L.subtype ∧
      yamadaY₂ d t ⊓ centralizer ({t} : Set G) = d.Y.map L.subtype ∧
      yamadaW₃ d t ⊓ centralizer ({t} : Set G) = d.W.map L.subtype ∧
      yamadaF₄ d t ⊓ centralizer ({t} : Set G) = d.F.map L.subtype ∧
      yamadaD₅ d t ⊓ centralizer ({t} : Set G) = d.D.map L.subtype ∧
      yamadaM₆ d t ⊓ centralizer ({t} : Set G) = d.M.map L.subtype ∧
      yamadaP d t ⊓ centralizer ({t} : Set G) = d.S.map L.subtype ∧
      Nat.card (yamadaD₅ d t) = (2 ^ f) ^ 18 ∧ Nat.card (yamadaM₆ d t) = (2 ^ f) ^ 22 ∧
      Nat.card (yamadaP d t) = (2 ^ f) ^ 24 ∧
      FreeLifted t (yamadaV₁ d t) ⊥ ∧ FreeLifted t (yamadaY₂ d t) (yamadaV₁ d t) ∧
      FreeLifted t (yamadaW₃ d t) (yamadaY₂ d t) ∧ FreeLifted t (yamadaF₄ d t) (yamadaW₃ d t) ∧
      FreeLifted t (yamadaD₅ d t) (yamadaF₄ d t) ∧ FreeLifted t (yamadaP d t) (yamadaD₅ d t) ∧
      FreeLifted t (yamadaM₆ d t) (yamadaF₄ d t) ∧ FreeLifted t (yamadaP d t) (yamadaM₆ d t) :=
  ProductToolboxAux.P04.main h d hp

section P05

open scoped commutatorElement

namespace ProductToolboxAux.P05

section Abstract

variable {Γ : Type*} [Group Γ] [Finite Γ] {A B J E : Subgroup Γ} {τ : Γ}

theorem le_centralizerMod (hAB : IsElemSection A B) (hJB : J ≤ normalizer (B : Set Γ)) :
    B ≤ centralizerMod B J := fun b hb =>
  (mem_inf.1 (Core.le_inf_centralizerMod_of_le hAB hJB hb)).2

theorem mem_centralizerMod_of_commute (hAB : IsElemSection A B) (hJB : J ≤ normalizer (B : Set Γ))
    {x : Γ} (hx : x ∈ A) (hc : x ∈ centralizer (J : Set Γ)) : x ∈ centralizerMod B J := by
  rw [Core.mem_centralizerMod_iff_of_le hAB hJB hx]
  intro j hj
  have h1 : j * x = x * j := mem_centralizer_iff.1 hc j hj
  rw [show j * x * j⁻¹ = x by rw [h1]; group, inv_mul_cancel]
  exact one_mem B

theorem le_of_inf_centralizerMod_le (hAB : IsElemSection A B) (hτ : τ * τ = 1)
    (hτB : τ ∈ normalizer (B : Set Γ)) (hEA : E ≤ A) (hτE : ∀ x ∈ E, τ * x * τ⁻¹ ∈ E)
    (h : E ⊓ centralizerMod B (zpowers τ) ≤ B) : E ≤ B := by
  intro x hx
  have hτi : τ⁻¹ * τ⁻¹ = 1 := by rw [← mul_inv_rev, hτ, inv_one]
  have hyE : x⁻¹ * (τ * x * τ⁻¹) ∈ E := mul_mem (inv_mem hx) (hτE x hx)
  have hyc : x⁻¹ * (τ * x * τ⁻¹) ∈ centralizerMod B (zpowers τ) := by
    rw [Core.mem_centralizerMod_zpowers_iff hAB hτ hτB (hEA hyE)]
    have e : (x⁻¹ * (τ * x * τ⁻¹))⁻¹ * (τ * (x⁻¹ * (τ * x * τ⁻¹)) * τ⁻¹) =
        (x⁻¹ * (τ * x * τ⁻¹))⁻¹ * (x⁻¹ * (τ * x * τ⁻¹))⁻¹ := by
      have e1 : τ * (x⁻¹ * (τ * x * τ⁻¹)) * τ⁻¹ = τ * x⁻¹ * τ * x * (τ⁻¹ * τ⁻¹) := by group
      have e2 : (x⁻¹ * (τ * x * τ⁻¹))⁻¹ = τ * x⁻¹ * τ⁻¹ * x := by group
      have hτi' : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
      rw [e1, hτi, mul_one, e2, hτi']
    rw [e]
    exact hAB.mul_self_mem _ (inv_mem (hEA hyE))
  have hyB := h ⟨hyE, hyc⟩
  have hxc : x ∈ centralizerMod B (zpowers τ) := by
    rw [Core.mem_centralizerMod_zpowers_iff hAB hτ hτB (hEA hx)]
    exact hyB
  exact h ⟨hx, hxc⟩

theorem inf_centralizerMod_eq_of_fixed (hAB : IsElemSection A B) (hτ : τ * τ = 1)
    (hτA : τ ∈ normalizer (A : Set Γ)) (hτB : τ ∈ normalizer (B : Set Γ))
    (hJτ : J ≤ centralizer ({τ} : Set Γ)) (hJB : J ≤ normalizer (B : Set Γ))
    (hlift : A ⊓ centralizerMod B (zpowers τ) ≤ (A ⊓ centralizer ({τ} : Set Γ)) ⊔ B)
    (hfix : ∀ x ∈ A ⊓ centralizer ({τ} : Set Γ), x ∈ centralizerMod B J → x ∈ B) :
    A ⊓ centralizerMod B J = B := by
  refine le_antisymm ?_ (Core.le_inf_centralizerMod_of_le hAB hJB)
  have hτE := Core.mem_normalizer_inf_centralizerMod hAB hJB hτA hτB hJτ
  refine le_of_inf_centralizerMod_le hAB hτ hτB inf_le_left
    (fun x hx => (mem_normalizer_iff.1 hτE x).1 hx) ?_
  rintro z ⟨hzE, hzc⟩
  obtain ⟨hzA, hzJ⟩ := mem_inf.1 hzE
  have hz : z ∈ (A ⊓ centralizer ({τ} : Set Γ)) ⊔ B := hlift ⟨hzA, hzc⟩
  have hX : A ⊓ centralizer ({τ} : Set Γ) ≤ normalizer (B : Set Γ) :=
    inf_le_left.trans (Core.le_normalizer hAB)
  rw [← SetLike.mem_coe, sup_comm, coe_mul_of_right_le_normalizer_left B _ hX, Set.mem_mul] at hz
  obtain ⟨b, hb, x, hx, rfl⟩ := hz
  have hxJ : x ∈ centralizerMod B J := by
    have := mul_mem (inv_mem (le_centralizerMod hAB hJB hb)) hzJ
    rwa [inv_mul_cancel_left] at this
  exact mul_mem hb (hfix x hx hxJ)

theorem le_centralizerMod_of_fixed (hAB : IsElemSection A B) (hτ : τ * τ = 1)
    (hτA : τ ∈ normalizer (A : Set Γ)) (hτB : τ ∈ normalizer (B : Set Γ))
    (hJτ : J ≤ centralizer ({τ} : Set Γ)) (hJA : J ≤ normalizer (A : Set Γ))
    (hJB : J ≤ normalizer (B : Set Γ))
    (hlift : A ⊓ centralizerMod B (zpowers τ) ≤ (A ⊓ centralizer ({τ} : Set Γ)) ⊔ B)
    (hfix : ∀ x ∈ A ⊓ centralizer ({τ} : Set Γ), x ∈ centralizerMod B J)
    (hdec : A = (A ⊓ centralizerMod B J) ⊔ (⁅A, J⁆ ⊔ B))
    (hinter : (A ⊓ centralizerMod B J) ⊓ (⁅A, J⁆ ⊔ B) = B) :
    A ≤ centralizerMod B J := by
  have hQA : ⁅A, J⁆ ⊔ B ≤ A := Core.commutator_sup_le hAB hJA
  have hQB : ⁅A, J⁆ ⊔ B ≤ B := by
    have hτQ := Core.mem_normalizer_commutator_sup (J := J) hτA hτB hJτ
    refine le_of_inf_centralizerMod_le hAB hτ hτB hQA
      (fun x hx => (mem_normalizer_iff.1 hτQ x).1 hx) ?_
    rintro z ⟨hzQ, hzc⟩
    have hzA : z ∈ A := hQA hzQ
    have hz : z ∈ (A ⊓ centralizer ({τ} : Set Γ)) ⊔ B := hlift ⟨hzA, hzc⟩
    have hX : A ⊓ centralizer ({τ} : Set Γ) ≤ normalizer (B : Set Γ) :=
      inf_le_left.trans (Core.le_normalizer hAB)
    rw [← SetLike.mem_coe, sup_comm, coe_mul_of_right_le_normalizer_left B _ hX, Set.mem_mul]
      at hz
    obtain ⟨b, hb, x, hx, rfl⟩ := hz
    have hzJ : b * x ∈ centralizerMod B J :=
      mul_mem (le_centralizerMod hAB hJB hb) (hfix x hx)
    rw [← hinter]
    exact ⟨⟨hzA, hzJ⟩, hzQ⟩
  calc A = (A ⊓ centralizerMod B J) ⊔ (⁅A, J⁆ ⊔ B) := hdec
    _ ≤ A ⊓ centralizerMod B J :=
        sup_le le_rfl (hQB.trans (Core.le_inf_centralizerMod_of_le hAB hJB))
    _ ≤ centralizerMod B J := inf_le_right

end Abstract

section LFacts

theorem scalar_fixed {Y Γ : Type*} [Group Y] [Field Γ] {x : Γ → Y}
    (hx : ∀ a b, x (a + b) = x a * x b) {B : Subgroup Y} {j : Y} {ν : Γ} (hν : ν ≠ 1)
    (hj : ∀ a, j * x a * j⁻¹ = x (ν * a)) (hjB : j ∈ normalizer (B : Set Y))
    (hxB : ∀ a, x a ∈ B → a = 0) {a : Γ} {n : Y} (hn : n ∈ B)
    (h : (x a * n)⁻¹ * (j * (x a * n) * j⁻¹) ∈ B) : a = 0 := by
  have hjn : j * n * j⁻¹ ∈ B := (mem_normalizer_iff.1 hjB n).1 hn
  have e : (x a * n)⁻¹ * (j * (x a * n) * j⁻¹) =
      n⁻¹ * (x ((ν - 1) * a)) * (j * n * j⁻¹) := by
    have h1 : x ((ν - 1) * a) = (x a)⁻¹ * (j * x a * j⁻¹) := by
      rw [hj a, ← map_neg_of_add hx a, ← hx]
      congr 1
      ring
    rw [h1]
    group
  rw [e] at h
  have h2 : x ((ν - 1) * a) ∈ B := by
    have := mul_mem (mul_mem hn h) (inv_mem hjn)
    rwa [show n * (n⁻¹ * x ((ν - 1) * a) * (j * n * j⁻¹)) * (j * n * j⁻¹)⁻¹ = x ((ν - 1) * a) by
      group] at this
  have h3 := hxB _ h2
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hν)

section Torus

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem exists_J₀_scalars :
    ∃ j ∈ d.J₀, ∃ m ν : d.Γ, m ≠ 1 ∧ ν ≠ 1 ∧ (∀ a, j * d.x₁ a * j⁻¹ = d.x₁ (m * a)) ∧
      (∀ a, j * d.x₃ a * j⁻¹ = d.x₃ (m * a)) ∧ (∀ a, j * d.x₄ a * j⁻¹ = d.x₄ (ν * a)) := by
  obtain ⟨j, hj, hj1⟩ : ∃ j ∈ d.J₀, j ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : d.J₀ = ⊥ := eq_bot_iff.2 fun j hj => (mem_bot).2 (hcon j hj)
    have hc := d.yamada_three_five_four.2
    rw [hbot, Subgroup.card_bot] at hc
    have := d.two_le_q
    nlinarith
  have hj' := hj
  rw [d.yamada_three_five_four.1] at hj'
  obtain ⟨⟨hj2, hj5⟩, -⟩ := mem_inf.1 hj'
  obtain ⟨h, rfl, h1⟩ := d.mem_J₂.1 hj2
  have hn := (d.torus_mem_J₅_iff h).1 hj5
  rw [h1, Units.val_one, one_mul] at hn
  have hm : (h.2 : d.Γ) ≠ 1 := fun hm => hj1 (by
    have : h = 1 := Prod.ext h1 (Units.ext hm)
    rw [this, map_one])
  have hN : (h.2 : d.Γ) * (d.σ (h.2 : d.Γ) * d.σ (d.σ (h.2 : d.Γ))) = 1 := by
    have := congrArg (fun z : d.Γ₀ => (z : d.Γ)) hn
    simpa [mul_assoc, coe_fixedNorm] using this
  refine ⟨_, hj, (h.2 : d.Γ), d.σ (h.2 : d.Γ) * d.σ (d.σ (h.2 : d.Γ)), hm, ?_, fun a => ?_,
    fun a => ?_, fun a => ?_⟩
  · intro hν
    rw [hν, mul_one] at hN
    exact hm hN
  · rw [d.torus_x₁]
  · rw [d.torus_x₃, h1]
    simp
  · rw [d.torus_x₄, h1]
    simp

end Torus

section LFix

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem J₀_le_centralizer_U₂ : d.J₀ ≤ centralizer (d.U₂ : Set X) := fun j hj => by
  have hj' := hj
  rw [d.yamada_three_five_four.1] at hj'
  exact (mem_inf.1 (mem_inf.1 (mem_inf.1 hj').1).1).2

theorem fix_W : ∃ j ∈ d.J₀, ∀ w ∈ d.W, w⁻¹ * (j * w * j⁻¹) ∈ d.Y → w ∈ d.Y := by
  obtain ⟨j, hj, m, ν, hm, hν, h1, h3, h4⟩ := exists_J₀_scalars d
  refine ⟨j, hj, fun w hw hc => ?_⟩
  obtain ⟨a, n, hn, rfl⟩ := d.mem_W_iff.1 hw
  have ha : a = 0 := scalar_fixed d.x₄_add hν h4 (d.J_le_normalizer_Y (d.J₀_le_J hj))
    (fun a => d.x₄_mem_Y_iff.1) hn hc
  rw [ha, d.x₄_zero, one_mul]
  exact hn

theorem fix_F : ∃ j ∈ d.J₀, ∀ w ∈ d.F, w⁻¹ * (j * w * j⁻¹) ∈ d.W → w ∈ d.W := by
  obtain ⟨j, hj, m, ν, hm, hν, h1, h3, h4⟩ := exists_J₀_scalars d
  refine ⟨j, hj, fun w hw hc => ?_⟩
  obtain ⟨a, n, hn, rfl⟩ := d.mem_F_iff.1 hw
  have ha : a = 0 := scalar_fixed d.x₃_add hm h3 (d.J_le_normalizer_W (d.J₀_le_J hj))
    (fun a => d.x₃_mem_W_iff.1) hn hc
  rw [ha, d.x₃_zero, one_mul]
  exact hn

theorem fix_M : ∃ j ∈ d.J₀, ∀ w ∈ d.M, w⁻¹ * (j * w * j⁻¹) ∈ d.F → w ∈ d.F := by
  obtain ⟨j, hj, m, ν, hm, hν, h1, h3, h4⟩ := exists_J₀_scalars d
  refine ⟨j, hj, fun w hw hc => ?_⟩
  obtain ⟨a, n, hn, rfl⟩ := d.mem_M_iff.1 hw
  have ha : a = 0 := scalar_fixed d.x₁_add hm h1 (d.J_le_normalizer_F (d.J₀_le_J hj))
    (fun a ha => d.x₁_mem_D_iff.1 (d.F_le_D ha)) hn hc
  rw [ha, d.x₁_zero, one_mul]
  exact hn

theorem fix_S : ∃ j ∈ d.J₀, ∀ w ∈ d.S, w⁻¹ * (j * w * j⁻¹) ∈ d.D → w ∈ d.D := by
  obtain ⟨j, hj, m, ν, hm, hν, h1, h3, h4⟩ := exists_J₀_scalars d
  refine ⟨j, hj, fun w hw hc => ?_⟩
  obtain ⟨a, n, hn, rfl⟩ := d.mem_S_iff.1 hw
  have ha : a = 0 := scalar_fixed d.x₁_add hm h1 (d.J_le_normalizer_D (d.J₀_le_J hj))
    (fun a => d.x₁_mem_D_iff.1) hn hc
  rw [ha, d.x₁_zero, one_mul]
  exact hn

theorem triv_D : ∀ x ∈ d.D, ∀ j ∈ d.J₀, x⁻¹ * (j * x * j⁻¹) ∈ d.F := by
  intro x hx j hj
  obtain ⟨a, n, hn, rfl⟩ := d.mem_D_iff.1 hx
  have hjc : j * d.x₂ a * j⁻¹ = d.x₂ a := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (mem_centralizer_iff.1 (J₀_le_centralizer_U₂ d hj) (d.x₂ a) ⟨a, rfl⟩).symm
  have hjn : j * n * j⁻¹ ∈ d.F := (mem_normalizer_iff.1 (d.J_le_normalizer_F (d.J₀_le_J hj)) n).1 hn
  have e : (d.x₂ a * n)⁻¹ * (j * (d.x₂ a * n) * j⁻¹) =
      n⁻¹ * ((d.x₂ a)⁻¹ * (j * d.x₂ a * j⁻¹)) * (j * n * j⁻¹) := by group
  rw [e, hjc, inv_mul_cancel, mul_one]
  exact mul_mem (inv_mem hn) hjn

theorem triv_S : ∀ x ∈ d.S, ∀ j ∈ d.J₀, x⁻¹ * (j * x * j⁻¹) ∈ d.M := by
  intro x hx j hj
  obtain ⟨a, n, hn, rfl⟩ := d.mem_S_iff_x₂.1 hx
  have hjc : j * d.x₂ a * j⁻¹ = d.x₂ a := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (mem_centralizer_iff.1 (J₀_le_centralizer_U₂ d hj) (d.x₂ a) ⟨a, rfl⟩).symm
  have hjn : j * n * j⁻¹ ∈ d.M := (mem_normalizer_iff.1 (d.J_le_normalizer_M (d.J₀_le_J hj)) n).1 hn
  have e : (d.x₂ a * n)⁻¹ * (j * (d.x₂ a * n) * j⁻¹) =
      n⁻¹ * ((d.x₂ a)⁻¹ * (j * d.x₂ a * j⁻¹)) * (j * n * j⁻¹) := by group
  rw [e, hjc, inv_mul_cancel, mul_one]
  exact mul_mem (inv_mem hn) hjn

end LFix

end LFacts

section Transfer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

theorem fix_transfer {A B : Subgroup G} {XL BL J₀ : Subgroup L} {j : L}
    (hLt : L ≤ centralizer ({t} : Set G)) (hAB : IsElemSection A B)
    (hA : A ⊓ centralizer ({t} : Set G) = XL.map L.subtype)
    (hB : B ⊓ centralizer ({t} : Set G) = BL.map L.subtype)
    (hJB : J₀.map L.subtype ≤ normalizer (B : Set G)) (hj : j ∈ J₀)
    (hfixL : ∀ y ∈ XL, y⁻¹ * (j * y * j⁻¹) ∈ BL → y ∈ BL) :
    ∀ x ∈ A ⊓ centralizer ({t} : Set G), x ∈ centralizerMod B (J₀.map L.subtype) → x ∈ B := by
  intro x hx hxc
  have hxA : x ∈ A := (mem_inf.1 hx).1
  rw [hA] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have h1 := (Core.mem_centralizerMod_iff_of_le hAB hJB hxA).1 hxc (L.subtype j) ⟨j, hj, rfl⟩
  have e : L.subtype (y⁻¹ * (j * y * j⁻¹)) =
      (L.subtype y)⁻¹ * (L.subtype j * L.subtype y * (L.subtype j)⁻¹) := by
    simp only [map_mul, map_inv]
  have h2 : L.subtype (y⁻¹ * (j * y * j⁻¹)) ∈ B ⊓ centralizer ({t} : Set G) :=
    ⟨e ▸ h1, hLt (y⁻¹ * (j * y * j⁻¹)).2⟩
  rw [hB] at h2
  obtain ⟨z, hz, hzeq⟩ := h2
  have hz' : z = y⁻¹ * (j * y * j⁻¹) := L.subtype_injective hzeq
  have hyB : L.subtype y ∈ BL.map L.subtype := ⟨y, hfixL y hy (hz' ▸ hz), rfl⟩
  rw [← hB] at hyB
  exact hyB.1

theorem triv_transfer {A B : Subgroup G} {XL BL J₀ : Subgroup L}
    (hAB : IsElemSection A B)
    (hA : A ⊓ centralizer ({t} : Set G) = XL.map L.subtype)
    (hB : B ⊓ centralizer ({t} : Set G) = BL.map L.subtype)
    (hJB : J₀.map L.subtype ≤ normalizer (B : Set G))
    (hfixL : ∀ y ∈ XL, ∀ j ∈ J₀, y⁻¹ * (j * y * j⁻¹) ∈ BL) :
    ∀ x ∈ A ⊓ centralizer ({t} : Set G), x ∈ centralizerMod B (J₀.map L.subtype) := by
  intro x hx
  have hxA : x ∈ A := (mem_inf.1 hx).1
  rw [hA] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [Core.mem_centralizerMod_iff_of_le hAB hJB hxA]
  rintro _ ⟨j, hj, rfl⟩
  have e : L.subtype (y⁻¹ * (j * y * j⁻¹)) =
      (L.subtype y)⁻¹ * (L.subtype j * L.subtype y * (L.subtype j)⁻¹) := by
    simp only [map_mul, map_inv]
  rw [← e]
  have hBL : BL.map L.subtype ≤ B := by
    rw [← hB]
    exact inf_le_left
  exact hBL ⟨_, hfixL y hy j hj, rfl⟩

end Transfer

section Inputs

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem le_normalizer_of_le_centralizer {K J : Subgroup G}
    (h : K ≤ centralizer (J : Set G)) : J ≤ normalizer (K : Set G) := fun j hj =>
  mem_normalizer_fintype fun y hy => by
    rw [show j * y * j⁻¹ = y by rw [mem_centralizer_iff.1 (h hy) j hj]; group]
    exact hy

theorem odd_card_jZeroG (d : TrialityD4Data L (2 ^ f)) : Odd (Nat.card (jZeroG d)) := by
  have h1 : Nat.card (jZeroG d) = Nat.card d.J₀ :=
    Subgroup.card_map_of_injective L.subtype_injective
  rw [h1, d.yamada_three_five_four.2]
  have he := d.even_q
  exact ((he.pow_of_ne_zero (by norm_num)).add he).add_one

theorem Y₂_le_centralizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaY₂ d t ≤ centralizer ((jZeroG d : Subgroup G) : Set G) :=
  Setup.yamadaY₂_le_centralizer_J₀ d (h.yamadaY₂_eq d hlay)

theorem jZeroG_le_normalizer_Y₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : jZeroG d ≤ normalizer (yamadaY₂ d t : Set G) :=
  le_normalizer_of_le_centralizer (Y₂_le_centralizer h d hlay)

theorem jZeroG_le_normalizer_R₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : jZeroG d ≤ normalizer (yamadaR₄ d t : Set G) :=
  h.J₀_map_le_normalizer_yamadaR₄ d (h.yamada_5_6_1 d hlay) (h.yamada_5_6_2 d hlay)
    (h.yamadaY₂_eq d hlay)

theorem jZeroG_le_normalizer_W₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : jZeroG d ≤ normalizer (yamadaW₃ d t : Set G) := fun _ hx =>
  (mem_inf.1 (mem_inf.1 (h.normalizer_yamadaR₄_le_of_layerHyp d hlay
    (jZeroG_le_normalizer_R₄ h d hlay hx))).1).2

theorem jZeroG_le_normalizer_F₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : jZeroG d ≤ normalizer (yamadaF₄ d t : Set G) := fun _ hx =>
  (mem_inf.1 (h.normalizer_yamadaR₄_le_normalizer_yamadaF₄ d hlay
    (jZeroG_le_normalizer_R₄ h d hlay hx))).2

theorem jZeroG_le_normalizer_D₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : jZeroG d ≤ normalizer (yamadaD₅ d t : Set G) := by
  rintro _ ⟨l, hl, rfl⟩
  exact (h.coe_mem_normalizer_yamadaD₅_C9 d (h.yamada_5_6_1 d hlay)
    (d.J_le_normalizer_V (d.J₀_le_J hl))).2.2

theorem jZeroG_le_normalizer_M₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : jZeroG d ≤ normalizer (yamadaM₆ d t : Set G) := fun x hx => by
  have hL₃ : x ∈ normalizer (yamadaL₃ d t : Set G) :=
    Setup.normalizer_yamadaL₂_le_normalizer_yamadaL₃ d (h.J₀_map_le_normalizer_yamadaL₂ d hx)
  have hCY₂ : x ∈ normalizer (centralizer (yamadaY₂ d t : Set G) : Set G) :=
    Setup.mem_normalizer_centralizer_C8 (jZeroG_le_normalizer_Y₂ h d hlay hx)
  have hM₃ : x ∈ normalizer (yamadaM₃ d t : Set G) := Common.mem_normalizer_inf hL₃ hCY₂
  exact Common.mem_normalizer_inf (le_normalizer_yamadaL₆ d t ⟨hL₃, hM₃⟩) hCY₂

theorem jZeroG_le_normalizer_P (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : jZeroG d ≤ normalizer (yamadaP d t : Set G) := fun _ hx =>
  Common.mem_normalizer_sup (jZeroG_le_normalizer_D₅ h d hlay hx)
    (jZeroG_le_normalizer_M₆ h d hlay hx)

end Inputs

section Order

variable {Γ : Type*} [Group Γ] [Finite Γ] {A B J : Subgroup Γ}

theorem eq_sup_of_coprime (hAB : IsElemSection A B) (hJA : J ≤ normalizer (A : Set Γ))
    (hJB : J ≤ normalizer (B : Set Γ)) (hsolv : Group.IsSolvable A)
    (hcop : (Nat.card J).Coprime (Nat.card A)) (hfix : A ≤ centralizerMod B J) :
    A = (A ⊓ centralizer (J : Set Γ)) ⊔ B := by
  refine le_antisymm (fun m hm => ?_) (sup_le inf_le_left hAB.le)
  obtain ⟨c, hc, n, hn, rfl⟩ := exists_mem_inf_centralizer_mul_of_coprime hAB.le
    (Core.le_normalizer hAB) hJA hJB hsolv hcop hm
    ((Core.mem_centralizerMod_iff_of_le hAB hJB hm).1 (hfix hm))
  exact mul_mem_sup hc hn

theorem card_inf_centralizer (hAB : IsElemSection A B)
    (hsup : A = (A ⊓ centralizer (J : Set Γ)) ⊔ B) :
    Nat.card (A ⊓ centralizer (J : Set Γ) : Subgroup Γ) =
      B.relIndex A * Nat.card (B ⊓ centralizer (J : Set Γ) : Subgroup Γ) := by
  have hX : A ⊓ centralizer (J : Set Γ) ≤ A := inf_le_left
  have h1 := Core.relIndex_sup_eq hX hAB.le (Core.normal_subgroupOf hAB)
  rw [← hsup] at h1
  have hBX : B ⊓ (A ⊓ centralizer (J : Set Γ)) = B ⊓ centralizer (J : Set Γ) := by
    ext x
    simp only [mem_inf]
    exact ⟨fun ⟨hb, _, hc⟩ => ⟨hb, hc⟩, fun ⟨hb, hc⟩ => ⟨hb, hAB.le hb, hc⟩⟩
  have h2 := relIndex_mul_card (B ⊓ (A ⊓ centralizer (J : Set Γ))) (A ⊓ centralizer (J : Set Γ))
  rw [inf_eq_left.2 (inf_le_right : B ⊓ (A ⊓ centralizer (J : Set Γ)) ≤
    A ⊓ centralizer (J : Set Γ)), hBX] at h2
  rw [hBX] at h1
  rw [h1, ← h2]

end Order

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem main (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    yamadaY₂ d t ≤ centralizer ((jZeroG d : Subgroup G) : Set G) ∧
      yamadaW₃ d t ⊓ centralizerMod (yamadaY₂ d t) (jZeroG d) = yamadaY₂ d t ∧
      yamadaF₄ d t ⊓ centralizerMod (yamadaW₃ d t) (jZeroG d) = yamadaW₃ d t ∧
      yamadaM₆ d t ⊓ centralizerMod (yamadaF₄ d t) (jZeroG d) = yamadaF₄ d t ∧
      yamadaP d t ⊓ centralizerMod (yamadaD₅ d t) (jZeroG d) = yamadaD₅ d t ∧
      yamadaD₅ d t ≤ centralizerMod (yamadaF₄ d t) (jZeroG d) ∧
      yamadaP d t ≤ centralizerMod (yamadaM₆ d t) (jZeroG d) ∧
      yamadaW₃ d t ⊓ centralizer ((jZeroG d : Subgroup G) : Set G) = yamadaY₂ d t ∧
      yamadaF₄ d t ⊓ centralizer ((jZeroG d : Subgroup G) : Set G) = yamadaY₂ d t ∧
      yamadaM₆ d t ⊓ centralizer ((jZeroG d : Subgroup G) : Set G) = yamadaY₂ d t ∧
      yamadaP d t ⊓ centralizer ((jZeroG d : Subgroup G) : Set G) = prodX d t ∧
      Nat.card (prodX d t) = (2 ^ f) ^ 6 := by
  have hlay := hp.layer
  have ht := h.t_mul_t
  obtain ⟨-, hY₂C, hW₃C, hF₄C, hD₅C, hM₆C, hPC, hcD₅, -, -, -, -, f3, f4, f5, f6, f7, f8⟩ :=
    T4_series_free h d hp
  have hLt : L ≤ centralizer ({t} : Set G) := h.L_le_centralizer
  have hJt : jZeroG d ≤ centralizer ({t} : Set G) := h.J₀_map_le_centralizer d
  have hJodd := odd_card_jZeroG d
  have hY₂J := Y₂_le_centralizer h d hlay
  have nY₂ := jZeroG_le_normalizer_Y₂ h d hlay
  have nW₃ := jZeroG_le_normalizer_W₃ h d hlay
  have nF₄ := jZeroG_le_normalizer_F₄ h d hlay
  have nD₅ := jZeroG_le_normalizer_D₅ h d hlay
  have nM₆ := jZeroG_le_normalizer_M₆ h d hlay
  have nP := jZeroG_le_normalizer_P h d hlay
  have tY₂ := h.t_mem_normalizer_yamadaY₂ d
  have tW₃ := ProductToolboxAux.P04.t_mem_normalizer_W₃ h d hlay
  have tF₄ := h.t_mem_normalizer_yamadaF₄ d hlay
  have tD₅ := h.t_mem_normalizer_yamadaD₅_C9 d
  have tM₆ := ProductToolboxAux.P04.t_mem_normalizer_M₆ h d hlay
  have tP := h.t_mem_normalizer_yamadaP d hlay
  obtain ⟨jW, hjW, hfixW⟩ := fix_W d
  obtain ⟨jF, hjF, hfixF⟩ := fix_F d
  obtain ⟨jM, hjM, hfixM⟩ := fix_M d
  obtain ⟨jS, hjS, hfixS⟩ := fix_S d
  have c2 : yamadaW₃ d t ⊓ centralizerMod (yamadaY₂ d t) (jZeroG d) = yamadaY₂ d t :=
    inf_centralizerMod_eq_of_fixed f3.1 ht tW₃ tY₂ hJt nY₂ f3.2.2.le
      (fix_transfer (J₀ := d.J₀) hLt f3.1 hW₃C hY₂C nY₂ hjW hfixW)
  have c3 : yamadaF₄ d t ⊓ centralizerMod (yamadaW₃ d t) (jZeroG d) = yamadaW₃ d t :=
    inf_centralizerMod_eq_of_fixed f4.1 ht tF₄ tW₃ hJt nW₃ f4.2.2.le
      (fix_transfer (J₀ := d.J₀) hLt f4.1 hF₄C hW₃C nW₃ hjF hfixF)
  have c4 : yamadaM₆ d t ⊓ centralizerMod (yamadaF₄ d t) (jZeroG d) = yamadaF₄ d t :=
    inf_centralizerMod_eq_of_fixed f7.1 ht tM₆ tF₄ hJt nF₄ f7.2.2.le
      (fix_transfer (J₀ := d.J₀) hLt f7.1 hM₆C hF₄C nF₄ hjM hfixM)
  have c5 : yamadaP d t ⊓ centralizerMod (yamadaD₅ d t) (jZeroG d) = yamadaD₅ d t :=
    inf_centralizerMod_eq_of_fixed f6.1 ht tP tD₅ hJt nD₅ f6.2.2.le
      (fix_transfer (J₀ := d.J₀) hLt f6.1 hPC hD₅C nD₅ hjS hfixS)
  obtain ⟨hsup6, hint6, -⟩ := T3_fixed f5.1 ht tD₅ tF₄ f5.2.1 hJodd hJt nD₅ nF₄
  obtain ⟨hsup7, hint7, -⟩ := T3_fixed f8.1 ht tP tM₆ f8.2.1 hJodd hJt nP nM₆
  have c6 : yamadaD₅ d t ≤ centralizerMod (yamadaF₄ d t) (jZeroG d) :=
    le_centralizerMod_of_fixed f5.1 ht tD₅ tF₄ hJt nD₅ nF₄ f5.2.2.le
      (triv_transfer (J₀ := d.J₀) f5.1 hD₅C hF₄C nF₄ (triv_D d)) hsup6 hint6
  have c7 : yamadaP d t ≤ centralizerMod (yamadaM₆ d t) (jZeroG d) :=
    le_centralizerMod_of_fixed f8.1 ht tP tM₆ hJt nP nM₆ f8.2.2.le
      (triv_transfer (J₀ := d.J₀) f8.1 hPC hM₆C nM₆ (triv_S d)) hsup7 hint7
  have c8 : yamadaW₃ d t ⊓ centralizer ((jZeroG d : Subgroup G) : Set G) = yamadaY₂ d t :=
    le_antisymm (fun x hx => c2.le ⟨hx.1, mem_centralizerMod_of_commute f3.1 nY₂ hx.1 hx.2⟩)
      (le_inf f3.1.le hY₂J)
  have c9 : yamadaF₄ d t ⊓ centralizer ((jZeroG d : Subgroup G) : Set G) = yamadaY₂ d t :=
    le_antisymm (fun x hx => c8.le ⟨c3.le ⟨hx.1, mem_centralizerMod_of_commute f4.1 nW₃ hx.1 hx.2⟩,
      hx.2⟩) (le_inf (f3.1.le.trans f4.1.le) hY₂J)
  have c10 : yamadaM₆ d t ⊓ centralizer ((jZeroG d : Subgroup G) : Set G) = yamadaY₂ d t :=
    le_antisymm (fun x hx => c9.le ⟨c4.le ⟨hx.1, mem_centralizerMod_of_commute f7.1 nF₄ hx.1 hx.2⟩,
      hx.2⟩) (le_inf (f3.1.le.trans (f4.1.le.trans f7.1.le)) hY₂J)
  have hX : prodX d t = yamadaD₅ d t ⊓ centralizer ((jZeroG d : Subgroup G) : Set G) := rfl
  have c11 : yamadaP d t ⊓ centralizer ((jZeroG d : Subgroup G) : Set G) = prodX d t := by
    rw [hX]
    exact le_antisymm (fun x hx => ⟨c5.le ⟨hx.1, mem_centralizerMod_of_commute f6.1 nD₅ hx.1 hx.2⟩,
      hx.2⟩) (fun x hx => ⟨f6.1.le hx.1, hx.2⟩)
  have hcop : (Nat.card (jZeroG d)).Coprime (Nat.card (yamadaD₅ d t)) := by
    rw [hcD₅]
    exact (Nat.Coprime.pow_right f (Nat.coprime_two_right.2 hJodd)).pow_right 18
  have hsolv : Group.IsSolvable (yamadaD₅ d t) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp2 : IsPGroup 2 (yamadaD₅ d t) :=
      IsPGroup.of_card (n := f * 18) (by rw [hcD₅, ← pow_mul])
    haveI := hp2.isNilpotent
    infer_instance
  have hsupD := eq_sup_of_coprime f5.1 nD₅ nF₄ hsolv hcop c6
  have hcard := card_inf_centralizer f5.1 hsupD
  have hidx : (yamadaF₄ d t).relIndex (yamadaD₅ d t) = (2 ^ f) ^ 2 := by
    have h1 := relIndex_mul_card (yamadaF₄ d t) (yamadaD₅ d t)
    rw [inf_of_le_left f5.1.le, h.card_yamadaF₄ d hlay, hcD₅] at h1
    have hpos : 0 < (2 ^ f) ^ 16 := by positivity
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, ← pow_add]
  rw [c9, hidx, (h.yamada_5_9_2 d hlay).2.1] at hcard
  refine ⟨hY₂J, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, ?_⟩
  rw [hX, hcard, ← pow_add]

end Main

end ProductToolboxAux.P05

end P05

theorem T5_J₀ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    yamadaY₂ d t ≤ centralizer ((jZeroG d : Subgroup G) : Set G) ∧
      yamadaW₃ d t ⊓ centralizerMod (yamadaY₂ d t) (jZeroG d) = yamadaY₂ d t ∧
      yamadaF₄ d t ⊓ centralizerMod (yamadaW₃ d t) (jZeroG d) = yamadaW₃ d t ∧
      yamadaM₆ d t ⊓ centralizerMod (yamadaF₄ d t) (jZeroG d) = yamadaF₄ d t ∧
      yamadaP d t ⊓ centralizerMod (yamadaD₅ d t) (jZeroG d) = yamadaD₅ d t ∧
      yamadaD₅ d t ≤ centralizerMod (yamadaF₄ d t) (jZeroG d) ∧
      yamadaP d t ≤ centralizerMod (yamadaM₆ d t) (jZeroG d) ∧
      yamadaW₃ d t ⊓ centralizer ((jZeroG d : Subgroup G) : Set G) = yamadaY₂ d t ∧
      yamadaF₄ d t ⊓ centralizer ((jZeroG d : Subgroup G) : Set G) = yamadaY₂ d t ∧
      yamadaM₆ d t ⊓ centralizer ((jZeroG d : Subgroup G) : Set G) = yamadaY₂ d t ∧
      yamadaP d t ⊓ centralizer ((jZeroG d : Subgroup G) : Set G) = prodX d t ∧
      Nat.card (prodX d t) = (2 ^ f) ^ 6 :=
  ProductToolboxAux.P05.main h d hp

end Series

end CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
