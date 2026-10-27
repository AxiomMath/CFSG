module

public import Mathlib.Order.CompletePartialOrder
public import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
public import CFSG.FeitThompson.OddOrder.FrobeniusKernelContainsRoots
public import CFSG.FeitThompson.OddOrder.FrobeniusKernelContainsCentralizers
public import CFSG.FeitThompson.OddOrder.CommutingSubgroupsJoinProduct
public import CFSG.FeitThompson.Representations.CoprimeAutomorphismCosetPartition

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CoprimeComponent

variable {G : Type*} [Group G] {p : ℕ} {S P U B A J : Subgroup G}

structure IsSylowCorePrimeSetup (p : ℕ) (S P U B A J : Subgroup G) : Prop where
  prime : p.Prime
  card_P : Nat.card P = p ^ (Nat.card G).factorization p
  ne_bot_P : P ≠ ⊥
  ne_bot_U : U ≠ ⊥
  ne_bot_B : B ≠ ⊥
  normal_P : (P.subgroupOf J).Normal
  coe_mul_coe_eq_J : (P : Set G) * (U : Set G) = (J : Set G)
  inf_P_U : P ⊓ U = ⊥
  normal_J : (J.subgroupOf S).Normal
  coe_mul_coe_eq_S : (J : Set G) * (B : Set G) = (S : Set G)
  inf_J_B : J ⊓ B = ⊥
  coprime_card : (Nat.card J).Coprime (Nat.card B)
  inf_centralizer_U : ∀ u ∈ U, u ≠ 1 → P ⊓ centralizer ({u} : Set G) = ⊥
  le_A_P : A ≤ P
  inf_centralizer_B : ∀ b ∈ B, b ≠ 1 → J ⊓ centralizer ({b} : Set G) = A
  normalizer_P : normalizer (P : Set G) = S
  ti_punctured : ∀ g : G, g ∉ S →
    Disjoint ((P : Set G) \ {1}) ((fun x => g⁻¹ * x * g) '' ((P : Set G) \ {1}))

namespace IsSylowCorePrimeSetup

variable (h : IsSylowCorePrimeSetup p S P U B A J)

include h

theorem le_P_J : P ≤ J := left_le_of_coe_mul_coe_eq h.coe_mul_coe_eq_J

theorem le_U_J : U ≤ J := right_le_of_coe_mul_coe_eq h.coe_mul_coe_eq_J

theorem le_J_S : J ≤ S := left_le_of_coe_mul_coe_eq h.coe_mul_coe_eq_S

theorem le_B_S : B ≤ S := right_le_of_coe_mul_coe_eq h.coe_mul_coe_eq_S

theorem le_A_centralizer : A ≤ centralizer (B : Set G) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro b hb
  by_cases hb1 : b = 1
  · simp [hb1]
  · have hxb : x ∈ J ⊓ centralizer ({b} : Set G) := by
      rw [h.inf_centralizer_B b hb hb1]; exact hx
    exact (mem_centralizer_singleton_iff.1 hxb.2).symm

theorem coe_sup_eq_mul : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
  coe_sup_eq_mul_of_commute fun _ hx y hy =>
    (mem_centralizer_iff.1 (h.le_A_centralizer hx) y hy).symm

theorem centralizer_singleton_le_S {a : G} (ha : a ∈ P) (ha1 : a ≠ 1) :
    centralizer ({a} : Set G) ≤ S := by
  intro c hc
  by_contra hcS
  have hca : c⁻¹ * a * c = a := by
    have hcomm := mem_centralizer_singleton_iff.1 hc
    calc c⁻¹ * a * c = c⁻¹ * (a * c) := by group
      _ = c⁻¹ * (c * a) := by rw [hcomm]
      _ = a := by group
  exact Set.disjoint_left.1 (h.ti_punctured c hcS) ⟨ha, ha1⟩ ⟨a, ⟨ha, ha1⟩, hca⟩

theorem inf_centralizer_singleton_le_P [Finite G] {a : G} (ha : a ∈ P) (ha1 : a ≠ 1) :
    J ⊓ centralizer ({a} : Set G) ≤ P := by
  have := h.normal_P
  have ha' : (⟨a, h.le_P_J ha⟩ : J) ∈ P.subgroupOf J := ha
  have ha1' : (⟨a, h.le_P_J ha⟩ : J) ≠ 1 := fun hh => ha1 (by simpa using Subtype.ext_iff.1 hh)
  have key := centralizer_singleton_le_of_mem_of_ne_one
    (isComplement'_subgroupOf_of_coe_mul_coe_eq h.coe_mul_coe_eq_J h.inf_P_U)
    (fun e he he1 => inf_centralizer_singleton_subgroupOf_eq_bot h.inf_centralizer_U he he1)
    ha' ha1'
  intro x hx
  have hmem : (⟨x, hx.1⟩ : J) ∈ centralizer ({(⟨a, h.le_P_J ha⟩ : J)} : Set J) :=
    mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.1 hx.2))
  exact key hmem

end IsSylowCorePrimeSetup

theorem exists_isPGroup_zpowers_commute {g : G} (hp : p.Prime) (hg : IsOfFinOrder g)
    (hdvd : p ∣ orderOf g) :
    ∃ a : G, IsPGroup p (zpowers a) ∧ p ∣ orderOf a ∧ Commute g a := by
  refine ⟨piComponent ({p} : Set ℕ) g, ?_, ?_, commute_self_piComponent _ _⟩
  ·
    have hpi := isPiNumber_orderOf_piComponent hg ({p} : Set ℕ)
    obtain ⟨k, hk⟩ : ∃ k, orderOf (piComponent ({p} : Set ℕ) g) = p ^ k :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hpi.ne_zero
        fun {d} hd hdd => hpi.mem_of_prime_dvd hd hdd⟩
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  ·
    have hN : orderOf g ≠ 0 := hg.orderOf_pos.ne'
    have hsplit := piPart_mul_piPart_compl (pi := ({p} : Set ℕ)) hN
    have hnp : ¬ p ∣ piPart ({p} : Set ℕ)ᶜ (orderOf g) := fun hd =>
      (isPiPrimeNumber_iff_forall_prime.1
        (isPiPrimeNumber_piPart_compl ({p} : Set ℕ) (orderOf g))).2 p hp hd rfl
    have hmul : p ∣ piPart ({p} : Set ℕ) (orderOf g) * piPart ({p} : Set ℕ)ᶜ (orderOf g) := by
      rw [hsplit]; exact hdvd
    rw [orderOf_piComponent hg]
    exact ((Nat.Prime.dvd_mul hp).1 hmul).resolve_right hnp

theorem IsSylowCorePrimeSetup.mem_conjugatesOfSet_punctured_union [Finite G]
    (h : IsSylowCorePrimeSetup p S P U B A J) {g : G} (hgp : p ∣ orderOf g) :
    g ∈ Group.conjugatesOfSet ((P : Set G) \ {1}) ∪
      Group.conjugatesOfSet (((A ⊔ B : Subgroup G) : Set G) \ {1}) := by
  have hp := h.prime
  have _ : Fact p.Prime := ⟨hp⟩
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hgp
    exact hp.one_lt.ne' (Nat.dvd_one.1 hgp)
  obtain ⟨a, hapg, hpa, hcomm⟩ :=
    exists_isPGroup_zpowers_commute hp (isOfFinOrder_of_finite g) hgp
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hpa
    exact hp.one_lt.ne' (Nat.dvd_one.1 hpa)
  obtain ⟨y, hy⟩ := exists_forall_inv_mul_mul_mem h.card_P hapg
  set a' : G := y⁻¹ * a * y with ha'def
  have ha'P : a' ∈ P := hy a (mem_zpowers a)
  have ha'1 : a' ≠ 1 := by
    rw [ha'def]
    intro hh
    exact ha1 (by simpa [mul_assoc] using congrArg (fun x => y * x * y⁻¹) hh)
  set g' : G := y⁻¹ * g * y with hg'def
  have hg'1 : g' ≠ 1 := by
    rw [hg'def]
    intro hh
    exact hg1 (by simpa [mul_assoc] using congrArg (fun x => y * x * y⁻¹) hh)
  have hconj : y * g' * y⁻¹ = g := by rw [hg'def]; group
  have hg'c : g' ∈ centralizer ({a'} : Set G) := by
    refine mem_centralizer_singleton_iff.mpr ?_
    rw [hg'def, ha'def]
    calc y⁻¹ * g * y * (y⁻¹ * a * y) = y⁻¹ * (g * a) * y := by group
      _ = y⁻¹ * (a * g) * y := by rw [hcomm.eq]
      _ = y⁻¹ * a * y * (y⁻¹ * g * y) := by group
  have hg'S : g' ∈ S := h.centralizer_singleton_le_S ha'P ha'1 hg'c
  have hg'mul : g' ∈ (J : Set G) * (B : Set G) := by rw [h.coe_mul_coe_eq_S]; exact hg'S
  obtain ⟨j, hj, b, hb, hjb⟩ := Set.mem_mul.1 hg'mul
  by_cases hb1 : b = 1
  ·
    refine Or.inl ?_
    have hg'J : g' ∈ J := by rw [← hjb, hb1, mul_one]; exact hj
    have hg'P : g' ∈ P := h.inf_centralizer_singleton_le_P ha'P ha'1 ⟨hg'J, hg'c⟩
    exact Group.mem_conjugatesOfSet_iff.2 ⟨g', ⟨hg'P, hg'1⟩, isConj_iff.2 ⟨y, hconj⟩⟩
  ·
    refine Or.inr ?_
    have hbord : orderOf b ∣ Nat.card B := B.orderOf_dvd_natCard hb
    have hcopb : (Nat.card J).Coprime (orderOf b) := h.coprime_card.coprime_dvd_right hbord
    have _ := h.normal_J
    have hbnorm : b ∈ normalizer (J : Set G) :=
      Subgroup.le_normalizer_of_normal_subgroupOf h.le_J_S (h.le_B_S hb)
    have hmem : g' ∈ (J : Set G) * ({b} : Set G) := ⟨j, hj, b, rfl, hjb⟩
    rw [← sUnion_centralizerCosetConjugates hcopb (isOfFinOrder_of_finite b) hbnorm,
      Set.mem_sUnion] at hmem
    obtain ⟨T, hT, hg'T⟩ := hmem
    obtain ⟨k, hk, rfl⟩ := mem_centralizerCosetConjugates_iff.1 hT
    rw [mem_conjAct_smul_set_iff, mem_centralizerCoset_iff, h.inf_centralizer_B b hb hb1] at hg'T
    set α : G := k⁻¹ * g' * k * b⁻¹ with hαdef
    have hαb : α * b = k⁻¹ * g' * k := by rw [hαdef]; group
    have hW : α * b ∈ (A ⊔ B : Subgroup G) :=
      (A ⊔ B).mul_mem ((le_sup_left : A ≤ A ⊔ B) hg'T) ((le_sup_right : B ≤ A ⊔ B) hb)
    have hne : α * b ≠ 1 := by
      rw [hαb]
      intro hh
      exact hg'1 (by simpa [mul_assoc] using congrArg (fun x => k * x * k⁻¹) hh)
    refine Group.mem_conjugatesOfSet_iff.2 ⟨α * b, ⟨hW, hne⟩, isConj_iff.2 ⟨y * k, ?_⟩⟩
    rw [hαb]
    calc y * k * (k⁻¹ * g' * k) * (y * k)⁻¹ = y * g' * y⁻¹ := by group
      _ = g := hconj

theorem IsSylowCorePrimeSetup.exists_conj_mem_sylow_or_sup [Finite G]
    (h : IsSylowCorePrimeSetup p S P U B A J) {g : G} (hgp : p ∣ orderOf g) :
    ∃ y : G, y⁻¹ * g * y ∈ P ∨ y⁻¹ * g * y ∈ A ⊔ B := by
  have key : ∀ (T : Subgroup G), g ∈ Group.conjugatesOfSet ((T : Set G) \ {1}) →
      ∃ y : G, y⁻¹ * g * y ∈ T := by
    intro T hmem
    obtain ⟨x, hx, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hmem
    obtain ⟨y, hxy⟩ := isConj_iff.1 hconj
    refine ⟨y, ?_⟩
    have hgx : y⁻¹ * g * y = x := by rw [← hxy]; group
    rw [hgx]
    exact hx.1
  rcases h.mem_conjugatesOfSet_punctured_union hgp with hmem | hmem
  · obtain ⟨y, hy⟩ := key P hmem
    exact ⟨y, Or.inl hy⟩
  · obtain ⟨y, hy⟩ := key (A ⊔ B) hmem
    exact ⟨y, Or.inr hy⟩

end

end CFSG.FeitThompson
