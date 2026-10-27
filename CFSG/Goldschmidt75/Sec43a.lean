module

public import CFSG.Goldschmidt75.Sec42

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_inf_centralizer_sup {A N O : Subgroup G} (hA : IsPGroup 2 A) (hON : O ≤ N)
    (hOn : N ⊔ A ≤ normalizer (O : Set G)) (hO : Odd (Nat.card O)) (hcomm : ⁅N, A⁆ ≤ O) :
    N ≤ (N ⊓ centralizer (A : Set G)) ⊔ O := by
  set H := N ⊔ A with hH
  have hMn : (O.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer (hON.trans le_sup_left)).mpr hOn
  have hcop : Nat.Coprime 2 (Nat.card (O.subgroupOf H)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (hON.trans le_sup_left)).toEquiv]
    exact Nat.coprime_two_left.mpr hO
  have : Fact (IsPGroup 2 (A.subgroupOf H)) := ⟨hA.comap_subtype⟩
  have hC := CFSG.centralizer_map_quotient_eq_map_centralizer 2 (A.subgroupOf H)
    (O.subgroupOf H) hMn hcop
  intro n hn
  set q := QuotientGroup.mk' (O.subgroupOf H)
  have hnH : n ∈ H := (le_sup_left : N ≤ H) hn
  have hmem : q ⟨n, hnH⟩ ∈ centralizer (((A.subgroupOf H).map q : Subgroup _) : Set _) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, mem_subgroupOf]
    have e : (((a * ⟨n, hnH⟩)⁻¹ * (⟨n, hnH⟩ * a) : H) : G) = ⁅n⁻¹, (a : G)⁻¹⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact hcomm (commutator_mem_commutator (inv_mem hn) (inv_mem (mem_subgroupOf.mp ha)))
  rw [hC] at hmem
  obtain ⟨c, hc, hcn⟩ := hmem
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf] at hcn
  have hcA : (c : G) ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    have := mem_centralizer_iff.mp hc ⟨a, (le_sup_right : A ≤ H) ha⟩ (mem_subgroupOf.mpr ha)
    exact congrArg Subtype.val this
  have hcN : (c : G) ∈ N := by
    have h1 : (c : G) = n * ((c : G)⁻¹ * n)⁻¹ := by group
    rw [h1]
    exact mul_mem hn (inv_mem (hON (by simpa using hcn)))
  have h2 : n = (c : G) * ((c : G)⁻¹ * n) := by group
  rw [h2]
  exact mul_mem_sup ⟨hcN, hcA⟩ (by simpa using hcn)

theorem oddCoreOf_le_of_le_normalizer {N L : Subgroup G} (hNL : N ≤ L)
    (hL : L ≤ normalizer (N : Set G)) : oddCoreOf N ≤ oddCoreOf L := by
  refine Completion.le_oddCoreOf ((map_subtype_le _).trans hNL) (fun l hl => ?_)
    (Balance.odd_card_oddCoreOf _)
  apply mem_normalizer_of_conjSub_eq
  rw [conjSub_oddCoreOf, conjSub_eq_of_mem_normalizer (hL hl)]

omit [Finite G] in
theorem mem_normalizer_of_forall {g : G} {P : Subgroup G} (h : ∀ x ∈ P, g * x * g⁻¹ ∈ P)
    (h' : ∀ x ∈ P, g⁻¹ * x * g ∈ P) : g ∈ normalizer (P : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have := h' _ hx
  simpa [mul_assoc] using this

omit [Finite G] in
theorem odd_card_sup {A O : Subgroup G} (hAO : A ≤ normalizer (O : Set G))
    (hA : Odd (Nat.card A)) (hO : Odd (Nat.card O)) : Odd (Nat.card (A ⊔ O : Subgroup G)) := by
  set P := A ⊔ O with hP
  have hOP : O ≤ P := le_sup_right
  have hn : (O.subgroupOf P).Normal :=
    (normal_subgroupOf_iff_le_normalizer hOP).mpr (sup_le hAO le_normalizer)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (O.subgroupOf P)
  have hsurj : Function.Surjective ((QuotientGroup.mk' (O.subgroupOf P)).comp
      (Subgroup.inclusion (le_sup_left : A ≤ P))) := by
    intro q
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hp : (p : G) ∈ ((A ⊔ O : Subgroup G) : Set G) := p.2
    rw [coe_mul_of_left_le_normalizer_right _ _ hAO] at hp
    obtain ⟨a, ha, o, ho, hao⟩ := hp
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      mem_subgroupOf]
    have e : (((Subgroup.inclusion (le_sup_left : A ≤ P) ⟨a, ha⟩)⁻¹ * p : P) : G) = o := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hao]
      group
    rw [e]
    exact ho
  have h2 := Subgroup.card_dvd_of_surjective hsurj
  rw [h1]
  refine Nat.odd_mul.mpr ⟨Odd.of_dvd_nat hA h2, ?_⟩
  rwa [Nat.card_congr (subgroupOfEquivOfLe hOP).toEquiv]

theorem le_oddCoreOf_of_le_sup {A Y N : Subgroup G} (hYN : Y ≤ N) (hN : N ≤ Y ⊔ oddCoreOf N)
    (hAY : A ≤ Y) (hYA : Y ≤ normalizer (A : Set G)) (hA : Odd (Nat.card A)) :
    A ≤ oddCoreOf N := by
  set O := oddCoreOf N with hO
  have hON : O ≤ N := map_subtype_le _
  have hNO : N ≤ normalizer (O : Set G) := Completion.le_normalizer_oddCoreOf N
  have hAO : A ≤ normalizer (O : Set G) := (hAY.trans hYN).trans hNO
  have hP : Odd (Nat.card (A ⊔ O : Subgroup G)) :=
    odd_card_sup hAO hA (Balance.odd_card_oddCoreOf N)
  have hPN : A ⊔ O ≤ N := sup_le (hAY.trans hYN) hON
  have hoN : ∀ o ∈ O, o ∈ normalizer ((A ⊔ O : Subgroup G) : Set G) := by
    have key : ∀ o ∈ O, ∀ x ∈ (A ⊔ O : Subgroup G), o * x * o⁻¹ ∈ (A ⊔ O : Subgroup G) := by
      intro o ho x hx
      have hx' : x ∈ ((A ⊔ O : Subgroup G) : Set G) := hx
      rw [coe_mul_of_left_le_normalizer_right _ _ hAO] at hx'
      obtain ⟨a, ha, b, hb, rfl⟩ := hx'
      have h1 : o * a * o⁻¹ * a⁻¹ ∈ O := by
        have := (mem_normalizer_iff.mp (hAO ha) o⁻¹).mp (inv_mem ho)
        have e : o * a * o⁻¹ * a⁻¹ = o * (a * o⁻¹ * a⁻¹) := by group
        rw [e]
        exact mul_mem ho this
      have h2 : o * b * o⁻¹ ∈ O := mul_mem (mul_mem ho hb) (inv_mem ho)
      have e : o * (a * b) * o⁻¹ = (o * a * o⁻¹ * a⁻¹) * a * (o * b * o⁻¹) := by group
      rw [e]
      exact mul_mem (mul_mem (mem_sup_right h1) (mem_sup_left ha)) (mem_sup_right h2)
    intro o ho
    exact mem_normalizer_of_forall (key o ho) (by simpa using key o⁻¹ (inv_mem ho))
  have hNP : N ≤ normalizer ((A ⊔ O : Subgroup G) : Set G) := by
    intro n hn
    have hn' : n ∈ ((Y ⊔ O : Subgroup G) : Set G) := hN hn
    rw [coe_mul_of_left_le_normalizer_right _ _ (hYN.trans hNO)] at hn'
    obtain ⟨y, hy, o, ho, rfl⟩ := hn'
    exact mul_mem (le_normalizer_sup hYA (hYN.trans hNO) hy) (hoN o ho)
  exact le_sup_left.trans (Completion.le_oddCoreOf hPN hNP hP)

omit [Finite G] in
theorem normalClosureIn_le_of_conj {H S X : Subgroup G}
    (h : ∀ c ∈ H, ∀ a ∈ S, c * a * c⁻¹ ∈ X) : normalClosureIn H S ≤ X := by
  rintro _ ⟨y, hy, rfl⟩
  have hle : normalClosure ((S.subgroupOf H : Subgroup H) : Set H) ≤ X.subgroupOf H := by
    change Subgroup.closure (Group.conjugatesOfSet _) ≤ _
    refine (closure_le _).mpr fun z hz => ?_
    obtain ⟨a, ha, haz⟩ := Set.mem_iUnion₂.1 hz
    obtain ⟨c, rfl⟩ := isConj_iff.1 haz
    exact mem_subgroupOf.mpr (h c c.2 a (mem_subgroupOf.mp ha))
  exact mem_subgroupOf.mp (hle hy)

theorem exists_conj_eq (T : Sylow 2 G) {S H : Subgroup G} (hST : S ≤ T)
    (hS : fusionStronglyClosed (S : Set G) T) (hSH : S ≤ H) {c a : G} (hc : c ∈ H)
    (ha : a ∈ S) : ∃ m ∈ normalClosureIn H S, ∃ s ∈ S, c * a * c⁻¹ = m⁻¹ * s * m := by
  obtain ⟨m, hm, hmeq⟩ := exists_conj_normalClosureIn T hST hS hSH (inv_mem hc)
  have h1 : c * a * c⁻¹ ∈ conjSub c⁻¹ S := by
    rw [mem_conjSub]
    simpa [mul_assoc] using ha
  rw [hmeq, mem_conjSub] at h1
  exact ⟨m, hm, _, h1, by group⟩

theorem normalClosureIn_le_normalClosureIn (T : Sylow 2 G) {S H L : Subgroup G} (hST : S ≤ T)
    (hS : fusionStronglyClosed (S : Set G) T) (hSH : S ≤ H) (hHL : normalClosureIn H S ≤ L) :
    normalClosureIn H S ≤ normalClosureIn L S := by
  have hSH' : S ≤ normalClosureIn H S := fun x hx =>
    ⟨⟨x, hSH hx⟩, subset_normalClosure (mem_subgroupOf.mpr hx), rfl⟩
  have hSL : S ≤ L := hSH'.trans hHL
  refine normalClosureIn_le_of_conj fun c hc a ha => ?_
  obtain ⟨m, hm, s, hs, e⟩ := exists_conj_eq T hST hS hSH hc ha
  rw [e]
  refine ⟨⟨m, hHL hm⟩⁻¹ * ⟨s, hSL hs⟩ * ⟨m, hHL hm⟩⁻¹⁻¹, ?_, by simp⟩
  exact (normalClosure_normal).conj_mem _ (subset_normalClosure (mem_subgroupOf.mpr hs)) _

theorem normalClosureIn_le_of_le_normalizer (T : Sylow 2 G) {S L X : Subgroup G} (hST : S ≤ T)
    (hS : fusionStronglyClosed (S : Set G) T) (hSL : S ≤ L) (hSX : S ≤ X)
    (hX : normalClosureIn L S ≤ normalizer (X : Set G)) : normalClosureIn L S ≤ X := by
  refine normalClosureIn_le_of_conj fun c hc a ha => ?_
  obtain ⟨m, hm, s, hs, e⟩ := exists_conj_eq T hST hS hSL hc ha
  rw [e]
  have := (mem_normalizer_iff.mp (hX (inv_mem hm)) s).mp (hSX hs)
  simpa using this

end CFSG.Goldschmidt75
