module

public import CFSG.CGT.PushingUpLit.CGT6.Nine7Five

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Nine7

open CFSG (conjugate)
open CFSG.Open
open CFSG.ComponentClassification
open CFSG.ComponentClassification.AschbacherKnownGroup (AschbacherKnownGroupFacts)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

section Delta

variable {G : Type} [Group G] [Finite G]

theorem delta_le_Dgrp {A X : Subgroup G} (hA : QS A) (hAX : IsCompIn A X) :
    Delta A X ≤ Dgrp A A := by
  refine iSup₂_le fun B hB => ?_
  have hBc : IsCompIn B X := ⟨hB.2.1, hB.2.2, ConjCl.qs hA hB.1⟩
  refine le_Dgrp hB.1 ?_
  by_cases hne : A = B
  · exact Or.inl hne
  · exact Or.inr (commute_of_isCompIn_ne hAX hBc hne)

theorem delta_normalizer_eq_Dgrp {A : Subgroup G} (hA : QS A) (hs : Star A) :
    Delta A (Subgroup.normalizer (A : Set G)) = Dgrp A A := by
  refine le_antisymm (delta_le_Dgrp hA (isCompIn_normalizer hA)) ?_
  refine Dgrp_le fun B hB hrel => ?_
  refine le_iSup₂_of_le B ⟨hB, ?_⟩ le_rfl
  rcases hrel with rfl | hcomm
  · exact ⟨Subgroup.le_normalizer, (isCompIn_normalizer hA).2.1⟩
  · have hC : IsCompIn B (Subgroup.centralizer (A : Set G)) :=
      isCompIn_centralizer_of_comm hA hs (mem_ConjCl_self A) hB hcomm
    have hnorm : Subgroup.normalizer (A : Set G) ≤
        Subgroup.normalizer (Subgroup.centralizer (A : Set G) : Set G) := by
      intro g hg
      apply mem_normalizer_of_conjugate_eq
      rw [conjugate_centralizer, conjugate_eq_of_mem_normalizer hg]
    have hN : IsCompIn B (Subgroup.normalizer (A : Set G)) :=
      hC.trans (Subgroup.normal_subgroupOf_of_le_normalizer hnorm).isSubnormal
        (Subgroup.centralizer_le_normalizer _)
    exact ⟨hN.1, hN.2.1⟩

omit [Finite G] in
theorem isSubnormal_of_normalizer_top {A : Subgroup G} (hA : QS A)
    (hN : Subgroup.normalizer (Dgrp A A : Set G) = ⊤) : A.IsSubnormal := by
  have hnormal : (Dgrp A A).Normal := Subgroup.normalizer_eq_top_iff.1 hN
  exact Subgroup.IsSubnormal.trans (le_Dgrp (mem_ConjCl_self A) (Rel.refl A))
    (isCompIn_Dgrp hA (mem_ConjCl_self A)).2.1 hnormal.isSubnormal

theorem eq_of_card_two {α : Type} [Finite α] (h : Nat.card α = 2) {x y z : α} (hxy : x ≠ y)
    (hxz : x ≠ z) : y = z := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hc : Fintype.card α = 2 := by rwa [← Nat.card_eq_fintype_card]
  by_contra hyz
  have h3 : ({x, y, z} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hyz]
    simp [hxy, hxz]
  have := Finset.card_le_univ ({x, y, z} : Finset α)
  omega

omit [Finite G] in
theorem orderOf_mul_involutions {z₁ z₂ : G} (h₁ : orderOf z₁ = 2) (h₂ : orderOf z₂ = 2)
    (hc : z₁ * z₂ = z₂ * z₁) (hne : z₁ ≠ z₂) : orderOf (z₁ * z₂) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : z₁ ^ 2 = 1 := by rw [← h₁]; exact pow_orderOf_eq_one z₁
  have h2 : z₂ ^ 2 = 1 := by rw [← h₂]; exact pow_orderOf_eq_one z₂
  refine orderOf_eq_prime ?_ ?_
  · rw [(Commute.mul_pow (show Commute z₁ z₂ from hc)), h1, h2, one_mul]
  · intro h
    apply hne
    have h3 : z₁ = z₂⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [h3]
    have : z₂ * z₂ = 1 := by rw [← pow_two]; exact h2
    exact inv_eq_of_mul_eq_one_right this

end Delta

section Main

variable {G : Type} [Group G] [Finite G]

@[expose] def NineSeven (A : Subgroup G) : Prop :=
  (Delta A (Subgroup.normalizer (A : Set G)) = A ∧
      (∀ a : G, orderOf a = 2 → A ≤ Subgroup.centralizer ({a} : Set G) →
        Delta A (Subgroup.centralizer ({a} : Set G)) = A) ∧
      ∀ g : G, ⁅A, conjugate A g⁆ ≠ ⊥) ∨
    (∃ x : G, ⁅A, conjugate A x⁆ = ⊥ ∧
      Delta A (Subgroup.normalizer (A : Set G)) = A ⊔ conjugate A x ∧
      Open.pRank 2 A = 1 ∧
      (∀ a : G, orderOf a = 2 → A ≤ Subgroup.centralizer ({a} : Set G) →
        Delta A (Subgroup.centralizer ({a} : Set G)) ≤ A ⊔ conjugate A x) ∧
      (∀ g : G, ⁅A, conjugate A g⁆ = ⊥ → conjugate A g = conjugate A x) ∧
      ∃ z : G, orderOf z = 2 ∧ z ∈ A ∧ z ∈ conjugate A x ∧
        z ∈ Subgroup.centralizer (A : Set G) ∧ z ∈ Subgroup.centralizer (conjugate A x : Set G)) ∨
    A.IsSubnormal

theorem nine_seven_star (h5 : GSThmB.AschbacherTheorem5Input) (hK : AschbacherKnownGroupFacts)
    {A : Subgroup G} (hA : QS A) (hs : Star A)
    (hglaub : GlaubermanAt (↥A ⧸ Subgroup.center ↥A)) : NineSeven A := by
  unfold NineSeven
  by_cases h3 : ∃ a : G, orderOf a = 2 ∧ A ≤ Subgroup.centralizer ({a} : Set G) ∧
      a ∈ Subgroup.center G
  · obtain ⟨a, ha, hAa, hz⟩ := h3
    exact Or.inr (Or.inr (isSubnormal_of_central_involution hs ha hAa hz))
  push Not at h3
  by_cases htriv : TrivCl A
  · exact Or.inl ⟨delta_normalizer_eq hA htriv,
      fun a ha hAa => delta_centralizer_eq hA hs htriv ha hAa, commutator_conjugate_ne_bot hA htriv⟩
  unfold TrivCl at htriv
  push Not at htriv
  obtain ⟨B₂, hB₂, hrel, hne⟩ := htriv
  have hcomm : ⁅A, B₂⁆ = ⊥ := by
    rcases hrel with h | h
    · exact absurd h.symm hne
    · exact h
  have hset : Setting A :=
    ⟨hA, hs, fun B hB => glaubermanAt_of_mem_ConjCl hB hglaub, ⟨B₂, hB₂, hcomm⟩⟩
  have hB₂c : B₂ ∈ Clq A := ⟨hB₂, hrel⟩
  by_cases hN : Subgroup.normalizer (Dgrp A A : Set G) = ⊤
  · exact Or.inr (Or.inr (isSubnormal_of_normalizer_top hA hN))
  rcases theorem5_clique h5 hK hset hN with h1 | ⟨h2, hall⟩
  · exfalso
    have hlt : 1 < Nat.card (Clq A) := by
      rw [Finite.one_lt_card_iff_nontrivial]
      exact ⟨⟨⟨A, mem_Clq_self A⟩, ⟨B₂, hB₂c⟩, fun h => hne (congrArg Subtype.val h).symm⟩⟩
    omega
  refine Or.inr (Or.inl ?_)
  obtain ⟨x, hx⟩ := hB₂
  have hAB : A ≠ B₂ := fun h => hne h.symm
  have hclq : ∀ B ∈ Clq A, B = A ∨ B = B₂ := by
    intro B hB
    by_cases hBA : B = A
    · exact Or.inl hBA
    · refine Or.inr ?_
      have := eq_of_card_two h2 (x := (⟨A, mem_Clq_self A⟩ : Clq A)) (y := ⟨B, hB⟩)
        (z := ⟨B₂, hB₂c⟩) (fun h => hBA (congrArg Subtype.val h).symm)
        (fun h => hAB (congrArg Subtype.val h))
      exact congrArg Subtype.val this
  have hD : Dgrp A A = A ⊔ B₂ := by
    refine le_antisymm (Dgrp_le fun B hB hrelB => ?_)
      (sup_le (le_Dgrp (mem_ConjCl_self A) (Rel.refl A)) (le_Dgrp ⟨x, hx⟩ hrel))
    rcases hclq B ⟨hB, hrelB⟩ with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  have hrank := hall A (mem_Clq_self A) B₂ hB₂c hAB
  have hrank' := hall B₂ hB₂c A (mem_Clq_self A) hne
  have hAinv := exists_involution_of_qs hA
  refine ⟨x, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hx]; exact hcomm
  · rw [delta_normalizer_eq_Dgrp hA hs, hD, hx]
  · exact le_antisymm hrank.1 (by
      obtain ⟨t, ht, ht2⟩ := hAinv
      exact one_le_pRank_of_involution ht ht2)
  · intro a ha hAa
    rw [← hx, ← hD]
    exact delta_le_Dgrp hA (isCompIn_centralizer_involution hA hs ha hAa)
  · intro g hg
    have hgc : conjugate A g ∈ Clq A := ⟨ConjCl.cj (mem_ConjCl_self A) g, Or.inr hg⟩
    rcases hclq _ hgc with h | h
    · exfalso
      rw [h] at hg
      exact qs_commutator_ne_bot hA hg
    · rw [h, hx]
  ·
    have hex : ∀ {B : Subgroup G}, QS B → Open.pRank 2 B ≤ 1 →
        ∃ u ∈ B, orderOf u = 2 ∧ u ∈ Subgroup.centralizer (B : Set G) := by
      intro B hB hr
      by_contra hcon
      push Not at hcon
      have := two_le_pRank_of_no_central_involution hB (fun u hu hu2 hc => hcon u hu hu2 hc)
      omega
    obtain ⟨z₁, hz₁, hz₁2, hz₁c⟩ := hex hA hrank.1
    obtain ⟨z₂, hz₂, hz₂2, hz₂c⟩ := hex (ConjCl.qs hA ⟨x, hx⟩) hrank'.1
    have hcen := hrank.2 z₁ hz₁ z₂ hz₂ hz₁2 hz₂2 hz₁c hz₂c
    by_cases hzz : z₁ = z₂
    · subst hzz
      rw [← hx]
      exact ⟨z₁, hz₁2, hz₁, hz₂, hz₁c, hz₂c⟩
    · exfalso
      have hc12 : z₁ * z₂ = z₂ * z₁ := mul_comm_of_commutator_eq_bot hcomm hz₁ hz₂
      have hZ : z₁ * z₂ ∈ Subgroup.center G := hcen.resolve_left hzz
      refine h3 (z₁ * z₂) (orderOf_mul_involutions hz₁2 hz₂2 hc12 hzz) ?_ hZ
      intro y hy
      rw [mem_centralizer_single]
      have h1 : y * z₁ = z₁ * y := Subgroup.mem_centralizer_iff.1 hz₁c y hy
      have h2 : y * z₂ = z₂ * y := mul_comm_of_commutator_eq_bot hcomm hy hz₂
      calc z₁ * z₂ * y = z₁ * (z₂ * y) := by group
        _ = z₁ * (y * z₂) := by rw [h2]
        _ = (z₁ * y) * z₂ := by group
        _ = (y * z₁) * z₂ := by rw [h1]
        _ = y * (z₁ * z₂) := by group

omit [Finite G] in
theorem inCatalog_center_quotient (hKP : Assembly.KProper Assembly.InCatalog G) {A : Subgroup G}
    (hA : QS A) (hAtop : A ≠ ⊤) : Assembly.InCatalog (↥A ⧸ Subgroup.center ↥A) := by
  set L : Subgroup G := (Subgroup.center ↥A).map A.subtype with hL
  have hLA : L ≤ A := Subgroup.map_subtype_le _
  have hLK : L.subgroupOf A = Subgroup.center ↥A :=
    Subgroup.comap_map_eq_self_of_injective A.subtype_injective _
  have : (L.subgroupOf A).Normal := by rw [hLK]; infer_instance
  let e : ↥A ⧸ L.subgroupOf A ≃* ↥A ⧸ Subgroup.center ↥A :=
    QuotientGroup.quotientMulEquivOfEq hLK
  have hsc : IsSimpleGroup (↥A ⧸ Subgroup.center ↥A) := hA.2
  have hsimple : IsSimpleGroup (↥A ⧸ L.subgroupOf A) := e.isSimpleGroup
  have hnonab : ∃ a b : ↥A ⧸ L.subgroupOf A, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_noncomm_center_quotient hA
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul, h]))⟩
  obtain ⟨i, ⟨φ⟩⟩ := hKP A L hAtop hLA hsimple hnonab
  exact ⟨i, ⟨e.symm.trans φ⟩⟩

theorem nine_seven_star_of_schreier (h5 : GSThmB.AschbacherTheorem5Input)
    (hK : AschbacherKnownGroupFacts) (hS : SchreierFor Assembly.InCatalog) {A : Subgroup G}
    (hA : QS A) (hs : Star A) (hcat : Assembly.InCatalog (↥A ⧸ Subgroup.center ↥A)) :
    NineSeven A :=
  nine_seven_star h5 hK hA hs (glaubermanAt_of_schreier hS hcat)

theorem nine_seven_star_of_kproper (h5 : GSThmB.AschbacherTheorem5Input)
    (hK : AschbacherKnownGroupFacts) (hS : SchreierFor Assembly.InCatalog)
    (hKP : Assembly.KProper Assembly.InCatalog G) {A : Subgroup G} (hA : QS A) (hs : Star A) :
    NineSeven A := by
  by_cases hAtop : A = ⊤
  · subst hAtop
    exact Or.inr (Or.inr Subgroup.IsSubnormal.top)
  · exact nine_seven_star_of_schreier h5 hK hS hA hs (inCatalog_center_quotient hKP hA hAtop)

end Main

end CFSG.CGT.PushingUpLit.CGT6.Nine7
