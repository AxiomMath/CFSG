module

public import CFSG.CGT.PushingUpLit.CGT6.Nine7Defs

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Nine7

open CFSG (conjugate)
open scoped commutatorElement

section Basic

variable {G : Type} [Group G]

theorem le_Dgrp {A B B' : Subgroup G} (hB' : B' ∈ ConjCl A) (h : Rel B B') : B' ≤ Dgrp A B :=
  le_iSup₂_of_le B' ⟨hB', h⟩ le_rfl

theorem Dgrp_le {A B X : Subgroup G} (h : ∀ B' ∈ ConjCl A, Rel B B' → B' ≤ X) : Dgrp A B ≤ X :=
  iSup₂_le fun B' hB' => h B' hB'.1 hB'.2

theorem Dgrp_conjugate {A B : Subgroup G} (g : G) :
    conjugate (Dgrp A B) g = Dgrp A (conjugate B g) := by
  apply le_antisymm
  · rw [Dgrp, conjugate_iSup]
    refine iSup_le fun B' => ?_
    rw [conjugate_iSup]
    refine iSup_le fun hB' => ?_
    exact le_Dgrp (ConjCl.cj hB'.1 g) (hB'.2.cj g)
  · refine Dgrp_le fun B'' hB'' h'' => ?_
    have h0 : Rel B (conjugate B'' g⁻¹) := by
      have := h''.cj g⁻¹
      rwa [conjugate_conjugate_inv] at this
    have hmem : conjugate B'' g⁻¹ ∈ ConjCl A := ConjCl.cj hB'' g⁻¹
    have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (le_Dgrp hmem h0)
    change conjugate (conjugate B'' g⁻¹) g ≤ conjugate (Dgrp A B) g at this
    rwa [conjugate_inv_conjugate] at this

theorem Dgrp_le_normalizer {A B : Subgroup G} : Dgrp A B ≤ Subgroup.normalizer (B : Set G) := by
  refine Dgrp_le fun B' _ h => ?_
  rcases h with rfl | h
  · exact Subgroup.le_normalizer
  · have h' : ⁅B', B⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact h
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h').trans
      (Subgroup.centralizer_le_normalizer _)

theorem normal_in_Dgrp {A B : Subgroup G} :
    (B.subgroupOf (Dgrp A B)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer Dgrp_le_normalizer

theorem isCompIn_Dgrp {A B : Subgroup G} (hA : QS A) (hB : B ∈ ConjCl A) :
    IsCompIn B (Dgrp A B) :=
  isCompIn_of_normal (le_Dgrp hB (Rel.refl B)) normal_in_Dgrp (ConjCl.qs hA hB)

theorem mem_normalizer_of_conjugate_eq {X : Subgroup G} {g : G} (h : conjugate X g = X) :
    g ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have := congrArg (fun Z : Subgroup G => x ∈ Z) h
  simp only [mem_conjugate] at this
  exact Eq.to_iff this.symm

theorem conjugate_eq_of_mem_normalizer {X : Subgroup G} {g : G}
    (h : g ∈ Subgroup.normalizer (X : Set G)) : conjugate X g = X := by
  ext x
  rw [mem_conjugate]
  exact (Subgroup.mem_normalizer_iff.1 h x).symm

@[expose] def TrivCl (A : Subgroup G) : Prop := ∀ B ∈ ConjCl A, Rel A B → B = A

theorem qs_commutator_ne_bot {A : Subgroup G} (hA : QS A) : ⁅A, A⁆ ≠ ⊥ := by
  intro h
  have hA' : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
  have hcenter : Subgroup.center ↥A = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    have := Subgroup.mem_centralizer_iff.1 (hA' y.2) x x.2
    exact Subtype.ext this.symm
  have hsimple : IsSimpleGroup (↥A ⧸ Subgroup.center ↥A) := hA.2
  have hsub : Subsingleton (↥A ⧸ Subgroup.center ↥A) := by
    rw [hcenter]
    exact QuotientGroup.subsingleton_quotient_top
  obtain ⟨x, y, hxy⟩ := hsimple.toNontrivial.exists_pair_ne
  exact hxy (Subsingleton.elim x y)

theorem isCompIn_normalizer {A : Subgroup G} (hA : QS A) :
    IsCompIn A (Subgroup.normalizer (A : Set G)) :=
  isCompIn_of_normal Subgroup.le_normalizer inferInstance hA

theorem isCompIn_centralizer_involution {A : Subgroup G} (hA : QS A) (hs : Star A) {a : G}
    (ha : orderOf a = 2) (hAa : A ≤ Subgroup.centralizer ({a} : Set G)) :
    IsCompIn A (Subgroup.centralizer ({a} : Set G)) :=
  ⟨hAa, hs a ha hAa, hA⟩

theorem commutator_conjugate_ne_bot {A : Subgroup G} (hA : QS A) (htriv : TrivCl A) (g : G) :
    ⁅A, conjugate A g⁆ ≠ ⊥ := by
  intro h
  have := htriv _ (ConjCl.cj (mem_ConjCl_self A) g) (Or.inr h)
  rw [this] at h
  exact qs_commutator_ne_bot hA h

theorem isSubnormal_of_central_involution {A : Subgroup G} (hs : Star A) {a : G}
    (ha : orderOf a = 2) (hAa : A ≤ Subgroup.centralizer ({a} : Set G))
    (hz : a ∈ Subgroup.center G) : A.IsSubnormal := by
  have htop : Subgroup.centralizer ({a} : Set G) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [mem_centralizer_single]
    exact (Subgroup.mem_center_iff.1 hz x).symm
  have h := hs a ha hAa
  rw [htop] at h
  have hsurj : Function.Surjective ((⊤ : Subgroup G).subtype) := fun x => ⟨⟨x, trivial⟩, rfl⟩
  have h' := h.map hsurj
  rwa [Subgroup.map_subgroupOf_eq_of_le (le_top : A ≤ ⊤)] at h'

end Basic

section Finite

variable {G : Type} [Group G] [Finite G]

theorem isCompIn_centralizer_of_comm {A B B' : Subgroup G} (hA : QS A) (hs : Star A)
    (hB : B ∈ ConjCl A) (hB' : B' ∈ ConjCl A) (hcomm : ⁅B, B'⁆ = ⊥) :
    IsCompIn B' (Subgroup.centralizer (B : Set G)) := by
  obtain ⟨b, hbB, hb2⟩ := exists_involution_of_qs (ConjCl.qs hA hB)
  have hB'C : B' ≤ Subgroup.centralizer (B : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hcomm
  have hCb : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.centralizer_le (by simpa using hbB)
  have hsub := ConjCl.star hs hB' b hb2 (hB'C.trans hCb)
  exact ⟨hB'C, CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hCb hsub, ConjCl.qs hA hB'⟩

theorem Rel.trans' {A B B' B'' : Subgroup G} (hA : QS A) (hs : Star A) (hB : B ∈ ConjCl A)
    (hB' : B' ∈ ConjCl A) (hB'' : B'' ∈ ConjCl A) (h₁ : Rel B B') (h₂ : Rel B' B'') :
    Rel B B'' := by
  rcases h₁ with rfl | h₁
  · exact h₂
  rcases h₂ with rfl | h₂
  · exact Or.inr h₁
  by_cases hne : B = B''
  · exact Or.inl hne
  refine Or.inr (commute_of_isCompIn_ne (X := Subgroup.centralizer (B' : Set G)) ?_ ?_ hne)
  · exact isCompIn_centralizer_of_comm hA hs hB' hB (by rw [Subgroup.commutator_comm]; exact h₁)
  · exact isCompIn_centralizer_of_comm hA hs hB' hB'' h₂

theorem Dgrp_eq {A B B' : Subgroup G} (hA : QS A) (hs : Star A) (hB : B ∈ ConjCl A)
    (hB' : B' ∈ ConjCl A) (h : Rel B B') : Dgrp A B = Dgrp A B' := by
  apply le_antisymm
  · refine Dgrp_le fun B'' hB'' h'' => le_Dgrp hB'' ?_
    exact Rel.trans' hA hs hB' hB hB'' h.symm h''
  · refine Dgrp_le fun B'' hB'' h'' => le_Dgrp hB'' ?_
    exact Rel.trans' hA hs hB hB' hB'' h h''

theorem mem_normalizer_Dgrp_of_rel' {A B : Subgroup G} (hA : QS A) (hs : Star A) (hB : B ∈ ConjCl A)
    {g : G} (h : Rel B (conjugate B g)) : g ∈ Subgroup.normalizer (Dgrp A B : Set G) := by
  apply mem_normalizer_of_conjugate_eq
  rw [Dgrp_conjugate]
  exact (Dgrp_eq hA hs hB (ConjCl.cj hB g) h).symm

theorem mem_normalizer_Dgrp_of_rel {A : Subgroup G} (hA : QS A) (hs : Star A) {g : G}
    (h : Rel A (conjugate A g)) : g ∈ Subgroup.normalizer (Dgrp A A : Set G) :=
  mem_normalizer_Dgrp_of_rel' hA hs (mem_ConjCl_self A) h

theorem rel_conjugate_of_mem_normalizer {A : Subgroup G} (hA : QS A) {g : G}
    (hg : g ∈ Subgroup.normalizer (Dgrp A A : Set G)) : Rel A (conjugate A g) := by
  have hAD : IsCompIn A (Dgrp A A) := isCompIn_Dgrp hA (mem_ConjCl_self A)
  have hBD := hAD.cj g
  rw [conjugate_eq_of_mem_normalizer hg] at hBD
  by_cases hne : A = conjugate A g
  · exact Or.inl hne
  · exact Or.inr (commute_of_isCompIn_ne hAD hBD hne)

theorem Delta_eq_of_trivCl {A X : Subgroup G} (hA : QS A) (htriv : TrivCl A)
    (hAX : IsCompIn A X) : Delta A X = A := by
  apply le_antisymm
  · refine iSup₂_le fun B hB => ?_
    have hBc : IsCompIn B X := ⟨hB.2.1, hB.2.2, ConjCl.qs hA hB.1⟩
    by_cases hne : B = A
    · rw [hne]
    · exact absurd (htriv B hB.1 (Or.inr (commute_of_isCompIn_ne hAX hBc (Ne.symm hne)))) hne
  · exact le_iSup₂_of_le A ⟨mem_ConjCl_self A, hAX.1, hAX.2.1⟩ le_rfl

theorem delta_normalizer_eq {A : Subgroup G} (hA : QS A) (htriv : TrivCl A) :
    Delta A (Subgroup.normalizer (A : Set G)) = A :=
  Delta_eq_of_trivCl hA htriv (isCompIn_normalizer hA)

theorem delta_centralizer_eq {A : Subgroup G} (hA : QS A) (hs : Star A) (htriv : TrivCl A) {a : G}
    (ha : orderOf a = 2) (hAa : A ≤ Subgroup.centralizer ({a} : Set G)) :
    Delta A (Subgroup.centralizer ({a} : Set G)) = A :=
  Delta_eq_of_trivCl hA htriv (isCompIn_centralizer_involution hA hs ha hAa)

end Finite

end CFSG.CGT.PushingUpLit.CGT6.Nine7
