module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Linked

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G]

structure MainSetting (Q : Subgroup G) : Prop where
  tight : TightlyEmbedded Q
  proper : normalizer (Q : Set G) ≠ ⊤
  four : HasFourGroup (twoPrimeLayerIn Q)
  caseI : ∀ a b : G, CaseIPair (rightConjugate Q b) (rightConjugate Q a)
  star : ∀ (a b : G) (X : Subgroup G), IsPGroup 2 X → centralizer (X : Set G) ≠ ⊤ →
    CoversLayer X (rightConjugate Q a) → CoversLayer X (rightConjugate Q b) →
    rightConjugate Q a = rightConjugate Q b ∨ Linked (rightConjugate Q a) (rightConjugate Q b)

theorem mainSetting_of_normalInCentralizers (h3 : AschbacherTheorem3.Theorem3Statement)
    {Q : Subgroup G} (htight : TightlyEmbedded Q) (hNQ : normalizer (Q : Set G) ≠ ⊤)
    (h4 : HasFourGroup (twoPrimeLayerIn Q)) (hno : NoThm3Alt3 Q) (hN : NormalInCentralizers Q) :
    MainSetting Q where
  tight := htight
  proper := hNQ
  four := h4
  caseI := caseIPair_rightConjugate h3 htight hno
  star := fun _ _ _ hX hXc hXa hXb =>
    eq_or_linked_of_normalInCentralizers h3 htight hno hN h4 hX hXc hXa hXb

namespace MainSetting

variable {Q : Subgroup G} (hS : MainSetting Q)
include hS

theorem four_rightConjugate (a : G) : HasFourGroup (twoPrimeLayerIn (rightConjugate Q a)) := by
  rw [twoPrimeLayerIn_rightConjugate]
  exact hS.four.map (MulAut.conj a⁻¹).injective

theorem trans {a b c : G} (hab : Linked (rightConjugate Q a) (rightConjugate Q b))
    (hbc : Linked (rightConjugate Q b) (rightConjugate Q c)) :
    Linked (rightConjugate Q a) (rightConjugate Q c) := by
  by_cases hAB : rightConjugate Q a = rightConjugate Q b
  · rwa [hAB]
  by_cases hBC : rightConjugate Q b = rightConjugate Q c
  · rwa [← hBC]
  obtain ⟨E, hEK, hE, hE4⟩ := hS.four_rightConjugate b
  have hne : E ≠ ⊥ := fun h => by rw [h, card_bot] at hE4; norm_num at hE4
  obtain ⟨⟨t, htE⟩, ht1⟩ := ne_bot_iff_exists_ne_one.mp hne
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have ht2 : t ^ 2 ^ 1 = 1 := by simpa using hE t htE
  have htK := hEK htE
  have hXa := coversLayer_zpowers_of_linked hS.tight hAB hab htK ht2
  have hXc := coversLayer_zpowers_of_linked hS.tight (Ne.symm hBC) hbc.symm htK ht2
  have hXc' := centralizer_zpowers_ne_top hS.tight hS.proper (twoPrimeLayerIn_le _ htK)
    (orderOf_eq_prime (hE t htE) ht1')
  rcases hS.star a c _ (isPGroup_zpowers_of_pow_eq_one ht2) hXc' hXa hXc with h | h
  · rw [h]
    exact Linked.refl _
  · exact h

theorem linked_of_le {a b : G}
    (h : twoPrimeLayerIn (rightConjugate Q a) ≤ normalizer (rightConjugate Q b : Set G)) :
    Linked (rightConjugate Q a) (rightConjugate Q b) :=
  ⟨h, twoPrimeLayerIn_le_normalizer_of_le hS.four (hS.caseI a b) h⟩

end MainSetting

@[expose] def linkedClass (Q : Subgroup G) : Set (Subgroup G) :=
  {A | (∃ a : G, A = rightConjugate Q a) ∧ Linked Q A}

@[expose] def linkedLayer (Q : Subgroup G) : Subgroup G :=
  ⨆ A ∈ linkedClass Q, twoPrimeLayerIn A

omit [Finite G] in
theorem self_mem_linkedClass (Q : Subgroup G) : Q ∈ linkedClass Q :=
  ⟨⟨1, (rightConjugate_one Q).symm⟩, Linked.refl Q⟩

omit [Finite G] in
theorem twoPrimeLayerIn_le_linkedLayer {Q A : Subgroup G} (hA : A ∈ linkedClass Q) :
    twoPrimeLayerIn A ≤ linkedLayer Q :=
  le_biSup (fun A => twoPrimeLayerIn A) hA

theorem mem_normalizer_linkedLayer_of_subset {Q : Subgroup G} {g : G}
    (hg : ∀ A ∈ linkedClass Q, rightConjugate A g ∈ linkedClass Q) :
    g ∈ normalizer (linkedLayer Q : Set G) := by
  rw [← rightConjugate_eq_self_iff]
  have hle : rightConjugate (linkedLayer Q) g ≤ linkedLayer Q := by
    unfold linkedLayer
    rw [rightConjugate, Subgroup.map_iSup]
    refine iSup_le fun A => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hA => ?_
    change rightConjugate (twoPrimeLayerIn A) g ≤ _
    rw [← twoPrimeLayerIn_rightConjugate]
    exact twoPrimeLayerIn_le_linkedLayer (hg A hA)
  exact eq_of_le_of_card_ge hle (rightConjugate_card _ g).ge

namespace MainSetting

variable {Q : Subgroup G} (hS : MainSetting Q)
include hS

theorem linked_of_mem {A B : Subgroup G} (hA : A ∈ linkedClass Q) (hB : B ∈ linkedClass Q) :
    Linked A B := by
  obtain ⟨⟨a, rfl⟩, hQA⟩ := hA
  obtain ⟨⟨b, rfl⟩, hQB⟩ := hB
  have hQA' : Linked (rightConjugate Q 1) (rightConjugate Q a) := by
    rwa [rightConjugate_one]
  have hQB' : Linked (rightConjugate Q 1) (rightConjugate Q b) := by
    rwa [rightConjugate_one]
  exact hS.trans hQA'.symm hQB'

theorem mem_linkedClass_of_linked {A : Subgroup G} (hA : A ∈ linkedClass Q) {b : G}
    (h : Linked A (rightConjugate Q b)) : rightConjugate Q b ∈ linkedClass Q := by
  obtain ⟨⟨a, rfl⟩, hQA⟩ := hA
  refine ⟨⟨b, rfl⟩, ?_⟩
  have hQA' : Linked (rightConjugate Q 1) (rightConjugate Q a) := by
    rwa [rightConjugate_one]
  have := hS.trans hQA' h
  rwa [rightConjugate_one] at this

theorem linkedLayer_le_normalizer {A : Subgroup G} (hA : A ∈ linkedClass Q) :
    linkedLayer Q ≤ normalizer (twoPrimeLayerIn A : Set G) :=
  iSup₂_le fun _ hB => (hS.linked_of_mem hB hA).1.trans
    (normalizer_le_normalizer_twoPrimeLayerIn A)

theorem normalIn_linkedLayer {A : Subgroup G} (hA : A ∈ linkedClass Q) :
    NormalIn (twoPrimeLayerIn A) (linkedLayer Q) :=
  normalIn_of_le_normalizer (twoPrimeLayerIn_le_linkedLayer hA) (hS.linkedLayer_le_normalizer hA)

theorem linkedLayer_le_normalizer_self : linkedLayer Q ≤ normalizer (Q : Set G) :=
  iSup₂_le fun _ hB => (hS.linked_of_mem hB (self_mem_linkedClass Q)).1

theorem rightConjugate_mem_linkedClass_of_mem_normalizer {h : G}
    (hh : h ∈ normalizer (linkedLayer Q : Set G)) {A : Subgroup G} (hA : A ∈ linkedClass Q) :
    rightConjugate A h ∈ linkedClass Q := by
  obtain ⟨⟨a, rfl⟩, hQA⟩ := hA
  rw [rightConjugate_mul]
  refine ⟨⟨a * h, rfl⟩, ?_⟩
  have hle : twoPrimeLayerIn (rightConjugate Q (a * h)) ≤
      normalizer (rightConjugate Q 1 : Set G) := by
    rw [rightConjugate_one, ← rightConjugate_mul, twoPrimeLayerIn_rightConjugate]
    have h1 : rightConjugate (twoPrimeLayerIn (rightConjugate Q a)) h ≤
        rightConjugate (linkedLayer Q) h :=
      AschbacherTheorem3.rightConjugate_le_rightConjugate
        (twoPrimeLayerIn_le_linkedLayer ⟨⟨a, rfl⟩, hQA⟩) h
    rw [(rightConjugate_eq_self_iff _ h).mpr hh] at h1
    exact h1.trans hS.linkedLayer_le_normalizer_self
  have := (hS.linked_of_le hle).symm
  rwa [rightConjugate_one] at this

theorem mem_normalizer_linkedLayer_of_linked {g : G} (hg : Linked Q (rightConjugate Q g)) :
    g ∈ normalizer (linkedLayer Q : Set G) := by
  refine mem_normalizer_linkedLayer_of_subset fun A hA => ?_
  obtain ⟨⟨a, rfl⟩, hQA⟩ := hA
  rw [rightConjugate_mul]
  refine hS.mem_linkedClass_of_linked (A := rightConjugate Q g) ⟨⟨g, rfl⟩, hg⟩ ?_
  have h1 : Linked (rightConjugate (rightConjugate Q 1) g)
      (rightConjugate (rightConjugate Q a) g) :=
    linked_rightConjugate_iff.mpr (by rwa [rightConjugate_one])
  rwa [rightConjugate_one, rightConjugate_mul] at h1

end MainSetting

end CFSG.ComponentClassification.Asc75T4
