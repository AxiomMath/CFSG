module

public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Balance.QNineShapeU
public import CFSG.ClassicalInvolution.Balance.QNineModels
import CFSG.ClassicalInvolution.Balance.BootstrapExoticG2D4

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank

section Component

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)}

@[expose] def LocalLeviComponent (p f : ℕ) [Fact p.Prime] {G : Type} [Group G]
    (Ω : Set (Subgroup G)) (x : G) : Prop :=
  ∃ D : LieSystemData p f (locQuot Ω x) (locFamily Ω x), ∃ i : Fin D.card,
    (D.tag i = .PSL ∧ 3 ≤ D.rank i) ∨ D.tag i = .PSU ∨ D.tag i = .PSp ∨ HasA2Pairs (D.tag i) ∨
      (p ^ f = 9 ∧ (D.tag i = .G2 ∨ D.tag i = .trialityD4))

theorem LocalLeviComponent.of_levi {x : G} (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    (i : Fin D.card)
    (h : (D.tag i = .PSL ∧ 3 ≤ D.rank i) ∨ D.tag i = .PSU ∨ D.tag i = .PSp ∨
      HasA2Pairs (D.tag i)) :
    LocalLeviComponent p f Ω x :=
  ⟨D, i, h.imp_right fun h => h.imp_right fun h => h.imp_right Or.inl⟩

theorem LocalLeviComponent.exists_member [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) {x : G} (h : LocalLeviComponent p f Ω x) :
    ∃ L ∈ centralizingMembers Ω {x}, LeviBlockImage p f (locImg Ω x L) := by
  obtain ⟨D, i, hi⟩ := h
  rcases hi with ⟨ht, hr⟩ | ht | ht | ha | ⟨h9, hex⟩
  · obtain ⟨k, hk⟩ : ∃ k, D.rank i = k + 1 := ⟨D.rank i - 1, by omega⟩
    exact exists_member_leviBlockImage_of_psl D i ht hk (by omega)
  · have hadm := D.admissible i
    rw [ht] at hadm
    exact exists_member_leviBlockImage_of_psu hp2 hq D i ht rfl hadm.2.2.1
  · have hadm := D.admissible i
    rw [ht] at hadm
    exact exists_member_leviBlockImage_of_psp D i ht rfl hadm.2.2.1
  · exact exists_member_leviBlockImage_of_a2Tag hp2 hq D i ha
  · exact exists_member_leviBlockImage_of_g2d4 hΩ h9 D i hex

theorem LocalShapeA.localLeviComponent {m : ℕ} (hm : 2 ≤ m) {x : G}
    (h : LocalShapeA p f m Ω x) : LocalLeviComponent p f Ω x := by
  obtain ⟨D, -, -, i₁, -, -, -, ht₁, hr₁⟩ := h
  exact ⟨D, i₁, Or.inl ⟨ht₁, by omega⟩⟩

theorem LocalShapeU.localLeviComponent {m : ℕ} {x : G} (h : LocalShapeU p f m Ω x) :
    LocalLeviComponent p f Ω x := by
  obtain ⟨D, -, -, i₁, -, -, -, ht₁, -⟩ := h
  exact ⟨D, i₁, Or.inr (Or.inl ht₁)⟩

theorem LocalShapeC.localLeviComponent {m : ℕ} {x : G} (h : LocalShapeC p f m Ω x) :
    LocalLeviComponent p f Ω x := by
  obtain ⟨D, -, -, i₁, -, -, -, ht₁, -⟩ := h
  exact ⟨D, i₁, Or.inr (Or.inr (Or.inl ht₁))⟩

theorem exactMembers_of_localLeviComponent [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {x : G}
    (hP1 : LocalOddCentral Ω {x}) (h : LocalLeviComponent p f Ω x) : ExactMembers Ω := by
  obtain ⟨L, hL, hlevi⟩ := h.exists_member hp2 hq hΩ
  exact exactMembers_of_leviBlockImage hp2 hq hΩ hsingle hP1 hL hlevi

end Component

section Stage

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {E : Subgroup G}

theorem stage2_of_leviBlockImage (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {X₂ : Set G}
    (hP1 : ∀ x ∈ X₂, LocalOddCentral Ω {x}) {x : G} (hx : x ∈ X₂) {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) (h : LeviBlockImage p f (locImg Ω x L)) :
    Stage2 Ω X₂ :=
  ⟨exactMembers_of_leviBlockImage hp2 hq hΩ hsingle (hP1 x hx) hL h, hP1⟩

theorem stage2_final_of_leviBlockImage [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    {F : Type*} [Field F] {S : Set (Subgroup G)} (Fr : WeakToralFrame F Ω E S)
    (h16 : 16 ≤ Nat.card E) (hGen : FusionGenerated E)
    (hlay : ∀ a ∈ E, a ≠ 1 → LayerGenerationAt E a) {x : G} (hxE : x ∈ E) (hx1 : x ≠ 1)
    (hmeet : FrameMeetsAt Ω E S x) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (h : LeviBlockImage p f (locImg Ω x L)) :
    Stage2 Ω {x | x ∈ E ∧ x ≠ 1 ∧ FrameMeetsAt Ω E S x} :=
  stage2_of_leviBlockImage hp2 hq hΩ hsingle
    (fun _ hy => localOddCentral_of_localLieSystems hnab hp2 h0 fundamentalWholeA1 hΩ hIH Fr h16
      hGen hlay hy.1 hy.2.1 hy.2.2) ⟨hxE, hx1, hmeet⟩ hL h

theorem stage2_final_of_localLeviComponent [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    {F : Type*} [Field F] {S : Set (Subgroup G)} (Fr : WeakToralFrame F Ω E S)
    (h16 : 16 ≤ Nat.card E) (hGen : FusionGenerated E)
    (hlay : ∀ a ∈ E, a ≠ 1 → LayerGenerationAt E a) {x : G} (hxE : x ∈ E) (hx1 : x ≠ 1)
    (hmeet : FrameMeetsAt Ω E S x) (h : LocalLeviComponent p f Ω x) :
    Stage2 Ω {x | x ∈ E ∧ x ≠ 1 ∧ FrameMeetsAt Ω E S x} := by
  obtain ⟨L, hL, hlevi⟩ := h.exists_member hp2 hq hΩ
  exact stage2_final_of_leviBlockImage hnab hp2 hq h0 hΩ hsingle hIH Fr h16 hGen hlay hxE hx1
    hmeet hL hlevi

theorem stage2_final_nine [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2)
    (hf : 0 < f) (h0 : ModelClauseZero) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    {F : Type*} [Field F] {S : Set (Subgroup G)} (Fr : WeakToralFrame F Ω E S)
    (h16 : 16 ≤ Nat.card E) (hGen : FusionGenerated E)
    (hlay : ∀ a ∈ E, a ≠ 1 → LayerGenerationAt E a)
    (hnine : p ^ f = 9 → ∃ x ∈ E, x ≠ 1 ∧ FrameMeetsAt Ω E S x ∧
      ∃ L ∈ centralizingMembers Ω {x}, LeviBlockImage p f (locImg Ω x L)) :
    Stage2 Ω {x | x ∈ E ∧ x ≠ 1 ∧ FrameMeetsAt Ω E S x} := by
  by_cases h9 : p ^ f = 9
  · obtain ⟨x, hxE, hx1, hmeet, L, hL, hlevi⟩ := hnine h9
    exact stage2_final_of_leviBlockImage hnab hp2 (by omega) h0 hΩ hsingle hIH Fr h16 hGen hlay
      hxE hx1 hmeet hL hlevi
  · exact stage2_final hnab hp2 hf h9 h0 hΩ hsingle hIH Fr h16 hGen hlay

theorem stage2_final_nine_of_localLeviComponent [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hf : 0 < f) (h0 : ModelClauseZero)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hIH : LocalLieSystems p f Ω) {F : Type*} [Field F] {S : Set (Subgroup G)}
    (Fr : WeakToralFrame F Ω E S) (h16 : 16 ≤ Nat.card E) (hGen : FusionGenerated E)
    (hlay : ∀ a ∈ E, a ≠ 1 → LayerGenerationAt E a)
    (hnine : p ^ f = 9 → ∃ x ∈ E, x ≠ 1 ∧ FrameMeetsAt Ω E S x ∧ LocalLeviComponent p f Ω x) :
    Stage2 Ω {x | x ∈ E ∧ x ≠ 1 ∧ FrameMeetsAt Ω E S x} := by
  refine stage2_final_nine hnab hp2 hf h0 hΩ hsingle hIH Fr h16 hGen hlay fun h9 => ?_
  obtain ⟨x, hxE, hx1, hmeet, hlevi⟩ := hnine h9
  obtain ⟨L, hL, hL'⟩ := hlevi.exists_member hp2 (by omega) hΩ
  exact ⟨x, hxE, hx1, hmeet, L, hL, hL'⟩

end Stage

end CFSG.ClassicalInvolution.Balance
