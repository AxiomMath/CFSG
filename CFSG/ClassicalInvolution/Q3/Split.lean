module

public import CFSG.ClassicalInvolution.Q3.Induction
public import CFSG.ClassicalInvolution.Generic.StepSplit

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

section Corefree

variable {Y : Type} [Group Y]

theorem lieSystemMod3_of_lieSystem3_corefree (hO : classicalInvolutionOddCore Y = ⊥)
    {Λ : Set (Subgroup Y)} (h : LieSystem3 Y Λ) : LieSystemMod3 Λ :=
  LieSystem3.congr (oddQuotientEquivOfCorefree hO) h

theorem lieSystem3_of_lieSystemMod3_corefree (hO : classicalInvolutionOddCore Y = ⊥)
    {Λ : Set (Subgroup Y)} (h : LieSystemMod3 Λ) : LieSystem3 Y Λ := by
  have hid : (oddQuotientEquivOfCorefree hO).symm.toMonoidHom.comp
      (QuotientGroup.mk' (classicalInvolutionOddCore Y)) = MonoidHom.id Y := by
    ext x
    exact (oddQuotientEquivOfCorefree hO).symm_apply_apply x
  have key : Subgroup.map (oddQuotientEquivOfCorefree hO).symm.toMonoidHom ''
      oddQuotientFamily Λ = Λ := by
    ext L
    constructor
    · rintro ⟨_, ⟨L', hL', rfl⟩, rfl⟩
      rw [Subgroup.map_map, hid, Subgroup.map_id]
      exact hL'
    · intro hL
      refine ⟨L.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)), ⟨L, hL, rfl⟩, ?_⟩
      rw [Subgroup.map_map, hid, Subgroup.map_id]
  have := LieSystem3.congr (oddQuotientEquivOfCorefree hO).symm h
  rwa [key] at this

end Corefree

section Parts

variable {Y : Type} [Group Y]

theorem inClass3_of_le {Λ : Set (Subgroup Y)} (hΛ : InClass3 Λ) {H : Subgroup Y}
    {Λ₁ : Set (Subgroup Y)} (hsub : Λ₁ ⊆ Λ) (hle : ∀ L ∈ Λ₁, L ≤ H) (hne : Λ₁.Nonempty)
    (hinv : ∀ h : H, ∀ L ∈ Λ₁, conjSub (h : Y) L ∈ Λ₁) (hgen : (⨆ L ∈ Λ₁, L) = H) :
    InClass3 {L' : Subgroup H | ∃ L ∈ Λ₁, L' = L.subgroupOf H} where
  nonempty := by
    obtain ⟨L, hL⟩ := hne
    exact ⟨L.subgroupOf H, L, hL, rfl⟩
  conjInvariant := by
    rintro n _ ⟨L, hL, rfl⟩
    exact ⟨conjSub (n : Y) L, hinv n L hL, conjSub_subgroupOf H n L⟩
  generated := by
    have key := iSup_subgroupOf_self (G := Y) (fun i : Λ₁ => (i : Subgroup Y))
    have hsup : (⨆ i : Λ₁, (i : Subgroup Y)) = H := by rw [← hgen, iSup_subtype']
    rw [hsup] at key
    refine eq_top_iff.mpr (key.symm.le.trans ?_)
    refine iSup_le fun i => ?_
    exact le_iSup₂ (f := fun (L' : Subgroup H)
      (_ : L' ∈ {L' : Subgroup H | ∃ L ∈ Λ₁, L' = L.subgroupOf H}) => L')
      ((i : Subgroup Y).subgroupOf H) ⟨i, i.2, rfl⟩
  classical := by
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨z, hz⟩ := hΛ.classical L (hsub hL)
    exact ⟨_, hz.subgroupOf (hle L hL)⟩

variable [Finite Y]

theorem lieSystem3_of_part (hBelow : CIT3Below (Nat.card Y))
    (hO : classicalInvolutionOddCore Y = ⊥) {Λ : Set (Subgroup Y)} (hΛ : InClass3 Λ)
    {Λ₁ : Set (Subgroup Y)} (hsub : Λ₁ ⊆ Λ) (hne : Λ₁.Nonempty) (hinv : ConjInvariant Λ₁)
    (hlt : (⨆ L ∈ Λ₁, L) ≠ ⊤) :
    LieSystem3 ↥(⨆ L ∈ Λ₁, L)
      {L' : Subgroup ↥(⨆ L ∈ Λ₁, L) | ∃ L ∈ Λ₁, L' = L.subgroupOf (⨆ L ∈ Λ₁, L)} := by
  set H : Subgroup Y := ⨆ L ∈ Λ₁, L with hH
  have hnormal : H.Normal := normal_biSup hinv
  have hclass : InClass3 {L' : Subgroup H | ∃ L ∈ Λ₁, L' = L.subgroupOf H} :=
    inClass3_of_le hΛ hsub (fun L hL => le_iSup₂_of_le L hL le_rfl) hne
      (fun h L hL => hinv _ L hL) hH.symm
  have hmod := hBelow H (card_lt_of_ne_top hlt) _ hclass
  have hsubnormal : IsSubnormal H ⊤ :=
    IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤)
  exact lieSystem3_of_lieSystemMod3_corefree
    (CFSG.ComponentClassification.OddCore.subnormal_corefree hO H hsubnormal) hmod

theorem lieSystem3_of_not_connected (hBelow : CIT3Below (Nat.card Y))
    (hO : classicalInvolutionOddCore Y = ⊥) {Λ : Set (Subgroup Y)} (hΛ : InClass3 Λ)
    (hnc : ¬ NonCommConnected Λ) : LieSystem3 Y Λ := by
  obtain ⟨Λ₁, Λ₂, hU, hne₁, hne₂, hinv₁, hinv₂, hcomm⟩ :=
    exists_split hΛ.nonempty hΛ.conjInvariant hΛ.generated hnc
  have hsub₁ : Λ₁ ⊆ Λ := hU ▸ Set.subset_union_left
  have hsub₂ : Λ₂ ⊆ Λ := hU ▸ Set.subset_union_right
  set Y₁ : Subgroup Y := ⨆ L ∈ Λ₁, L with hY₁
  set Y₂ : Subgroup Y := ⨆ L ∈ Λ₂, L with hY₂
  have hgen : Y₁ ⊔ Y₂ = ⊤ := by
    have := hΛ.generated
    rw [← hU, iSup_union] at this
    exact this
  have hc : Commutes Y₁ Y₂ := commutes_biSup hcomm
  have hne_top : ∀ {Λ' Λ'' : Set (Subgroup Y)}, Λ' ⊆ Λ → Λ'' ⊆ Λ → Λ''.Nonempty →
      (∀ L ∈ Λ', ∀ M ∈ Λ'', Commutes L M) → (⨆ L ∈ Λ', L) ≠ ⊤ := by
    intro Λ' Λ'' h' h'' hne hc' htop
    obtain ⟨M, hM⟩ := hne
    obtain ⟨z, hz⟩ := hΛ.classical M (h'' hM)
    refine hz.not_le_center ?_
    have h1 : (⨆ L ∈ Λ', L) ≤ Subgroup.centralizer (M : Set Y) :=
      iSup₂_le fun L hL => commutes_iff_le_centralizer.mp (hc' L hL M hM)
    rw [htop, top_le_iff, Subgroup.centralizer_eq_top_iff_subset] at h1
    exact h1
  have hlt₁ : Y₁ ≠ ⊤ := hne_top hsub₁ hsub₂ hne₂ hcomm
  have hlt₂ : Y₂ ≠ ⊤ :=
    hne_top hsub₂ hsub₁ hne₁ fun L hL M hM => (hcomm M hM L hL).symm
  obtain ⟨ι₁, hι₁, ⟨D₁⟩⟩ := lieSystem3_of_part hBelow hO hΛ hsub₁ hne₁ hinv₁ hlt₁
  obtain ⟨ι₂, hι₂, ⟨D₂⟩⟩ := lieSystem3_of_part hBelow hO hΛ hsub₂ hne₂ hinv₂ hlt₂
  refine ⟨ι₁ ⊕ ι₂, inferInstance, ⟨LieSystemData3.sum Y₁ Y₂ hc hgen D₁ D₂ ?_ ?_ ?_⟩⟩
  · intro L hL
    rw [← hU] at hL
    rcases hL with hL | hL
    · left
      refine ⟨L.subgroupOf Y₁, ⟨L, hL, rfl⟩, ?_⟩
      rw [Subgroup.map_subgroupOf_eq_of_le (le_iSup₂_of_le L hL le_rfl)]
    · right
      refine ⟨L.subgroupOf Y₂, ⟨L, hL, rfl⟩, ?_⟩
      rw [Subgroup.map_subgroupOf_eq_of_le (le_iSup₂_of_le L hL le_rfl)]
  · rintro _ ⟨L, hL, rfl⟩
    rw [Subgroup.map_subgroupOf_eq_of_le (le_iSup₂_of_le L hL le_rfl)]
    exact hsub₁ hL
  · rintro _ ⟨L, hL, rfl⟩
    rw [Subgroup.map_subgroupOf_eq_of_le (le_iSup₂_of_le L hL le_rfl)]
    exact hsub₂ hL

end Parts

theorem lieSystemMod3_of_oddQuotient {Y : Type} [Group Y] [Finite Y]
    (hBelow : CIT3Below (Nat.card Y)) (hO : classicalInvolutionOddCore Y ≠ ⊥)
    {Λ : Set (Subgroup Y)} (hΛ : InClass3 Λ) : LieSystemMod3 Λ := by
  have hlt : Nat.card (Y ⧸ classicalInvolutionOddCore Y) < Nat.card Y := by
    have hmul := (classicalInvolutionOddCore Y).card_eq_card_quotient_mul_card_subgroup
    have h1 : 1 < Nat.card (classicalInvolutionOddCore Y) :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr hO
    have h2 : 0 < Nat.card (Y ⧸ classicalInvolutionOddCore Y) := Nat.card_pos
    nlinarith
  have hmod := hBelow _ hlt (oddQuotientFamily Λ) (inClass3_oddQuotient hΛ)
  exact lieSystem3_of_lieSystemMod3_corefree
    (CFSG.ComponentClassification.OddCore.quotient_corefree Y) hmod

end CFSG.ClassicalInvolution.Q3
