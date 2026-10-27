module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7StepOdd
public import CFSG.ClassicalInvolution.Generic.StepSplit

public section

namespace CFSG.ClassicalInvolution.Hat2A7

open CFSG.Open CFSG.ClassicalInvolution.Generic

section Indexed

structure A7SystemDataOn (ι : Type) (X : Type) [Group X] (Φ : Set (Subgroup X)) where
  comp : ι → Subgroup X
  perfect : ∀ i, Group.IsPerfect ↥(comp i)
  witness : ∀ i, A7Witness (comp i)
  commute : ∀ i j, i ≠ j → ∀ a ∈ comp i, ∀ b ∈ comp j, a * b = b * a
  generate : ⨆ i, comp i = ⊤
  members : Φ = Set.range comp

variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

def A7SystemData.toOn (D : A7SystemData X Φ) : A7SystemDataOn (Fin D.card) X Φ where
  comp := D.comp
  perfect := D.perfect
  witness := D.witness
  commute := D.commute
  generate := D.generate
  members := D.members

noncomputable def A7SystemDataOn.toData {ι : Type} [Finite ι] (D : A7SystemDataOn ι X Φ) :
    A7SystemData X Φ :=
  let e : Fin (Nat.card ι) ≃ ι := (Finite.equivFin ι).symm
  { card := Nat.card ι
    comp := fun i => D.comp (e i)
    perfect := fun i => D.perfect (e i)
    witness := fun i => D.witness (e i)
    commute := fun i j h a ha b hb =>
      D.commute (e i) (e j) (fun hij => h (e.injective hij)) a ha b hb
    generate := (Equiv.iSup_comp (g := fun k => D.comp k) e).trans D.generate
    members := D.members.trans (e.surjective.range_comp D.comp).symm }

variable {Y : Type} [Group Y]

noncomputable def A7SystemDataOn.sum (Y₁ Y₂ : Subgroup Y) (hc : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a)
    (hgen : Y₁ ⊔ Y₂ = ⊤) {ι₁ ι₂ : Type} {Φ₁ : Set (Subgroup Y₁)} {Φ₂ : Set (Subgroup Y₂)}
    {Φ : Set (Subgroup Y)} (D₁ : A7SystemDataOn ι₁ Y₁ Φ₁) (D₂ : A7SystemDataOn ι₂ Y₂ Φ₂)
    (hΦ : Φ = (fun L' => L'.map Y₁.subtype) '' Φ₁ ∪ (fun L' => L'.map Y₂.subtype) '' Φ₂) :
    A7SystemDataOn (ι₁ ⊕ ι₂) Y Φ where
  comp := Sum.elim (fun j => (D₁.comp j).map Y₁.subtype) (fun j => (D₂.comp j).map Y₂.subtype)
  perfect := by
    rintro (i | i)
    · have := D₁.perfect i
      exact Group.IsPerfect.ofSurjective
        (f := ((D₁.comp i).equivMapOfInjective Y₁.subtype Y₁.subtype_injective).toMonoidHom)
        (MulEquiv.surjective _)
    · have := D₂.perfect i
      exact Group.IsPerfect.ofSurjective
        (f := ((D₂.comp i).equivMapOfInjective Y₂.subtype Y₂.subtype_injective).toMonoidHom)
        (MulEquiv.surjective _)
  witness := by
    rintro (i | i)
    · exact A7Witness.of_mulEquiv ((D₁.comp i).equivMapOfInjective Y₁.subtype
        Y₁.subtype_injective) (D₁.witness i)
    · exact A7Witness.of_mulEquiv ((D₂.comp i).equivMapOfInjective Y₂.subtype
        Y₂.subtype_injective) (D₂.witness i)
  commute := by
    rintro (i | i) (j | j) hij a ha b hb
    · obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      have hne : i ≠ j := fun h => hij (congrArg Sum.inl h)
      exact congrArg Subtype.val (D₁.commute i j hne a' ha' b' hb')
    · obtain ⟨a', -, rfl⟩ := ha
      obtain ⟨b', -, rfl⟩ := hb
      exact hc _ a'.2 _ b'.2
    · obtain ⟨a', -, rfl⟩ := ha
      obtain ⟨b', -, rfl⟩ := hb
      exact (hc _ b'.2 _ a'.2).symm
    · obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      have hne : i ≠ j := fun h => hij (congrArg Sum.inr h)
      exact congrArg Subtype.val (D₂.commute i j hne a' ha' b' hb')
  generate := by
    rw [eq_top_iff, ← hgen]
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · have hx' : (⟨x, hx⟩ : Y₁) ∈ (⊤ : Subgroup Y₁) := trivial
      rw [← D₁.generate] at hx'
      have hx'' := Subgroup.mem_map_of_mem Y₁.subtype hx'
      rw [Subgroup.map_iSup] at hx''
      refine (iSup_le (fun j => ?_) : (⨆ j, (D₁.comp j).map Y₁.subtype) ≤ _) hx''
      exact le_iSup_of_le (Sum.inl j) le_rfl
    · have hx' : (⟨x, hx⟩ : Y₂) ∈ (⊤ : Subgroup Y₂) := trivial
      rw [← D₂.generate] at hx'
      have hx'' := Subgroup.mem_map_of_mem Y₂.subtype hx'
      rw [Subgroup.map_iSup] at hx''
      refine (iSup_le (fun j => ?_) : (⨆ j, (D₂.comp j).map Y₂.subtype) ≤ _) hx''
      exact le_iSup_of_le (Sum.inr j) le_rfl
  members := by
    have h1 : ∀ L', L' ∈ Φ₁ ↔ ∃ i, D₁.comp i = L' := fun L' => Set.ext_iff.mp D₁.members L'
    have h2 : ∀ L', L' ∈ Φ₂ ↔ ∃ i, D₂.comp i = L' := fun L' => Set.ext_iff.mp D₂.members L'
    rw [hΦ]
    ext L
    constructor
    · rintro (⟨L', hL', rfl⟩ | ⟨L', hL', rfl⟩)
      · obtain ⟨i, rfl⟩ := (h1 L').mp hL'
        exact ⟨Sum.inl i, rfl⟩
      · obtain ⟨i, rfl⟩ := (h2 L').mp hL'
        exact ⟨Sum.inr i, rfl⟩
    · rintro ⟨i | i, rfl⟩
      · exact Or.inl ⟨D₁.comp i, (h1 _).mpr ⟨i, rfl⟩, rfl⟩
      · exact Or.inr ⟨D₂.comp i, (h2 _).mpr ⟨i, rfl⟩, rfl⟩

end Indexed

section Parts

variable {Y : Type} [Group Y]

theorem inClass2A7_of_le {Λ : Set (Subgroup Y)} (hΛ : InClass2A7 Λ) {H : Subgroup Y}
    {Λ₁ : Set (Subgroup Y)} (hsub : Λ₁ ⊆ Λ) (hle : ∀ L ∈ Λ₁, L ≤ H) (hne : Λ₁.Nonempty)
    (hinv : ∀ h : H, ∀ L ∈ Λ₁, conjSub (h : Y) L ∈ Λ₁) (hgen : (⨆ L ∈ Λ₁, L) = H) :
    InClass2A7 {L' : Subgroup H | ∃ L ∈ Λ₁, L' = L.subgroupOf H} where
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
    exact ⟨_, hz.subgroupOf (hle L hL) le_top⟩

variable [Finite Y]

theorem a7System_of_part (hBelow : CITBelow2A7 (Nat.card Y))
    (hO : classicalInvolutionOddCore Y = ⊥) {Λ : Set (Subgroup Y)} (hΛ : InClass2A7 Λ)
    {Λ₁ : Set (Subgroup Y)} (hsub : Λ₁ ⊆ Λ) (hne : Λ₁.Nonempty) (hinv : ConjInvariant Λ₁)
    (hlt : (⨆ L ∈ Λ₁, L) ≠ ⊤) :
    A7System ↥(⨆ L ∈ Λ₁, L)
      {L' : Subgroup ↥(⨆ L ∈ Λ₁, L) | ∃ L ∈ Λ₁, L' = L.subgroupOf (⨆ L ∈ Λ₁, L)} := by
  set H : Subgroup Y := ⨆ L ∈ Λ₁, L with hH
  have hnormal : H.Normal := normal_biSup hinv
  have hclass : InClass2A7 {L' : Subgroup H | ∃ L ∈ Λ₁, L' = L.subgroupOf H} :=
    inClass2A7_of_le hΛ hsub (fun L hL => le_iSup₂_of_le L hL le_rfl) hne
      (fun h L hL => hinv _ L hL) hH.symm
  have hmod := hBelow H (card_lt_of_ne_top' hlt) _ hclass
  have hsubnormal : IsSubnormal H ⊤ :=
    IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤)
  exact a7System_of_a7SystemMod_corefree
    (CFSG.ComponentClassification.OddCore.subnormal_corefree hO H hsubnormal) hmod

theorem a7System_of_not_connected (hBelow : CITBelow2A7 (Nat.card Y))
    (hO : classicalInvolutionOddCore Y = ⊥) {Λ : Set (Subgroup Y)} (hΛ : InClass2A7 Λ)
    (hnc : ¬ NonCommConnected Λ) : A7System Y Λ := by
  obtain ⟨Λ₁, Λ₂, hU, hne₁, hne₂, hinv₁, hinv₂, hcomm⟩ :=
    exists_split hΛ.nonempty hΛ.conjInvariant.toConjInvariant hΛ.generated hnc
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
  obtain ⟨D₁⟩ := a7System_of_part hBelow hO hΛ hsub₁ hne₁ hinv₁ hlt₁
  obtain ⟨D₂⟩ := a7System_of_part hBelow hO hΛ hsub₂ hne₂ hinv₂ hlt₂
  refine ⟨(A7SystemDataOn.sum Y₁ Y₂ hc hgen D₁.toOn D₂.toOn ?_).toData⟩
  rw [← hU]
  ext L
  simp only [Set.mem_union, Set.mem_image]
  constructor
  · rintro (hL | hL)
    · left
      refine ⟨L.subgroupOf Y₁, ⟨L, hL, rfl⟩, ?_⟩
      rw [Subgroup.map_subgroupOf_eq_of_le (le_iSup₂_of_le L hL le_rfl)]
    · right
      refine ⟨L.subgroupOf Y₂, ⟨L, hL, rfl⟩, ?_⟩
      rw [Subgroup.map_subgroupOf_eq_of_le (le_iSup₂_of_le L hL le_rfl)]
  · rintro (⟨_, ⟨L', hL', rfl⟩, rfl⟩ | ⟨_, ⟨L', hL', rfl⟩, rfl⟩)
    · left
      rw [Subgroup.map_subgroupOf_eq_of_le (le_iSup₂_of_le L' hL' le_rfl)]
      exact hL'
    · right
      rw [Subgroup.map_subgroupOf_eq_of_le (le_iSup₂_of_le L' hL' le_rfl)]
      exact hL'

end Parts

end CFSG.ClassicalInvolution.Hat2A7
