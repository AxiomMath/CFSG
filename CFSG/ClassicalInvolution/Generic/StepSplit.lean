module

public import CFSG.ClassicalInvolution.Generic.StepBasic
public import CFSG.ClassicalInvolution.Generic.StepMember
public import CFSG.ClassicalInvolution.Generic.InductionLocal

public section

namespace CFSG.ClassicalInvolution.Generic

open CFSG.Open CFSG.LieType CFSG.LieType.Universal CFSG.ClassicalInvolution

section Indexed

variable (p f : ℕ) [Fact p.Prime]

structure LieSystemDataOn (ι : Type) (X : Type) [Group X] (Φ : Set (Subgroup X)) where
  tag : ι → CFSG.Assembly.LowTwoRank.StatedLieTag
  rank : ι → ℕ
  exp : ι → ℕ
  hom : ∀ i, (modelUniv (tag i) (rank i) p (exp i) Fact.out).K →* X
  isFundTag : ∀ i, IsFundTag (tag i)
  admissible : ∀ i, CFSG.Assembly.LowTwoRank.StatedLieAdmissible (tag i) (rank i) p (exp i)
  exp_eq : ∀ i, exp i = f ∨ (tag i = .trialityD4 ∧ 3 * exp i = f)
  ker_le_center : ∀ i, (hom i).ker ≤ Subgroup.center _
  commute : ∀ i j, i ≠ j → ∀ x y, hom i x * hom j y = hom j y * hom i x
  generate : ⨆ i, (hom i).range = ⊤
  fundamental : ∀ L ∈ Φ, ∃ i,
    ∃ R ∈ fundamentalSubgroups (tag i) (modelUniv (tag i) (rank i) p (exp i) Fact.out).D,
      L = R.map (hom i)
  meets : ∀ i,
    ∃ R ∈ fundamentalSubgroups (tag i) (modelUniv (tag i) (rank i) p (exp i) Fact.out).D,
      R.map (hom i) ∈ Φ

variable {p f} {X : Type} [Group X] {Φ : Set (Subgroup X)}

def LieSystemData.toOn (D : LieSystemData p f X Φ) : LieSystemDataOn p f (Fin D.card) X Φ where
  tag := D.tag
  rank := D.rank
  exp := D.exp
  hom := D.hom
  isFundTag := D.isFundTag
  admissible := D.admissible
  exp_eq := D.exp_eq
  ker_le_center := D.ker_le_center
  commute := D.commute
  generate := D.generate
  fundamental := D.fundamental
  meets := D.meets

noncomputable def LieSystemDataOn.toData {ι : Type} [Finite ι] (D : LieSystemDataOn p f ι X Φ) :
    LieSystemData p f X Φ :=
  let e : Fin (Nat.card ι) ≃ ι := (Finite.equivFin ι).symm
  { card := Nat.card ι
    tag := fun i => D.tag (e i)
    rank := fun i => D.rank (e i)
    exp := fun i => D.exp (e i)
    hom := fun i => D.hom (e i)
    isFundTag := fun i => D.isFundTag (e i)
    admissible := fun i => D.admissible (e i)
    exp_eq := fun i => D.exp_eq (e i)
    ker_le_center := fun i => D.ker_le_center (e i)
    commute := fun i j h x y => D.commute (e i) (e j) (fun hij => h (e.injective hij)) x y
    generate := (Equiv.iSup_comp (g := fun k => (D.hom k).range) e).trans D.generate
    fundamental := by
      intro L hL
      obtain ⟨k, R, hR, hLR⟩ := D.fundamental L hL
      obtain ⟨i, rfl⟩ := e.surjective k
      exact ⟨i, R, hR, hLR⟩
    meets := fun i => D.meets (e i) }

variable {Y : Type} [Group Y]

noncomputable def LieSystemDataOn.sum (Y₁ Y₂ : Subgroup Y) (hc : Commutes Y₁ Y₂)
    (hgen : Y₁ ⊔ Y₂ = ⊤) {ι₁ ι₂ : Type} {Φ₁ : Set (Subgroup Y₁)} {Φ₂ : Set (Subgroup Y₂)}
    {Φ : Set (Subgroup Y)} (D₁ : LieSystemDataOn p f ι₁ Y₁ Φ₁)
    (D₂ : LieSystemDataOn p f ι₂ Y₂ Φ₂)
    (hΦ : ∀ L ∈ Φ, (∃ L' ∈ Φ₁, L = L'.map Y₁.subtype) ∨ (∃ L' ∈ Φ₂, L = L'.map Y₂.subtype))
    (hΦ₁ : ∀ L' ∈ Φ₁, L'.map Y₁.subtype ∈ Φ) (hΦ₂ : ∀ L' ∈ Φ₂, L'.map Y₂.subtype ∈ Φ) :
    LieSystemDataOn p f (ι₁ ⊕ ι₂) Y Φ where
  tag := Sum.elim D₁.tag D₂.tag
  rank := Sum.elim D₁.rank D₂.rank
  exp := Sum.elim D₁.exp D₂.exp
  hom := fun i => match i with
    | Sum.inl j => Y₁.subtype.comp (D₁.hom j)
    | Sum.inr j => Y₂.subtype.comp (D₂.hom j)
  isFundTag := fun i => match i with
    | Sum.inl j => D₁.isFundTag j
    | Sum.inr j => D₂.isFundTag j
  admissible := fun i => match i with
    | Sum.inl j => D₁.admissible j
    | Sum.inr j => D₂.admissible j
  exp_eq := fun i => match i with
    | Sum.inl j => D₁.exp_eq j
    | Sum.inr j => D₂.exp_eq j
  ker_le_center := by
    rintro (j | j) x hx
    · have h : D₁.hom j x = 1 := Subtype.ext hx
      exact D₁.ker_le_center j h
    · have h : D₂.hom j x = 1 := Subtype.ext hx
      exact D₂.ker_le_center j h
  commute := by
    rintro (i | i) (j | j) hij x y
    · have hne : i ≠ j := fun h => hij (congrArg Sum.inl h)
      exact congrArg Subtype.val (D₁.commute i j hne x y)
    · exact hc _ (D₁.hom i x).2 _ (D₂.hom j y).2
    · exact (hc _ (D₁.hom j y).2 _ (D₂.hom i x).2).symm
    · have hne : i ≠ j := fun h => hij (congrArg Sum.inr h)
      exact congrArg Subtype.val (D₂.commute i j hne x y)
  generate := by
    rw [eq_top_iff, ← hgen]
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · have hx' : (⟨x, hx⟩ : Y₁) ∈ (⊤ : Subgroup Y₁) := trivial
      rw [← D₁.generate] at hx'
      have hx'' := Subgroup.mem_map_of_mem Y₁.subtype hx'
      rw [Subgroup.map_iSup] at hx''
      refine (iSup_le (fun j => ?_) : (⨆ j, (D₁.hom j).range.map Y₁.subtype) ≤ _) hx''
      rw [← MonoidHom.range_comp]
      exact le_iSup_of_le (Sum.inl j) le_rfl
    · have hx' : (⟨x, hx⟩ : Y₂) ∈ (⊤ : Subgroup Y₂) := trivial
      rw [← D₂.generate] at hx'
      have hx'' := Subgroup.mem_map_of_mem Y₂.subtype hx'
      rw [Subgroup.map_iSup] at hx''
      refine (iSup_le (fun j => ?_) : (⨆ j, (D₂.hom j).range.map Y₂.subtype) ≤ _) hx''
      rw [← MonoidHom.range_comp]
      exact le_iSup_of_le (Sum.inr j) le_rfl
  fundamental := by
    intro L hL
    rcases hΦ L hL with ⟨L', hL', rfl⟩ | ⟨L', hL', rfl⟩
    · obtain ⟨j, R, hR, rfl⟩ := D₁.fundamental L' hL'
      exact ⟨Sum.inl j, R, hR, Subgroup.map_map _ _ _⟩
    · obtain ⟨j, R, hR, rfl⟩ := D₂.fundamental L' hL'
      exact ⟨Sum.inr j, R, hR, Subgroup.map_map _ _ _⟩
  meets := by
    rintro (j | j)
    · obtain ⟨R, hR, hmem⟩ := D₁.meets j
      refine ⟨R, hR, ?_⟩
      have := hΦ₁ _ hmem
      rwa [Subgroup.map_map] at this
    · obtain ⟨R, hR, hmem⟩ := D₂.meets j
      refine ⟨R, hR, ?_⟩
      have := hΦ₂ _ hmem
      rwa [Subgroup.map_map] at this

end Indexed

section Generated

variable {Y : Type} [Group Y]

theorem commutes_iff_le_centralizer {K L : Subgroup Y} :
    Commutes K L ↔ K ≤ Subgroup.centralizer (L : Set Y) := by
  constructor
  · intro h x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (h x hx y hy).symm
  · intro h x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (h hx) y hy).symm

theorem commutes_biSup {Λ₁ Λ₂ : Set (Subgroup Y)} (h : ∀ L ∈ Λ₁, ∀ M ∈ Λ₂, Commutes L M) :
    Commutes (⨆ L ∈ Λ₁, L) (⨆ M ∈ Λ₂, M) := by
  rw [commutes_iff_le_centralizer]
  refine iSup₂_le fun L hL => ?_
  rw [← commutes_iff_le_centralizer]
  refine Commutes.symm ?_
  rw [commutes_iff_le_centralizer]
  exact iSup₂_le fun M hM => commutes_iff_le_centralizer.mp (h L hL M hM).symm

theorem normal_biSup {Λ₁ : Set (Subgroup Y)} (h : ConjInvariant Λ₁) : (⨆ L ∈ Λ₁, L).Normal := by
  have key : ∀ g : Y, (⨆ L ∈ Λ₁, L).map (MulAut.conj g).toMonoidHom ≤ ⨆ L ∈ Λ₁, L := by
    intro g
    rw [Subgroup.map_iSup]
    refine iSup_le fun L => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hL => ?_
    exact le_iSup₂_of_le (conjSub g L) (h g L hL) le_rfl
  exact ⟨fun n hn g => key g ⟨n, hn, rfl⟩⟩

end Generated

section Split

variable {Y : Type} [Group Y]

theorem exists_split {Λ : Set (Subgroup Y)} (hne : Λ.Nonempty) (hinv : ConjInvariant Λ)
    (hgen : ⨆ L ∈ Λ, L = ⊤) (hnc : ¬ NonCommConnected Λ) :
    ∃ Λ₁ Λ₂ : Set (Subgroup Y), Λ₁ ∪ Λ₂ = Λ ∧ Λ₁.Nonempty ∧ Λ₂.Nonempty ∧
      ConjInvariant Λ₁ ∧ ConjInvariant Λ₂ ∧ ∀ L ∈ Λ₁, ∀ M ∈ Λ₂, Commutes L M := by
  have hpre : ¬ (nonCommGraph Λ).Preconnected := fun h => by
    have : Nonempty ↥Λ := hne.to_subtype
    exact hnc ⟨h⟩
  simp only [SimpleGraph.Preconnected, not_forall] at hpre
  obtain ⟨u, v, huv⟩ := hpre
  let R : Set (Subgroup Y) := {M | ∃ h : M ∈ Λ, (nonCommGraph Λ).Reachable u ⟨M, h⟩}
  have hRΛ : R ⊆ Λ := fun M hM => hM.1
  have hstep : ∀ L M : Subgroup Y, L ∈ R → M ∈ Λ → L ≠ M → ¬ Commutes L M → M ∈ R := by
    rintro L M ⟨hL, hLreach⟩ hM hLM hnc'
    refine ⟨hM, hLreach.trans ?_⟩
    exact (nonCommGraph_adj (S := Λ) (K := ⟨L, hL⟩) (L := ⟨M, hM⟩)).mpr
      ⟨fun h => hLM (congrArg Subtype.val h), hnc'⟩ |>.reachable
  have hgenL : ∀ L ∈ Λ, ∀ g ∈ L, ∀ M ∈ R, conjSub g M ∈ R := by
    intro L hL g hg M hM
    have hMΛ : M ∈ Λ := hRΛ hM
    have hMg : conjSub g M ∈ Λ := hinv g M hMΛ
    by_cases hcomm : Commutes L M
    · rw [conjSub_eq_of_mem_of_commutes hg hcomm]
      exact hM
    · have hLR : L ∈ R := by
        by_cases hLM : L = M
        · rw [hLM]; exact hM
        · exact hstep M L hM hL (Ne.symm hLM) fun h => hcomm h.symm
      by_cases hN : conjSub g M = L
      · rw [hN]; exact hLR
      · refine hstep L _ hLR hMg (Ne.symm hN) ?_
        intro h
        apply hcomm
        have h' : Commutes (conjSub g L) (conjSub g M) := by
          rwa [conjSub_eq_self_of_mem hg]
        exact (commutes_conjSub_iff g).mp h'
  have hR : ConjInvariant R := by
    let S : Subgroup Y :=
      { carrier := {g | (∀ M ∈ R, conjSub g M ∈ R) ∧ (∀ M ∈ R, conjSub g⁻¹ M ∈ R)}
        mul_mem' := by
          rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
          refine ⟨fun M hM => ?_, fun M hM => ?_⟩
          · rw [conjSub_mul]; exact ha _ (hb M hM)
          · rw [mul_inv_rev, conjSub_mul]; exact hb' _ (ha' M hM)
        one_mem' := ⟨fun M hM => by rwa [conjSub_one], fun M hM => by rwa [inv_one, conjSub_one]⟩
        inv_mem' := by
          rintro a ⟨ha, ha'⟩
          exact ⟨by simpa using ha', by simpa using ha⟩ }
    have hS : ∀ L ∈ Λ, L ≤ S := fun L hL g hg =>
      ⟨fun M hM => hgenL L hL g hg M hM, fun M hM => hgenL L hL g⁻¹ (L.inv_mem hg) M hM⟩
    have hSΛ : (⨆ L ∈ Λ, L) ≤ S := iSup₂_le hS
    rw [hgen] at hSΛ
    intro g M hM
    exact (hSΛ (Subgroup.mem_top g)).1 M hM
  refine ⟨R, Λ \ R, ?_, ⟨u.1, u.2, SimpleGraph.Reachable.refl u⟩, ⟨v.1, v.2, fun h => huv ?_⟩, hR, ?_, ?_⟩
  · ext M
    constructor
    · rintro (hM | hM)
      · exact hRΛ hM
      · exact hM.1
    · intro hM
      by_cases hMR : M ∈ R
      · exact Or.inl hMR
      · exact Or.inr ⟨hM, hMR⟩
  · obtain ⟨_, hr⟩ := h
    exact hr
  · rintro g M ⟨hMΛ, hMR⟩
    refine ⟨hinv g M hMΛ, fun h => hMR ?_⟩
    have := hR g⁻¹ _ h
    rwa [conjSub_inv_conjSub] at this
  · rintro L hL M ⟨hMΛ, hMR⟩
    by_contra hnc'
    exact hMR (hstep L M hL hMΛ (fun h => hMR (h ▸ hL)) hnc')

end Split

section Parts

variable (p f : ℕ) [Fact p.Prime] {Y : Type} [Group Y]

variable {p f}

theorem inClass_of_le {Λ : Set (Subgroup Y)} (hΛ : InClass p f Λ) {H : Subgroup Y}
    {Λ₁ : Set (Subgroup Y)} (hsub : Λ₁ ⊆ Λ) (hle : ∀ L ∈ Λ₁, L ≤ H) (hne : Λ₁.Nonempty)
    (hinv : ∀ h : H, ∀ L ∈ Λ₁, conjSub (h : Y) L ∈ Λ₁) (hgen : (⨆ L ∈ Λ₁, L) = H) :
    InClass p f {L' : Subgroup H | ∃ L ∈ Λ₁, L' = L.subgroupOf H} where
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
    exact ⟨_, hz.subgroupOf p f (hle L hL)⟩

variable [Finite Y]

theorem lieSystem_of_part (hBelow : CITBelowU p f (Nat.card Y))
    (hO : classicalInvolutionOddCore Y = ⊥) {Λ : Set (Subgroup Y)} (hΛ : InClass p f Λ)
    {Λ₁ : Set (Subgroup Y)} (hsub : Λ₁ ⊆ Λ) (hne : Λ₁.Nonempty) (hinv : ConjInvariant Λ₁)
    (hlt : (⨆ L ∈ Λ₁, L) ≠ ⊤) :
    LieSystem p f ↥(⨆ L ∈ Λ₁, L)
      {L' : Subgroup ↥(⨆ L ∈ Λ₁, L) | ∃ L ∈ Λ₁, L' = L.subgroupOf (⨆ L ∈ Λ₁, L)} := by
  set H : Subgroup Y := ⨆ L ∈ Λ₁, L with hH
  have hnormal : H.Normal := normal_biSup hinv
  have hclass : InClass p f {L' : Subgroup H | ∃ L ∈ Λ₁, L' = L.subgroupOf H} :=
    inClass_of_le hΛ hsub (fun L hL => le_iSup₂_of_le L hL le_rfl) hne
      (fun h L hL => hinv _ L hL) hH.symm
  have hmod := hBelow H (card_lt_of_ne_top hlt) _ hclass
  have hsubnormal : IsSubnormal H ⊤ :=
    IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤)
  exact lieSystem_of_lieSystemMod_corefree
    (CFSG.ComponentClassification.OddCore.subnormal_corefree hO H hsubnormal) hmod

theorem lieSystem_of_not_connected (hBelow : CITBelowU p f (Nat.card Y))
    (hO : classicalInvolutionOddCore Y = ⊥) {Λ : Set (Subgroup Y)} (hΛ : InClass p f Λ)
    (hnc : ¬ NonCommConnected Λ) : LieSystem p f Y Λ := by
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
  obtain ⟨D₁⟩ := lieSystem_of_part hBelow hO hΛ hsub₁ hne₁ hinv₁ hlt₁
  obtain ⟨D₂⟩ := lieSystem_of_part hBelow hO hΛ hsub₂ hne₂ hinv₂ hlt₂
  refine ⟨(LieSystemDataOn.sum Y₁ Y₂ hc hgen D₁.toOn D₂.toOn ?_ ?_ ?_).toData⟩
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

end CFSG.ClassicalInvolution.Generic
