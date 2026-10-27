module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516Leaf
public import CFSG.Milestones.CT_catalog_nonabelian_type_partition

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

@[expose] def CF516LeafAt (S : Type) [Group S] [Finite S] : Prop :=
  IsSimpleGroup S → (∃ x y : S, x * y ≠ y * x) → SectionRank.IsKGroupCat S →
    ∀ (σ : MulAut S) (P : Subgroup S), ProperFixedComponent σ P →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    ((p ^ f % 4 = 3 ∧ Blueprint.LieModel (P ⧸ pPrimeCore 2 P) .PSL 4 p f) ∨
      (p ^ f % 4 = 1 ∧ Blueprint.LieModel (P ⧸ pPrimeCore 2 P) .PSU 4 p f)) →
    ∀ t ∈ P, orderOf t = 2 →
    ∀ J : Subgroup S, J ≤ centralizer ({t} : Set S) →
      IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set S))) →
      Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p (2 * f) →
      (∀ j ∈ J, σ j ∈ J) → (∀ j ∈ J, j⁻¹ * σ j ∈ oddCoreIn J) →
    ∀ JB : Subgroup S, JB ≤ J ⊓ P → ⁅JB, JB⁆ = JB → J ≤ JB ⊔ oddCoreIn J → False

@[expose] def CF516EvenRow : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Blueprint.EvenLieType S → CF516LeafAt S

@[expose] def CF516OddRow (T : StatedLieTag → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (τ : StatedLieTag) (n r e : ℕ), r.Prime → r ≠ 2 → T τ →
    StatedLieAdmissible τ n r e → Blueprint.LieModel S τ n r e → CF516LeafAt S

@[expose] def CF516LinRow : Prop := CF516OddRow fun τ => τ = .PSL ∨ τ = .PSU

@[expose] def CF516SpRow : Prop := CF516OddRow fun τ => τ = .PSp

@[expose] def CF516OrthRow : Prop :=
  CF516OddRow fun τ => τ = .POmegaOdd ∨ τ = .POmegaPlus ∨ τ = .POmegaMinus

@[expose] def CF516ExcRow : Prop :=
  CF516OddRow fun τ => τ ∈ Blueprint.chevalleyExceptionalTags ∨ τ = .twistedG2

@[expose] def CF516AltRow : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (n : ℕ), 5 ≤ n →
    Nonempty (S ≃* alternatingGroup (Fin n)) → CF516LeafAt S

@[expose] def CF516SporRow : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (s : TauCeti.SporadicName),
    Nonempty (S ≃* Blueprint.NativeSporadic.Carrier s) → CF516LeafAt S

theorem cf516PumpLeaf_of_leafAt
    (h : ∀ (S : Type) [Group S] [Finite S], Blueprint.Catalog S → CF516LeafAt S) :
    CF516PumpLeaf := by
  intro S _ _ hs hna hcat hK σ P hP p f hp hp2 hf hPm t ht ht2 J hJC hJ hJm hσJ hσO JB hJB
    hJBp hJBs
  exact h S hcat hs hna hK σ P hP p f hp hp2 hf hPm t ht ht2 J hJC hJ hJm hσJ hσO JB hJB hJBp hJBs

theorem leafAt_of_oddLieType (hLin : CF516LinRow) (hSp : CF516SpRow) (hOrth : CF516OrthRow)
    (hExc : CF516ExcRow) {S : Type} [Group S] [Finite S] (h : Blueprint.OddLieType S) :
    CF516LeafAt S := by
  obtain ⟨τ, n, r, e, hr, hr2, hadm, hm⟩ := h
  cases τ with
  | PSL => exact hLin S _ n r e hr hr2 (Or.inl rfl) hadm hm
  | PSU => exact hLin S _ n r e hr hr2 (Or.inr rfl) hadm hm
  | PSp => exact hSp S _ n r e hr hr2 rfl hadm hm
  | POmegaOdd => exact hOrth S _ n r e hr hr2 (Or.inl rfl) hadm hm
  | POmegaPlus => exact hOrth S _ n r e hr hr2 (Or.inr (Or.inl rfl)) hadm hm
  | POmegaMinus => exact hOrth S _ n r e hr hr2 (Or.inr (Or.inr rfl)) hadm hm
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 =>
    exact hExc S _ n r e hr hr2 (Or.inl (by decide)) hadm hm
  | twistedG2 => exact hExc S _ n r e hr hr2 (Or.inr rfl) hadm hm
  | twistedB2 | twistedF4 | Tits => exact absurd hadm.2.2.2.1 hr2

theorem cf516PumpLeaf_of_rows (hEven : CF516EvenRow) (hLin : CF516LinRow) (hSp : CF516SpRow)
    (hOrth : CF516OrthRow) (hExc : CF516ExcRow) (hAlt : CF516AltRow) (hSpor : CF516SporRow) :
    CF516PumpLeaf := by
  refine cf516PumpLeaf_of_leafAt fun S _ _ hcat hs hna => ?_
  rcases (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat with
    ⟨n, hn, he⟩ | ho | he | ⟨s, hs'⟩
  · exact hAlt S n hn he hs hna
  · exact leafAt_of_oddLieType hLin hSp hOrth hExc ho hs hna
  · exact hEven S he hs hna
  · exact hSpor S s hs' hs hna

end CFSG.ComponentClassification.GSThmB
