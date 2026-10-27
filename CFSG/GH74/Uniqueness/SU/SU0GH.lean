module

public import CFSG.GH74.Generic.Sections

public section

namespace CFSG.GH74.Uniqueness.SU.SU0

open Subgroup CFSG.GH74

@[expose] def GHGroup (H : Type) [Group H] : Prop :=
  ∀ (A : Subgroup H) (S : Type) [Group S] (f : ↥A →* S), Function.Surjective f →
    IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) → GHList S

variable {H : Type} [Group H]

theorem GHGroup.ghList_of_surjection (h : GHGroup H) {A : Subgroup H} {S : Type} [Group S]
    (f : ↥A →* S) (hf : Function.Surjective f) (hs : IsSimpleGroup S)
    (hn : ∃ a b : S, a * b ≠ b * a) : GHList S :=
  h A S f hf hs hn

theorem GHGroup.of_kgh {G : Type} [Group G] (hK : KGH G) {M : Subgroup G} (hM : M ≠ ⊤) :
    GHGroup M := by
  intro A S _ f hf hs hn
  let A' : Subgroup G := A.map M.subtype
  have hA'M : A' ≤ M := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hA' : A' ≠ ⊤ := fun h => hM (top_le_iff.1 (h ▸ hA'M))
  let e : ↥A ≃* ↥A' := A.equivMapOfInjective M.subtype M.subtype_injective
  exact Generic.ghList_of_surjection hK hA' (f.comp e.symm.toMonoidHom)
    (hf.comp e.symm.surjective) hs hn

theorem GHGroup.subgroup (h : GHGroup H) (A : Subgroup H) : GHGroup A := by
  intro B S _ f hf hs hn
  let B' : Subgroup H := B.map A.subtype
  let e : ↥B ≃* ↥B' := B.equivMapOfInjective A.subtype A.subtype_injective
  exact h B' S (f.comp e.symm.toMonoidHom) (hf.comp e.symm.surjective) hs hn

theorem GHGroup.quotient (h : GHGroup H) (N : Subgroup H) [N.Normal] : GHGroup (H ⧸ N) := by
  intro B S _ f hf hs hn
  let B' : Subgroup H := B.comap (QuotientGroup.mk' N)
  let g : ↥B' →* ↥B := ((QuotientGroup.mk' N).comp B'.subtype).codRestrict B fun x => x.2
  have hg : Function.Surjective g := by
    intro b
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N (b : H ⧸ N)
    exact ⟨⟨x, show QuotientGroup.mk' N x ∈ B by rw [hx]; exact b.2⟩, Subtype.ext hx⟩
  exact h B' S (f.comp g) (hf.comp hg) hs hn

theorem GHGroup.of_mulEquiv {H' : Type} [Group H'] (e : H ≃* H') (h : GHGroup H) :
    GHGroup H' := by
  intro B S _ f hf hs hn
  let B' : Subgroup H := B.comap e.toMonoidHom
  let g : ↥B' →* ↥B := (e.toMonoidHom.comp B'.subtype).codRestrict B fun x => x.2
  have hg : Function.Surjective g := by
    intro b
    exact ⟨⟨e.symm b, show e (e.symm (b : H')) ∈ B by rw [MulEquiv.apply_symm_apply]; exact b.2⟩,
      Subtype.ext (by simp [g])⟩
  exact h B' S (f.comp g) (hf.comp hg) hs hn

theorem GHGroup.of_kgh_quotient {G : Type} [Group G] (hK : KGH G) {M : Subgroup G} (hM : M ≠ ⊤)
    (N : Subgroup M) [N.Normal] : GHGroup (M ⧸ N) :=
  (GHGroup.of_kgh hK hM).quotient N

end CFSG.GH74.Uniqueness.SU.SU0
