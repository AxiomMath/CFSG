module

public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic

public section

namespace CFSG.SectionRank

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

variable {G H : Type} [Group G] [Group H]

theorem statedClassicalModel_of_mulEquiv (e : G ≃* H) {t : StatedLieTag} {n p f : ℕ}
    (h : StatedClassicalModel H t n p f) : StatedClassicalModel G t n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm h

theorem untwistedChevalleyModel_of_mulEquiv (e : G ≃* H) {τ : Chevalley.Tag} {q : ℕ}
    (h : UntwistedChevalleyModel H τ q) : UntwistedChevalleyModel G τ q := by
  obtain ⟨K, _, _, hK, ⟨e'⟩⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e.trans e'⟩⟩

theorem twistedChevalleyModel_of_mulEquiv (e : G ≃* H) {t : Chevalley.TwistTag} {q : ℕ}
    (h : TwistedChevalleyModel H t q) : TwistedChevalleyModel G t q := by
  obtain ⟨K, _, _, hK, σ, hσ, ⟨e'⟩⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, σ, hσ, ⟨e.trans e'⟩⟩

theorem chevalleyExceptionalModel_of_mulEquiv (e : G ≃* H) {t : StatedLieTag} {p f : ℕ}
    (h : ChevalleyExceptionalModel H t p f) : ChevalleyExceptionalModel G t p f := by
  obtain ⟨hadm, hm⟩ := h
  refine ⟨hadm, ?_⟩
  cases t with
  | G2 => exact untwistedChevalleyModel_of_mulEquiv e hm
  | F4 => exact untwistedChevalleyModel_of_mulEquiv e hm
  | E6 => exact untwistedChevalleyModel_of_mulEquiv e hm
  | E7 => exact untwistedChevalleyModel_of_mulEquiv e hm
  | E8 => exact untwistedChevalleyModel_of_mulEquiv e hm
  | twistedE6 => exact twistedChevalleyModel_of_mulEquiv e hm
  | trialityD4 => exact twistedChevalleyModel_of_mulEquiv e hm
  | _ => exact hm.elim

theorem reeTitsRelationModel_of_mulEquiv (e : G ≃* H) {τ : Chevalley.Tag}
    {ρ : Equiv.Perm (Fin τ.rank)} {L : Finset (Fin τ.rank)} {p f a : ℕ}
    (h : ReeTitsRelationModel H τ ρ L p f a) : ReeTitsRelationModel G τ ρ L p f a := by
  obtain ⟨K, _, _, hK, ⟨e'⟩⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e.trans e'⟩⟩

theorem reeTitsModel_of_mulEquiv (e : G ≃* H) {t : StatedLieTag} {p f : ℕ}
    (h : ReeTitsModel H t p f) : ReeTitsModel G t p f := by
  obtain ⟨hadm, a, ha, hm⟩ := h
  refine ⟨hadm, a, ha, ?_⟩
  cases t with
  | twistedG2 => exact reeTitsRelationModel_of_mulEquiv e hm
  | twistedF4 => exact reeTitsRelationModel_of_mulEquiv e hm
  | Tits => exact reeTitsRelationModel_of_mulEquiv e hm
  | _ => exact hm.elim

theorem suzukiModel_of_mulEquiv (e : G ≃* H) {p f : ℕ} (h : SuzukiModel H p f) :
    SuzukiModel G p f := by
  obtain ⟨hp, a, ha, K, _, _, hf, hK, ⟨e'⟩⟩ := h
  exact ⟨hp, a, ha, K, inferInstance, inferInstance, hf, hK, ⟨e.trans e'⟩⟩

theorem catalog_of_mulEquiv (e : G ≃* H) (h : Catalog H) : Catalog G := by
  rcases h with ⟨p, hp, ⟨e'⟩⟩ | ⟨n, hn, ⟨e'⟩⟩ | ⟨t, n, p, f, hm⟩ |
      (⟨t, p, f, ht, hm⟩ | ⟨t, p, f, ht, hm⟩ | ⟨p, f, hm⟩) | ⟨s, ⟨e'⟩⟩
  · exact Or.inl ⟨p, hp, ⟨e.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.trans e'⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨t, n, p, f, statedClassicalModel_of_mulEquiv e hm⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (Or.inl ⟨t, p, f, ht, chevalleyExceptionalModel_of_mulEquiv e hm⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (Or.inr (Or.inl ⟨t, p, f, ht, reeTitsModel_of_mulEquiv e hm⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr ⟨p, f, suzukiModel_of_mulEquiv e hm⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨s, ⟨e.trans e'⟩⟩)))

theorem catalog_congr (e : G ≃* H) : Catalog G ↔ Catalog H :=
  ⟨catalog_of_mulEquiv e.symm, catalog_of_mulEquiv e⟩

theorem catalog_isoInvariant : KCore.IsoInvariant Catalog := catalog_of_mulEquiv

theorem catalog_containsAbelianSimple : KCore.ContainsAbelianSimple Catalog := by
  intro S _ _ _ hcomm
  let _ : CommGroup S := { ‹Group S› with mul_comm := hcomm }
  have hp : (Nat.card S).Prime := IsSimpleGroup.prime_card
  have : Fact (Nat.card S).Prime := ⟨hp⟩
  have : NeZero (Nat.card S) := ⟨hp.ne_zero⟩
  refine Or.inl ⟨Nat.card S, hp, ⟨mulEquivOfPrimeCardEq rfl ?_⟩⟩
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

@[expose] def IsKGroupCat (X : Type) [Group X] : Prop :=
  KCore.KGroupAllSimple Catalog X

@[expose] def IsSQTKCat (X : Type) [Group X] : Prop :=
  IsStronglyQuasithin X ∧ IsKGroupCat X

theorem isKGroupCat_iff_kGroupAllSimple {X : Type} [Group X] :
    IsKGroupCat X ↔ KCore.KGroupAllSimple Catalog X :=
  Iff.rfl

theorem isSQTKCat_iff_sQTKOver {X : Type} [Group X] :
    IsSQTKCat X ↔ KCore.SQTKOver Catalog IsStronglyQuasithin X :=
  Iff.rfl

theorem catalog_of_isKGroupCat_of_surjective {X : Type} [Group X] (hX : IsKGroupCat X)
    (K : Subgroup X) {S : Type} [Group S] [IsSimpleGroup S] (φ : K →* S)
    (hφ : Function.Surjective φ) : Catalog S :=
  KCore.KGroupAllSimple.catalogue_of_surjective catalog_isoInvariant hX K φ hφ

theorem IsKGroupCat.subgroup {X : Type} [Group X] (hX : IsKGroupCat X) (Y : Subgroup X) :
    IsKGroupCat Y :=
  KCore.KGroupAllSimple.subgroup catalog_isoInvariant hX Y

theorem IsKGroupCat.quotient {X : Type} [Group X] (hX : IsKGroupCat X) (M : Subgroup X)
    [M.Normal] : IsKGroupCat (X ⧸ M) :=
  KCore.KGroupAllSimple.quotient catalog_isoInvariant hX M

theorem IsKGroupCat.of_mulEquiv {X Y : Type} [Group X] [Group Y] (hY : IsKGroupCat Y)
    (e : X ≃* Y) : IsKGroupCat X :=
  KCore.KGroupAllSimple.of_mulEquiv catalog_isoInvariant hY e

theorem IsKGroupCat.of_injective {X Y : Type} [Group X] [Group Y] (hY : IsKGroupCat Y)
    (f : X →* Y) (hf : Function.Injective f) : IsKGroupCat X :=
  KCore.KGroupAllSimple.of_injective catalog_isoInvariant hY f hf

theorem IsKGroupCat.of_surjective {X Y : Type} [Group X] [Group Y] (hX : IsKGroupCat X)
    (f : X →* Y) (hf : Function.Surjective f) : IsKGroupCat Y :=
  KCore.KGroupAllSimple.of_surjective catalog_isoInvariant hX f hf

end CFSG.SectionRank
