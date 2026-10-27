module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.Milestones.CT_catalog_nonabelian_type_partition

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat

open CFSG Subgroup CatLeaf

@[expose] def FivePumpNonAlt (S : Type) [Group S] : Prop :=
  Blueprint.LieModel S .PSL 2 2 4 ∨ Blueprint.LieModel S .PSL 3 2 2 ∨
  Blueprint.LieModel S .PSU 3 2 2 ∨ Blueprint.LieModel S .PSL 2 5 2 ∨
  Blueprint.LieModel S .PSL 3 5 1 ∨ Blueprint.LieModel S .PSU 3 5 1 ∨
  Blueprint.LieModel S .PSp 2 5 1 ∨
  Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .J1) ∨
  Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .J2) ∨
  Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .M12)

@[expose] def FivePumpOutcome (S : Type) [Group S] : Prop :=
  (∃ m : ℕ, Odd m ∧ 7 ≤ m ∧ Nonempty (S ≃* alternatingGroup (Fin m))) ∨ FivePumpNonAlt S

@[expose] def FivePumpClause (𝓕 : ∀ (S : Type) [Group S], Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ x y : S, x * y ≠ y * x) → 𝓕 S →
    ∀ (σ : MulAut S) (P : Subgroup S), ProperFixedComponent σ P →
    Open.fusionZStar ↥P = pPrimeCore 2 ↥P →
    Nonempty (↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin 5)) →
    (∀ P' : Subgroup S, ProperFixedComponent σ P' → P' = P) → FivePumpOutcome S

@[expose] def FivePumpLeaf : Prop := FivePumpClause (fun S _ => Blueprint.Catalog S)

@[expose] def FivePumpAltClause : Prop :=
  FivePumpClause (fun S _ => ∃ n : ℕ, 5 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n)))

@[expose] def FivePumpOddPrimeClause : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ x y : S, x * y ≠ y * x) →
    ∀ (τ : Open.StatedLieTag) (n p f : ℕ), p.Prime → p ≠ 2 → Blueprint.LieModel S τ n p f →
    ∀ (σ : MulAut S) (P : Subgroup S), ProperFixedComponent σ P →
    Open.fusionZStar ↥P = pPrimeCore 2 ↥P →
    Nonempty (↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin 5)) → p = 5

@[expose] def FivePumpCharFiveClause (τ : Open.StatedLieTag) : Prop :=
  FivePumpClause (fun S _ => ∃ n f : ℕ, Blueprint.LieModel S τ n 5 f)

@[expose] def FivePumpEvenClause (τ : Open.StatedLieTag) : Prop :=
  FivePumpClause (fun S _ => ∃ n f : ℕ, Blueprint.LieModel S τ n 2 f)

@[expose] def FivePumpSporClause (s : TauCeti.SporadicName) : Prop :=
  FivePumpClause (fun S _ => Nonempty (S ≃* Blueprint.NativeSporadic.Carrier s))

theorem fivePumpLeaf_of_clauses (hAlt : FivePumpAltClause) (hOdd : FivePumpOddPrimeClause)
    (h5 : ∀ τ, FivePumpCharFiveClause τ) (hEven : ∀ τ, FivePumpEvenClause τ)
    (hSpor : ∀ s, FivePumpSporClause s) : FivePumpLeaf := by
  intro S _ _ hs hna hcat σ P hP hZ eP huniq
  rcases (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat with
    ⟨n, hn, e⟩ | ⟨τ, n, p, f, hp, hp2, -, hL⟩ | ⟨τ, n, f, -, hL⟩ | ⟨s, e⟩
  · exact hAlt S hs hna ⟨n, hn, e⟩ σ P hP hZ eP huniq
  · have h5' : p = 5 := hOdd S hs hna τ n p f hp hp2 hL σ P hP hZ eP
    subst h5'
    exact h5 τ S hs hna ⟨n, f, hL⟩ σ P hP hZ eP huniq
  · exact hEven τ S hs hna ⟨n, f, hL⟩ σ P hP hZ eP huniq
  · exact hSpor s S hs hna e σ P hP hZ eP huniq

theorem fivePump_spor_J1 : FivePumpSporClause .J1 :=
  fun _ _ _ _ _ ⟨e⟩ _ _ _ _ _ _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inl ⟨e⟩))))))))

theorem fivePump_spor_J2 : FivePumpSporClause .J2 :=
  fun _ _ _ _ _ ⟨e⟩ _ _ _ _ _ _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inl ⟨e⟩)))))))))

theorem fivePump_spor_M12 : FivePumpSporClause .M12 :=
  fun _ _ _ _ _ ⟨e⟩ _ _ _ _ _ _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr ⟨e⟩)))))))))

@[expose] def FivePumpUpInput : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SectionRank.IsKGroupCat H →
    ∀ M : Subgroup H, IsPComponent 2 M →
    ∀ x : H, orderOf x = 2 → x ∈ normalizer (M : Set H) →
    ∀ T : Subgroup H, T ≤ M → T ≤ centralizer ({x} : Set H) →
      IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set H))) →
      Nonempty (↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin 5)) →
      T ⊔ (pPrimeCore 2 ↥M).map M.subtype ≠ M →
      (∀ T' : Subgroup H, T' ≤ M → T' ≤ centralizer ({x} : Set H) →
        IsPComponent 2 (T'.subgroupOf (centralizer ({x} : Set H))) → T' = T) →
      (∃ m : ℕ, Odd m ∧ 7 ≤ m ∧ Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m))) ∨
        FivePumpNonAlt (↥M ⧸ Open.fusionZStar ↥M)

@[expose] def FiveTwoLayerOutcome (S : Type) [Group S] : Prop :=
  Blueprint.LieModel S .PSL 4 5 1 ∨ Blueprint.LieModel S .PSU 4 5 1

@[expose] def FiveTwoLayerClause (𝓕 : ∀ (S : Type) [Group S], Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ x y : S, x * y ≠ y * x) → 𝓕 S →
    ∀ (σ : MulAut S) (P₁ P₂ : Subgroup S), ProperFixedComponent σ P₁ →
    ProperFixedComponent σ P₂ → P₁ ≠ P₂ →
    Open.fusionZStar ↥P₁ = pPrimeCore 2 ↥P₁ → Open.fusionZStar ↥P₂ = pPrimeCore 2 ↥P₂ →
    Nonempty (↥P₁ ⧸ Open.fusionZStar ↥P₁ ≃* alternatingGroup (Fin 5)) →
    Nonempty (↥P₂ ⧸ Open.fusionZStar ↥P₂ ≃* alternatingGroup (Fin 5)) →
    (∀ P' : Subgroup S, ProperFixedComponent σ P' → P' = P₁ ∨ P' = P₂) → FiveTwoLayerOutcome S

@[expose] def FiveTwoLayerLeaf : Prop := FiveTwoLayerClause (fun S _ => Blueprint.Catalog S)

@[expose] def FiveTwoLayerAltClause : Prop :=
  FiveTwoLayerClause (fun S _ => ∃ n : ℕ, 5 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n)))

@[expose] def FiveTwoLayerCharFiveClause (τ : Open.StatedLieTag) : Prop :=
  FiveTwoLayerClause (fun S _ => ∃ n f : ℕ, Blueprint.LieModel S τ n 5 f)

@[expose] def FiveTwoLayerEvenClause (τ : Open.StatedLieTag) : Prop :=
  FiveTwoLayerClause (fun S _ => ∃ n f : ℕ, Blueprint.LieModel S τ n 2 f)

@[expose] def FiveTwoLayerSporClause (s : TauCeti.SporadicName) : Prop :=
  FiveTwoLayerClause (fun S _ => Nonempty (S ≃* Blueprint.NativeSporadic.Carrier s))

theorem fiveTwoLayerLeaf_of_clauses (hAlt : FiveTwoLayerAltClause) (hOdd : FivePumpOddPrimeClause)
    (h5 : ∀ τ, FiveTwoLayerCharFiveClause τ) (hEven : ∀ τ, FiveTwoLayerEvenClause τ)
    (hSpor : ∀ s, FiveTwoLayerSporClause s) : FiveTwoLayerLeaf := by
  intro S _ _ hs hna hcat σ P₁ P₂ h₁ h₂ hne hZ₁ hZ₂ e₁ e₂ huniq
  rcases (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat with
    ⟨n, hn, e⟩ | ⟨τ, n, p, f, hp, hp2, -, hL⟩ | ⟨τ, n, f, -, hL⟩ | ⟨s, e⟩
  · exact hAlt S hs hna ⟨n, hn, e⟩ σ P₁ P₂ h₁ h₂ hne hZ₁ hZ₂ e₁ e₂ huniq
  · have h5' : p = 5 := hOdd S hs hna τ n p f hp hp2 hL σ P₁ h₁ hZ₁ e₁
    subst h5'
    exact h5 τ S hs hna ⟨n, f, hL⟩ σ P₁ P₂ h₁ h₂ hne hZ₁ hZ₂ e₁ e₂ huniq
  · exact hEven τ S hs hna ⟨n, f, hL⟩ σ P₁ P₂ h₁ h₂ hne hZ₁ hZ₂ e₁ e₂ huniq
  · exact hSpor s S hs hna e σ P₁ P₂ h₁ h₂ hne hZ₁ hZ₂ e₁ e₂ huniq

@[expose] def FiveTwoLayerInput : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SectionRank.IsKGroupCat H →
    ∀ M : Subgroup H, IsPComponent 2 M →
    ∀ x : H, orderOf x = 2 → x ∈ normalizer (M : Set H) →
    ∀ T₁ T₂ : Subgroup H, T₁ ≠ T₂ → T₁ ≤ M → T₂ ≤ M →
      T₁ ≤ centralizer ({x} : Set H) → T₂ ≤ centralizer ({x} : Set H) →
      IsPComponent 2 (T₁.subgroupOf (centralizer ({x} : Set H))) →
      IsPComponent 2 (T₂.subgroupOf (centralizer ({x} : Set H))) →
      Nonempty (↥T₁ ⧸ pPrimeCore 2 ↥T₁ ≃* alternatingGroup (Fin 5)) →
      Nonempty (↥T₂ ⧸ pPrimeCore 2 ↥T₂ ≃* alternatingGroup (Fin 5)) →
      (∀ T' : Subgroup H, T' ≤ M → T' ≤ centralizer ({x} : Set H) →
        IsPComponent 2 (T'.subgroupOf (centralizer ({x} : Set H))) → T' = T₁ ∨ T' = T₂) →
      FiveTwoLayerOutcome (↥M ⧸ Open.fusionZStar ↥M)

end CFSG.ComponentClassification.SolMax.FiveCat
