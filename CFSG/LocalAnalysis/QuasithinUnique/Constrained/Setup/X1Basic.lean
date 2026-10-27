module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique.Setup.Family

@[expose] def IsIrrOn {W : Type} [CommGroup W] (L : Subgroup (MulAut W)) : Prop :=
  Nontrivial W ∧ ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤

section Transfer

variable {V : Type} [CommGroup V]

@[expose] def TL (T L : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  T ⊓ Subgroup.normalizer (L : Set (MulAut V))

@[expose] def HL (T L : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  L ⊔ TL T L

@[expose] def XL (M T L : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  (M ⊓ L) ⊔ TL T L

end Transfer

structure ComponentTransfer (V : Type) [CommGroup V] [Finite V] (T M L : Subgroup (MulAut V)) :
    Prop where
  sylow : IsSylowTwoOf (TL T L) (HL T L)
  not_normal : ¬ ((TL T L).subgroupOf (HL T L)).Normal
  unique_max : XL M T L < HL T L ∧ TL T L ≤ XL M T L ∧
    ∀ Y : Subgroup (MulAut V), TL T L ≤ Y → Y < HL T L → Y ≤ XL M T L
  offender : ∃ A : Subgroup (MulAut V), A ≤ TL T L ∧ IsElemAbelian2 A ∧ ⁅L, A⁆ = L ∧
    Nat.card V ≤ Nat.card A * Nat.card (fixV A) ∧
    ∀ B : Subgroup (MulAut V), B ≤ A → B ≠ ⊥ → B ≠ A →
      Nat.card B * Nat.card (fixV B) < Nat.card A * Nat.card (fixV A)

@[expose] def ComponentTransferProp : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H T M E : Subgroup (MulAut V)),
    FFHyp V H T M E → ¬ Group.IsSolvable H →
    ∀ L : Subgroup (MulAut V), IsComp L H → ComponentTransfer V T M L

structure IrrSection (V : Type) [CommGroup V] [Finite V] (L A : Subgroup (MulAut V)) where
  I : Subgroup V
  W : Type
  [commGroup : CommGroup W]
  [finite : Finite W]
  τI : ↥(L ⊔ A) →* MulAut ↥I
  π : ↥I →* W
  τW : ↥(L ⊔ A) →* MulAut W
  τI_apply : ∀ (x : ↥(L ⊔ A)) (v : ↥I), ((τI x v : ↥I) : V) = (x : MulAut V) (v : V)
  I_eq : I = Subgroup.closure {w | ∃ l ∈ L, ∃ v ∈ I, (l : MulAut V) v * v⁻¹ = w}
  π_surjective : Function.Surjective π
  π_ker : ∀ v : ↥I, π v = 1 ↔ ∀ l ∈ L, (l : MulAut V) (v : V) = (v : V)
  π_equivariant : ∀ (x : ↥(L ⊔ A)) (v : ↥I), π (τI x v) = τW x (π v)
  nontrivial : Nontrivial W
  irreducible : ∀ U : Subgroup W,
    (∀ x : ↥(L ⊔ A), (x : MulAut V) ∈ L → ∀ u ∈ U, τW x u ∈ U) → U = ⊥ ∨ U = ⊤
  lbar_ne_bot : (τW.comp (Subgroup.inclusion le_sup_left)).range ≠ ⊥
  lbar_quasisimple : CFSG.IsQuasisimple ↥((τW.comp (Subgroup.inclusion le_sup_left)).range)
  abar_ne_bot : (τW.comp (Subgroup.inclusion le_sup_right)).range ≠ ⊥
  abar_elem : IsElemAbelian2 (τW.comp (Subgroup.inclusion le_sup_right)).range
  abar_quadratic : IsQuadratic (τW.comp (Subgroup.inclusion le_sup_right)).range
  abar_offender : Nat.card W ≤
    Nat.card (τW.comp (Subgroup.inclusion le_sup_right)).range *
      Nat.card (fixV (τW.comp (Subgroup.inclusion le_sup_right)).range)
  injective_image : ∀ x : ↥(L ⊔ A), (∀ w, τW x w = w) → ∀ v, τI x v = v

attribute [instance] IrrSection.commGroup IrrSection.finite

@[expose] def IrreducibleSectionProp : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v * v = 1) →
    ∀ G L A : Subgroup (MulAut V), IsComp L G → IsBestOffender G A → ⁅L, A⁆ ≠ ⊥ →
      A ≤ Subgroup.normalizer (L : Set (MulAut V)) ∧ ⁅L, A⁆ = L ∧ Nonempty (IrrSection V L A)

@[expose] def M11M12ExclusionProp : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ L E : Subgroup (MulAut W), CFSG.IsQuasisimple ↥L → IsIrrOn L →
      (Nonempty (CQ L ≃* NativeSporadic.Carrier .M11) ∨
        Nonempty (CQ L ≃* NativeSporadic.Carrier .M12)) →
      E ≤ Subgroup.normalizer (L : Set (MulAut W)) → E ≠ ⊥ → IsElemAbelian2 E →
      Nat.card E * Nat.card (fixV E) < Nat.card W

@[expose] def MathieuExclusionProp : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ L E : Subgroup (MulAut W), CFSG.IsQuasisimple ↥L → IsIrrOn L →
      (Nonempty (CQ L ≃* NativeSporadic.Carrier .M22) ∨
        Nonempty (CQ L ≃* NativeSporadic.Carrier .M23) ∨
        Nonempty (CQ L ≃* NativeSporadic.Carrier .M24)) →
      E ≤ Subgroup.normalizer (L : Set (MulAut W)) → E ≠ ⊥ → IsElemAbelian2 E → IsQuadratic E →
      Nat.card E * Nat.card (fixV E) < Nat.card W

@[expose] def J1ExclusionProp : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ L E : Subgroup (MulAut W), Group.IsPerfect ↥L → IsIrrOn L →
      Nonempty (CQ L ≃* NativeSporadic.Carrier .J1) →
      E ≤ Subgroup.normalizer (L : Set (MulAut W)) → E ≠ ⊥ → IsElemAbelian2 E →
      Nat.card E * Nat.card (fixV E) < Nat.card W

@[expose] def HeExclusionProp : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ L E : Subgroup (MulAut W), Group.IsPerfect ↥L → IsIrrOn L →
      E ≤ Subgroup.normalizer (L : Set (MulAut W)) → E ≠ ⊥ → IsElemAbelian2 E →
      Nat.card W ≤ Nat.card E * Nat.card (fixV E) →
      ¬ Nonempty (CQ L ≃* NativeSporadic.Carrier .He)

@[expose] def J4ExclusionProp : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ L E : Subgroup (MulAut W), Group.IsPerfect ↥L → IsIrrOn L →
      E ≤ Subgroup.normalizer (L : Set (MulAut W)) → E ≠ ⊥ → IsElemAbelian2 E →
      Nat.card W ≤ Nat.card E * Nat.card (fixV E) →
      ¬ Nonempty (CQ L ≃* NativeSporadic.Carrier .J4)

@[expose] def TwoExtensionProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T K : Subgroup X), K.Normal → IsPGroup 2 T →
    ¬ 2 ∣ T.index → K ⊔ T = ⊤ →
    (Nonempty (↥K ≃* NativeSporadic.Carrier .J2) ∨ Nonempty (↥K ≃* NativeSporadic.Carrier .HS) ∨
      Nonempty (↥K ≃* NativeSporadic.Carrier .Ru)) →
    ∃ U₁ U₂ : Subgroup X, U₁ ≠ U₂ ∧ IsCoatom U₁ ∧ IsCoatom U₂ ∧ T ≤ U₁ ∧ T ≤ U₂

@[expose] def SporadicExclusion (s : TauCeti.SporadicName) : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ L E : Subgroup (MulAut W), CFSG.IsQuasisimple ↥L → IsIrrOn L →
      Nonempty (CQ L ≃* NativeSporadic.Carrier s) →
      E ≤ Subgroup.normalizer (L : Set (MulAut W)) → E ≠ ⊥ → IsElemAbelian2 E → IsQuadratic E →
      Nat.card E * Nat.card (fixV E) < Nat.card W

@[expose] def TwoExtensionFor (s : TauCeti.SporadicName) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T K : Subgroup X), K.Normal → IsPGroup 2 T →
    ¬ 2 ∣ T.index → K ⊔ T = ⊤ → Nonempty (↥K ≃* NativeSporadic.Carrier s) →
    ∃ U₁ U₂ : Subgroup X, U₁ ≠ U₂ ∧ IsCoatom U₁ ∧ IsCoatom U₂ ∧ T ≤ U₁ ∧ T ≤ U₂

theorem sporadicExclusion_of_M11M12 (h : M11M12ExclusionProp) :
    SporadicExclusion .M11 ∧ SporadicExclusion .M12 :=
  ⟨fun W _ _ hW L E hq hirr hiso hE hEne hEel _ =>
      h W hW L E hq hirr (Or.inl hiso) hE hEne hEel,
    fun W _ _ hW L E hq hirr hiso hE hEne hEel _ =>
      h W hW L E hq hirr (Or.inr hiso) hE hEne hEel⟩

theorem sporadicExclusion_of_Mathieu (h : MathieuExclusionProp) :
    SporadicExclusion .M22 ∧ SporadicExclusion .M23 ∧ SporadicExclusion .M24 :=
  ⟨fun W _ _ hW L E hq hirr hiso hE hEne hEel hq2 =>
      h W hW L E hq hirr (Or.inl hiso) hE hEne hEel hq2,
    fun W _ _ hW L E hq hirr hiso hE hEne hEel hq2 =>
      h W hW L E hq hirr (Or.inr (Or.inl hiso)) hE hEne hEel hq2,
    fun W _ _ hW L E hq hirr hiso hE hEne hEel hq2 =>
      h W hW L E hq hirr (Or.inr (Or.inr hiso)) hE hEne hEel hq2⟩

theorem sporadicExclusion_of_J1 (h : J1ExclusionProp) : SporadicExclusion .J1 :=
  fun W _ _ hW L E hq hirr hiso hE hEne hEel _ =>
    h W hW L E hq.1 hirr hiso hE hEne hEel

theorem sporadicExclusion_of_He (h : HeExclusionProp) : SporadicExclusion .He :=
  fun W _ _ hW L E hq hirr hiso hE hEne hEel _ => by
    by_contra hcon
    exact h W hW L E hq.1 hirr hE hEne hEel (not_lt.1 hcon) hiso

theorem sporadicExclusion_of_J4 (h : J4ExclusionProp) : SporadicExclusion .J4 :=
  fun W _ _ hW L E hq hirr hiso hE hEne hEel _ => by
    by_contra hcon
    exact h W hW L E hq.1 hirr hE hEne hEel (not_lt.1 hcon) hiso

theorem twoExtensionFor_of (h : TwoExtensionProp) :
    TwoExtensionFor .J2 ∧ TwoExtensionFor .HS ∧ TwoExtensionFor .Ru :=
  ⟨fun X _ _ T K hK hT hidx hsup hiso => h X T K hK hT hidx hsup (Or.inl hiso),
    fun X _ _ T K hK hT hidx hsup hiso => h X T K hK hT hidx hsup (Or.inr (Or.inl hiso)),
    fun X _ _ T K hK hT hidx hsup hiso => h X T K hK hT hidx hsup (Or.inr (Or.inr hiso))⟩

end CFSG.QuasithinUnique.Setup.X1
