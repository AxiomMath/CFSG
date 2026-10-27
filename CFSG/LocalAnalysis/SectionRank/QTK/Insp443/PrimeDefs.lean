module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConf
public import CFSG.LocalAnalysis.SectionRank.QTK.List
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Hyp

public section

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace CFSG.Quasithin.H13.Ch4.E443

@[expose] def Concl443BWith (b : Prop) (G : Type) [Group G] (T M L K LB VB : Subgroup G) :
    Prop :=
  (CFSG.IsQuasisimple (↥LB ⧸ CFSG.pCore 2 ↥LB) ∧ Shape443 (↥LB ⧸ CFSG.pCore 2 ↥LB) ∧
    (((∃ _ : IsMulCommutative ↥VB,
          IsFFModule (V := ↥VB) (autOn (M ⊓ Subgroup.normalizer (VB : Set G)) VB)) ∧
        (LieModel (↥LB ⧸ CFSG.pCore 2 ↥LB) .PSL 3 2 1 → IsNaturalSumUnder 3 LB VB) ∧
        (LieModel (↥LB ⧸ CFSG.pCore 2 ↥LB) .PSL 4 2 1 →
          IsNaturalSumUnder 4 LB VB ∨
            ∃ _ : IsMulCommutative ↥VB, SLExteriorTwo (V := ↥VB) (autOn LB VB) ⊤ ⊥ 4) ∧
        b ∧
        (LieModel (↥LB ⧸ CFSG.pCore 2 ↥LB) .PSU 3 3 1 → Nat.card VB = 2 ^ 6 →
          ∃ V₃ : Subgroup G, V₃ ≤ VB ∧ Nat.card V₃ = 2 ^ 3 ∧
            T ⊓ conjClosure L T ≤ Subgroup.normalizer (V₃ : Set G) ∧
              ¬ K ⊓ Subgroup.centralizer (V₃ : Set G) ≤ M)) ∨
      (∃ m : ℕ, 1 ≤ m ∧ LieModel (↥LB ⧸ CFSG.pCore 2 ↥LB) .PSL 2 2 (2 * m) ∧
        ∃ _ : IsMulCommutative ↥VB, BinaryOrthogonalFour (V := ↥VB) (autOn LB VB) ⊤ ⊥ m) ∨
      (LieModel (↥LB ⧸ CFSG.pCore 2 ↥LB) .PSL 3 2 1 ∧
        ∃ _ : IsMulCommutative ↥VB, FanoCoreModule (V := ↥VB) (autOn LB VB) ⊤ ⊥))) ∨
  (IsSporadic .J4 ↥K ∧
    (IsSporadic .M24 (↥LB ⧸ CFSG.pCore 2 ↥LB) ∨ LieModel (↥LB ⧸ CFSG.pCore 2 ↥LB) .PSL 5 2 1))

@[expose] def Concl443B' (G : Type) [Group G] (T M L K LB VB : Subgroup G) : Prop :=
  Concl443BWith
    ((Group.IsPerfect (↥LB ⧸ CFSG.pCore 2 ↥LB) ∧
        Nat.card (Subgroup.center (↥LB ⧸ CFSG.pCore 2 ↥LB)) = 3 ∧
        Nonempty ((↥LB ⧸ CFSG.pCore 2 ↥LB) ⧸ Subgroup.center (↥LB ⧸ CFSG.pCore 2 ↥LB) ≃*
          alternatingGroup (Fin 6))) → Nat.card VB = 2 ^ 6 →
      ∀ z ∈ VB ⊓ Subgroup.centralizer ((T ⊓ conjClosure L T : Subgroup G) : Set G),
        orderOf z = 2 → ¬ VB ≤ pCoreOf 2 (K ⊓ Subgroup.centralizer ({z} : Set G)))
    G T M L K LB VB

theorem Concl443BWith.mono {b b' : Prop} (hb : b → b') {G : Type} [Group G]
    {T M L K LB VB : Subgroup G} (h : Concl443BWith b G T M L K LB VB) :
    Concl443BWith b' G T M L K LB VB := by
  rcases h with ⟨hq, hshape, ⟨hFF, hnat3, hnat4, hB, hU3⟩ | hbin | hfano⟩ | hJ
  · exact Or.inl ⟨hq, hshape, Or.inl ⟨hFF, hnat3, hnat4, hb hB, hU3⟩⟩
  · exact Or.inl ⟨hq, hshape, Or.inr (Or.inl hbin)⟩
  · exact Or.inl ⟨hq, hshape, Or.inr (Or.inr hfano)⟩
  · exact Or.inr hJ

theorem Concl443B.toPrime {G : Type} [Group G] {T M L K LB VB : Subgroup G}
    (h : Concl443B G T M L K LB VB) : Concl443B' G T M L K LB VB :=
  Concl443BWith.mono (fun hB h3 _ => hB h3) (b := _) h

@[expose] def Insp443' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L B Tp VB K : Subgroup G),
    H13.Ch4.Setting443 G T M L B Tp VB →
    IsUniqueM (perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) ⊔
      (Tp ⊓ Subgroup.normalizer (B : Set G))) M →
    oddCoreIn (Subgroup.normalizer (B : Set G)) ≤ M ⊓ Subgroup.normalizer (B : Set G) →
    K ≤ Subgroup.normalizer (B : Set G) →
    Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (K : Set G) →
    CFSG.IsQuasisimple ↥K → ¬ K ≤ M → VB ≤ K →
    perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) ≤ K →
    Subgroup.normalizer (B : Set G) ⊓ Subgroup.centralizer (K : Set G) =
      oddCoreIn (Subgroup.normalizer (B : Set G)) →
    Concl443B' G T M L K (perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))) VB

end CFSG.Quasithin.H13.Ch4.E443

namespace CFSG.SectionRank.QTK

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Ch4.E443

@[expose] def Insp443List' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L B Tp VB K : Subgroup G),
    CFSG.Quasithin.H13.Ch4.Setting443 G T M L B Tp VB →
    IsUniqueM (perfectCore (conjClosure L T ⊓ centralizer (B : Set G)) ⊔
      (Tp ⊓ normalizer (B : Set G))) M →
    oddCoreIn (normalizer (B : Set G)) ≤ M ⊓ normalizer (B : Set G) →
    K ≤ normalizer (B : Set G) → normalizer (B : Set G) ≤ normalizer (K : Set G) →
    CFSG.IsQuasisimple ↥K → ¬ K ≤ M → VB ≤ K →
    perfectCore (conjClosure L T ⊓ centralizer (B : Set G)) ≤ K →
    normalizer (B : Set G) ⊓ centralizer (K : Set G) = oddCoreIn (normalizer (B : Set G)) →
    QTKSimpleList (↥K ⧸ Subgroup.center ↥K) →
    Concl443B' G T M L K (perfectCore (conjClosure L T ⊓ centralizer (B : Set G))) VB

end CFSG.SectionRank.QTK

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.Quasithin.H13 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.E443

@[expose] def For' (P : (S : Type) → [Group S] → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L B Tp VB K : Subgroup G),
    Hyp G T M L B Tp VB K → P (↥K ⧸ Subgroup.center ↥K) →
    Concl443B' G T M L K (perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))) VB

theorem For.toPrime {P : (S : Type) → [Group S] → Prop} (h : For P) : For' P :=
  fun G _ _ T M L B Tp VB K hH hP => (h G T M L B Tp VB K hH hP).toPrime

theorem For'.mono {P Q : (S : Type) → [Group S] → Prop}
    (h : ∀ (S : Type) [Group S], P S → Q S) (hQ : For' Q) : For' P := by
  intro G _ _ T M L B Tp VB K hH hP
  exact hQ G T M L B Tp VB K hH (h _ hP)

theorem For'.or {P Q : (S : Type) → [Group S] → Prop} (hP : For' P) (hQ : For' Q) :
    For' (fun S _ => P S ∨ Q S) := by
  intro G _ _ T M L B Tp VB K hH h
  rcases h with h' | h'
  · exact hP G T M L B Tp VB K hH h'
  · exact hQ G T M L B Tp VB K hH h'

@[expose] def ConclKWith (b : Prop) (K : Type) [Group K] (L V MK : Subgroup K) : Prop :=
  (CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∧ Shape443 (↥L ⧸ CFSG.pCore 2 ↥L) ∧
    (((∃ _ : IsMulCommutative ↥V,
          IsFFModule (V := ↥V) (autOn (Subgroup.normalizer (V : Set K)) V)) ∧
        (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 → IsNaturalSumUnder 3 L V) ∧
        (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 →
          IsNaturalSumUnder 4 L V ∨
            ∃ _ : IsMulCommutative ↥V, SLExteriorTwo (V := ↥V) (autOn L V) ⊤ ⊥ 4) ∧
        b ∧
        (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 → Nat.card V = 2 ^ 6 →
          ∀ S : Subgroup K, IsSylowTwoOf S L →
            ∃ V₃ : Subgroup K, V₃ ≤ V ∧ Nat.card V₃ = 2 ^ 3 ∧
              S ≤ Subgroup.normalizer (V₃ : Set K) ∧
                ¬ Subgroup.centralizer (V₃ : Set K) ≤ MK)) ∨
      (∃ m : ℕ, 1 ≤ m ∧ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 (2 * m) ∧
        ∃ _ : IsMulCommutative ↥V, BinaryOrthogonalFour (V := ↥V) (autOn L V) ⊤ ⊥ m) ∨
      (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 ∧
        ∃ _ : IsMulCommutative ↥V, FanoCoreModule (V := ↥V) (autOn L V) ⊤ ⊥))) ∨
  (IsSporadic .J4 K ∧
    (IsSporadic .M24 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 5 2 1))

@[expose] def ConclK' (K : Type) [Group K] (L V MK : Subgroup K) : Prop :=
  ConclKWith
    ((Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) ∧
        Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 ∧
        Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
          alternatingGroup (Fin 6))) → Nat.card V = 2 ^ 6 →
      ∀ S : Subgroup K, IsSylowTwoOf S L →
        ∀ z ∈ V ⊓ Subgroup.centralizer (S : Set K), orderOf z = 2 →
          ¬ V ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set K)))
    K L V MK

theorem ConclKWith.mono {b b' : Prop} (hb : b → b') {K : Type} [Group K] {L V MK : Subgroup K}
    (h : ConclKWith b K L V MK) : ConclKWith b' K L V MK := by
  rcases h with ⟨hq, hshape, ⟨hFF, hnat3, hnat4, hB, hU3⟩ | hbin | hfano⟩ | hJ
  · exact Or.inl ⟨hq, hshape, Or.inl ⟨hFF, hnat3, hnat4, hb hB, hU3⟩⟩
  · exact Or.inl ⟨hq, hshape, Or.inr (Or.inl hbin)⟩
  · exact Or.inl ⟨hq, hshape, Or.inr (Or.inr hfano)⟩
  · exact Or.inr hJ

theorem ConclK.toPrime {K : Type} [Group K] {L V MK : Subgroup K} (h : ConclK K L V MK) :
    ConclK' K L V MK :=
  ConclKWith.mono (fun hB h3 _ => hB h3) (b := _) h

end CFSG.SectionRank.QTK.Insp443

end
