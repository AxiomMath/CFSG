module

public import CFSG.LocalAnalysis.GLTheoremA.Exc

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def excIndex : TauCeti.CFSGIndex → Prop
  | .alternating n _ => n = 6 ∨ n = 7
  | .sporadic s => s = .M22
  | .lie i =>
    match i.1 with
    | .A 2 q => q.card % 9 = 4 ∨ q.card % 9 = 7
    | .twistedA 2 q => q.card % 9 = 2 ∨ q.card % 9 = 5
    | _ => False
  | _ => False

@[expose] def clubIndex (i : TauCeti.CFSGIndex) : Prop :=
  excIndex i ∨
    match i with
    | .alternating n _ => n = 5
    | .lie j =>
      match j.1 with
      | .A 1 q => q.card % 3 ≠ 0 ∧ q.card % 9 ≠ 1 ∧ q.card % 9 ≠ 8
      | _ => False
    | _ => False

variable {G : Type} [Group G] [Finite G]

@[expose] def IsExcType (p : ℕ) (K : Subgroup G) : Prop :=
  p = 3 ∧ Nat.card (Subgroup.center (PQuot p K)) = 3 ∧ catalogIs (PSimple p K) excIndex

@[expose] def IsClubType (p : ℕ) (K : Subgroup G) : Prop :=
  p = 3 ∧ Nat.card (Subgroup.center (PQuot p K)) = 1 ∧ catalogIs (PSimple p K) clubIndex

theorem catalogIs_congr {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    {Q : TauCeti.CFSGIndex → Prop} : catalogIs S Q ↔ catalogIs S' Q :=
  ⟨fun ⟨i, hi, ⟨f⟩⟩ => ⟨i, hi, ⟨e.symm.trans f⟩⟩, fun ⟨i, hi, ⟨f⟩⟩ => ⟨i, hi, ⟨e.trans f⟩⟩⟩

theorem nonempty_pSimple_congr {p : ℕ} {K K' : Subgroup G} (e : PQuot p K ≃* PQuot p K') :
    Nonempty (PSimple p K ≃* PSimple p K') :=
  ⟨QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)⟩

theorem card_center_pQuot_congr {p : ℕ} {K K' : Subgroup G} (e : PQuot p K ≃* PQuot p K') :
    Nat.card (Subgroup.center (PQuot p K)) = Nat.card (Subgroup.center (PQuot p K')) :=
  Nat.card_congr (Subgroup.centerCongr e).toEquiv

theorem isExcType_congr {p : ℕ} {K K' : Subgroup G} (h : Nonempty (PQuot p K ≃* PQuot p K')) :
    IsExcType p K ↔ IsExcType p K' := by
  obtain ⟨e⟩ := h
  obtain ⟨f⟩ := nonempty_pSimple_congr e
  unfold IsExcType
  rw [card_center_pQuot_congr e, catalogIs_congr f]

theorem isClubType_congr {p : ℕ} {K K' : Subgroup G} (h : Nonempty (PQuot p K ≃* PQuot p K')) :
    IsClubType p K ↔ IsClubType p K' := by
  obtain ⟨e⟩ := h
  obtain ⟨f⟩ := nonempty_pSimple_congr e
  unfold IsClubType
  rw [card_center_pQuot_congr e, catalogIs_congr f]

theorem not_isClubType_of_isExcType {p : ℕ} {K : Subgroup G} (h : IsExcType p K) :
    ¬ IsClubType p K := fun h' => by
  have := h.2.1.symm.trans h'.2.1
  omega

theorem card_center_of_isExcType {p : ℕ} {K : Subgroup G} (h : IsExcType p K) :
    Nat.card (Subgroup.center (PQuot p K)) = p := h.1 ▸ h.2.1

@[expose] def I1131At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (y : G) (K : Subgroup G), GLAIsBmax p B → IsEssential p B y →
    GLAPComponent p (Subgroup.centralizer ({y} : Set G)) K →
    ¬ B ≤ Subgroup.normalizer (K : Set G) → IsExcType p K

@[expose] def I1411At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (X K : Subgroup G) (y : G), GLAPComponent p X K → y ^ p = 1 →
    y ∈ Subgroup.normalizer (K : Set G) →
    ∀ J : Subgroup G, GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set G)) J →
      IsClubType p K → IsClubType p J

@[expose] def I1122At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (y : G) (K : Subgroup G) (b : G), GLAIsBmax p B → IsEssential p B y →
    GLAPComponent p (Subgroup.centralizer ({y} : Set G)) K → b ∈ B →
    b ∉ Subgroup.normalizer (K : Set G) →
    ∀ J : Subgroup G, GLAPComponent p (closureIn K B ⊓ Subgroup.centralizer ({b} : Set G)) J →
      IsClubType p J

@[expose] def I1122IsoAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (y : G) (K : Subgroup G) (b : G), GLAIsBmax p B → IsEssential p B y →
    GLAPComponent p (Subgroup.centralizer ({y} : Set G)) K → b ∈ B →
    b ∉ Subgroup.normalizer (K : Set G) →
    ∀ J : Subgroup G, GLAPComponent p (closureIn K B ⊓ Subgroup.centralizer ({b} : Set G)) J →
      Nonempty (PQuot p J ≃* PSimple p K)

theorem excClubHyp_of {p : ℕ} (h1131 : I1131At G p) (h1411 : I1411At G p)
    (h1122 : I1122At G p) : ExcClubHyp G p (IsExcType p) (IsClubType p) where
  exc_congr _ _ h := isExcType_congr h
  club_congr _ _ h := isClubType_congr h
  not_club_of_exc _ h := not_isClubType_of_isExcType h
  card_center_of_exc _ h := card_center_of_isExcType h
  exc_of_not_le := h1131
  club_down := h1411
  club_diag := h1122

end CFSG.LocalAnalysis.GLTheoremA
