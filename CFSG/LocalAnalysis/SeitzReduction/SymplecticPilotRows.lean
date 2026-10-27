module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR8RootTorus
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCoresModel

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

inductive Sp2mKind
  | field
  | swap
  | linearEven
  | unitaryEven
  | linearOdd
  | unitaryOdd
  | omegaPlus
  | omegaMinus
  deriving DecidableEq

@[expose] def Sp2mKindType (S : Type) [Group S] (m f : ℕ) : Sp2mKind → Prop
  | .field => LieModel S .PSp m 2 (2 * f)
  | .swap => False
  | .linearEven => LieModel S .PSL (2 * m) 2 f
  | .unitaryEven => LieModel S .PSU (2 * m) 2 f
  | .linearOdd => LieModel S .PSL (2 * m + 1) 2 f
  | .unitaryOdd => LieModel S .PSU (2 * m + 1) 2 f
  | .omegaPlus => LieModel S .POmegaPlus (m + 1) 2 f
  | .omegaMinus => LieModel S .POmegaMinus (m + 1) 2 f

theorem exists_sp2mKindType_of_sp2mOvergroupType {S : Type} [Group S] {m f : ℕ}
    (h : Sp2mOvergroupType S m f) : ∃ κ : Sp2mKind, κ ≠ .swap ∧ Sp2mKindType S m f κ := by
  rcases h with h | h | h | h | h | h | h
  · exact ⟨.field, by decide, h⟩
  · exact ⟨.linearEven, by decide, h⟩
  · exact ⟨.unitaryEven, by decide, h⟩
  · exact ⟨.linearOdd, by decide, h⟩
  · exact ⟨.unitaryOdd, by decide, h⟩
  · exact ⟨.omegaPlus, by decide, h⟩
  · exact ⟨.omegaMinus, by decide, h⟩

theorem sp2mOvergroupType_of_sp2mKindType {S : Type} [Group S] {m f : ℕ} {κ : Sp2mKind}
    (h : Sp2mKindType S m f κ) : Sp2mOvergroupType S m f := by
  cases κ
  · exact Or.inl h
  · exact h.elim
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem sp2mKindType_of_mulEquiv {S S' : Type} [Group S] [Group S'] (φ : S ≃* S') {m f : ℕ}
    {κ : Sp2mKind} (h : Sp2mKindType S m f κ) : Sp2mKindType S' m f κ := by
  cases κ
  · exact LieType.CurtisTits.lieModel_of_mulEquiv φ h
  · exact h.elim
  all_goals exact LieType.CurtisTits.lieModel_of_mulEquiv φ h

theorem not_sp2mKindType_two_omegaPlus {S : Type} [Group S] {f : ℕ} :
    ¬ Sp2mKindType S 2 f .omegaPlus := fun h => by
  have := (F4Pilot.statedLieAdmissible_of_lieModel h).2.2
  simp at this

theorem not_sp2mKindType_two_omegaMinus {S : Type} [Group S] {f : ℕ} :
    ¬ Sp2mKindType S 2 f .omegaMinus := fun h => by
  have := (F4Pilot.statedLieAdmissible_of_lieModel h).2.2
  simp at this

section Kinds

variable {Y : Type} [Group Y]

@[expose] def NeighbourOvergroupSp2mKind (s : Y) (D : Subgroup Y) (m f : ℕ) (κ : Sp2mKind) :
    Prop :=
  ∃ Kc : Subgroup Y, IsComponent Kc ∧ D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
    ((κ ≠ .swap ∧ Kc.map (MulAut.conj s).toMonoidHom = Kc ∧ D < Kc ∧ s ∉ Kc ∧
        ∃ hsN : s ∈ normalizer (Kc : Set Y),
          Sp2mOvergroup Kc (Kc.normalizerMonoidHom ⟨s, hsN⟩) m f ∧
            Sp2mKindType (Kc ⧸ center Kc) m f κ) ∨
      (κ = .swap ∧ Kc.map (MulAut.conj s).toMonoidHom ≠ Kc ∧
        ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥ ∧ Nonempty (Kc ⧸ center Kc ≃* D)))

theorem exists_neighbourOvergroupSp2mKind {s : Y} {D : Subgroup Y} {m f : ℕ}
    (h : NeighbourOvergroupSp2m s D m f) : ∃ κ : Sp2mKind, NeighbourOvergroupSp2mKind s D m f κ := by
  obtain ⟨Kc, hKc, hDK, h1 | h2⟩ := h
  · obtain ⟨hfix, hlt, hsK, hsN, hov⟩ := h1
    obtain ⟨κ, hκ, hty⟩ := exists_sp2mKindType_of_sp2mOvergroupType hov.2.2.1
    exact ⟨κ, Kc, hKc, hDK, .inl ⟨hκ, hfix, hlt, hsK, hsN, hov, hty⟩⟩
  · exact ⟨.swap, Kc, hKc, hDK, .inr ⟨rfl, h2⟩⟩

theorem NeighbourOvergroupSp2mKind.neighbourOvergroupSp2m {s : Y} {D : Subgroup Y} {m f : ℕ}
    {κ : Sp2mKind} (h : NeighbourOvergroupSp2mKind s D m f κ) : NeighbourOvergroupSp2m s D m f := by
  obtain ⟨Kc, hKc, hDK, ⟨-, hfix, hlt, hsK, hsN, hov, -⟩ | ⟨-, h2⟩⟩ := h
  · exact ⟨Kc, hKc, hDK, .inl ⟨hfix, hlt, hsK, hsN, hov⟩⟩
  · exact ⟨Kc, hKc, hDK, .inr h2⟩

end Kinds

section Root

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

@[expose] def HR8KindAtSp (t : G) (m f : ℕ) (X D : Subgroup G) (κ : Sp2mKind) : Prop :=
  ∃ htX : t ∈ centralizer (X : Set G),
    NeighbourOvergroupSp2mKind (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) m f κ

@[expose] def RootKindSp {n : ℕ} (e : L ≃* StatedSp n K) (t : G) (f : ℕ) (k : Fin n)
    (κ : Sp2mKind) : Prop :=
  HR8KindAtSp t (n - 1) f (modelToG e (rootTorusSp K k)) (modelToG e (complSp K k)) κ

theorem exists_hr8KindAtSp_of_neighbourOvergroupSp2m {t : G} {m f : ℕ} {X D : Subgroup G}
    (htX : t ∈ centralizer (X : Set G))
    (h : NeighbourOvergroupSp2m (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) m f) :
    ∃ κ : Sp2mKind, HR8KindAtSp t m f X D κ := by
  obtain ⟨κ, hκ⟩ := exists_neighbourOvergroupSp2mKind h
  exact ⟨κ, htX, hκ⟩

theorem exists_rootKindSp [Finite G] {n f : ℕ} (hcat : Sp2mCatalogueClausesAt (n - 1))
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hn : 3 ≤ n)
    (e : L ≃* StatedSp n K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (k : Fin n) : ∃ κ : Sp2mKind, RootKindSp e t f k κ := by
  obtain ⟨htX, h⟩ := neighbour_overgroup_rootTorusSp_of_three_le hcat hset hKc hf hn e htC ht k
    (X := modelToG e (rootTorusSp K k)) rfl (D := modelToG e (complSp K k)) rfl
  exact exists_hr8KindAtSp_of_neighbourOvergroupSp2m htX h

end Root

end CFSG.SeitzReduction.SymplecticPilot
