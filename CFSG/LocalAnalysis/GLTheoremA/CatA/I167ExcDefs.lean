module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Compl123
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def ExcSmallIdx : TauCeti.CFSGIndex → Prop :=
  fun i => ambiguousChev 2 i ∨ onLie (fun | .suzuki _ => True | .tits => True | _ => False) i

@[expose] def ExcRk2Idx : TauCeti.CFSGIndex → Prop :=
  onLie fun | .G2 q => q.p = 2 | .trialityD4 q => q.p = 2 | .reeF4 _ => True | _ => False

@[expose] def ExcE6Idx : TauCeti.CFSGIndex → Prop :=
  onLie fun | .E6 q => q.p = 2 | _ => False

@[expose] def ExcE6OverIdx (k : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun | .E6 q => q.p = 2 ∧ q.exponent ∣ k | _ => False

@[expose] def ExcE6FourIdx : TauCeti.CFSGIndex → Prop :=
  onLie fun | .E6 q => q.card = 4 | _ => False

@[expose] def ExcParIdx : TauCeti.CFSGIndex → Prop :=
  onLie fun | .F4 q => q.p = 2 | .twistedE6 q => q.p = 2 | .E7 q => q.p = 2 | .E8 q => q.p = 2 | _ => False

@[expose] def ExcBigIdx : TauCeti.CFSGIndex → Prop := fun i => ExcE6Idx i ∨ ExcParIdx i

variable {Ω : Type} [Group Ω] [Finite Ω]

structure ExcHyp (p : ℕ) (B X D J : Subgroup Ω) (x : Ω) : Prop where
  hp : p.Prime
  hp2 : p ≠ 2
  hB : IsElemAbelian p B
  hX : CFSG.Open.IsQuasisimple ↥X
  hchev : IsChevSimple 2 (PSimple p X)
  hBN : B ≤ Subgroup.normalizer (X : Set Ω)
  hrank : GLATwoLocalRank p ↥(X ⊔ B) ≤ CFSG.Open.pRank p B
  hSC : ∀ g ∈ X ⊔ B, g ∈ Subgroup.centralizer (B : Set Ω) → orderOf g = p → g ∈ B
  hcard : Nat.card ↥(B ⊓ cs X) = p
  hD : IsE2 p B D
  hJ : GLAPComponent p (X ⊓ cs D) J
  hDJ : D = B ⊓ cs J
  htype : Type167J p J
  hsplit : HalfSplit16At p X ∨ ∃ d ∈ D, FieldOn p d X
  hxD : x ∈ D
  hxX : x ∉ cs X
  hDx : D = (B ⊓ cs X) ⊔ Subgroup.zpowers x
  hnf : ∀ d ∈ D, ¬ FieldOn p d X
  hhs : HalfSplit16At p X
  hinn : InnDiagOn p (Subgroup.zpowers x) X
  hexc : ¬ catalogIs (PSimple p X) K1419.I1419Classical2

theorem ExcHyp.hJX {p : ℕ} {B X D J : Subgroup Ω} {x : Ω} (H : ExcHyp p B X D J x) : J ≤ X :=
  H.hJ.1.trans inf_le_left

theorem ExcHyp.hxJ {p : ℕ} {B X D J : Subgroup Ω} {x : Ω} (H : ExcHyp p B X D J x) :
    x ∈ Subgroup.centralizer (J : Set Ω) := by
  have hx : x ∈ B ⊓ cs J := H.hDJ ▸ H.hxD
  exact hx.2

theorem ExcHyp.hxB {p : ℕ} {B X D J : Subgroup Ω} {x : Ω} (H : ExcHyp p B X D J x) : x ∈ B :=
  H.hD.1 H.hxD

theorem ExcHyp.hxN {p : ℕ} {B X D J : Subgroup Ω} {x : Ω} (H : ExcHyp p B X D J x) :
    x ∈ Subgroup.normalizer (X : Set Ω) :=
  H.hBN H.hxB

theorem ExcHyp.hxp {p : ℕ} {B X D J : Subgroup Ω} {x : Ω} (H : ExcHyp p B X D J x) : x ^ p = 1 :=
  H.hD.2.1.2 x H.hxD

theorem exc_dispatch {S : Type} [Group S] (hch : IsChevSimple 2 S)
    (hncl : ¬ catalogIs S K1419.I1419Classical2) :
    catalogIs S ExcSmallIdx ∨ catalogIs S ExcRk2Idx ∨ catalogIs S ExcE6Idx ∨ catalogIs S ExcParIdx := by
  rcases hch with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | cyclic _ _ => exact hi.elim
    | alternating _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
    | lie dl =>
      obtain ⟨d, hv⟩ := dl
      have hc : d.characteristic = 2 := hi
      cases d with
      | A r q => exact absurd ⟨.lie ⟨_, hv⟩, ⟨hc, trivial⟩, ⟨e⟩⟩ hncl
      | twistedA r q => exact absurd ⟨.lie ⟨_, hv⟩, ⟨hc, trivial⟩, ⟨e⟩⟩ hncl
      | B r q => exact absurd ⟨.lie ⟨_, hv⟩, ⟨hc, trivial⟩, ⟨e⟩⟩ hncl
      | C r q => exact absurd ⟨.lie ⟨_, hv⟩, ⟨hc, trivial⟩, ⟨e⟩⟩ hncl
      | D r q => exact absurd ⟨.lie ⟨_, hv⟩, ⟨hc, trivial⟩, ⟨e⟩⟩ hncl
      | twistedD r q => exact absurd ⟨.lie ⟨_, hv⟩, ⟨hc, trivial⟩, ⟨e⟩⟩ hncl
      | G2 q =>
        exact Or.inr (Or.inl ⟨.lie ⟨_, hv⟩, (TauCeti.LieTypeIndex.characteristic_G2 q).symm.trans hc, ⟨e⟩⟩)
      | trialityD4 q =>
        exact Or.inr (Or.inl ⟨.lie ⟨_, hv⟩,
          (TauCeti.LieTypeIndex.characteristic_trialityD4 q).symm.trans hc, ⟨e⟩⟩)
      | reeF4 m => exact Or.inr (Or.inl ⟨.lie ⟨_, hv⟩, trivial, ⟨e⟩⟩)
      | F4 q =>
        exact Or.inr (Or.inr (Or.inr ⟨.lie ⟨_, hv⟩,
          (TauCeti.LieTypeIndex.characteristic_F4 q).symm.trans hc, ⟨e⟩⟩))
      | E6 q =>
        exact Or.inr (Or.inr (Or.inl ⟨.lie ⟨_, hv⟩,
          (TauCeti.LieTypeIndex.characteristic_E6 q).symm.trans hc, ⟨e⟩⟩))
      | twistedE6 q =>
        exact Or.inr (Or.inr (Or.inr ⟨.lie ⟨_, hv⟩,
          (TauCeti.LieTypeIndex.characteristic_twistedE6 q).symm.trans hc, ⟨e⟩⟩))
      | E7 q =>
        exact Or.inr (Or.inr (Or.inr ⟨.lie ⟨_, hv⟩,
          (TauCeti.LieTypeIndex.characteristic_E7 q).symm.trans hc, ⟨e⟩⟩))
      | E8 q =>
        exact Or.inr (Or.inr (Or.inr ⟨.lie ⟨_, hv⟩,
          (TauCeti.LieTypeIndex.characteristic_E8 q).symm.trans hc, ⟨e⟩⟩))
      | suzuki m => exact Or.inl ⟨.lie ⟨_, hv⟩, Or.inr trivial, ⟨e⟩⟩
      | tits => exact Or.inl ⟨.lie ⟨_, hv⟩, Or.inr trivial, ⟨e⟩⟩
      | reeG2 m =>
        exfalso
        have h3 : (TauCeti.LieTypeIndex.reeG2 m).characteristic = 3 :=
          TauCeti.LieTypeIndex.characteristic_reeG2 m
        omega
  · exact Or.inl ⟨i, Or.inl hi, ⟨e⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.I167

end
