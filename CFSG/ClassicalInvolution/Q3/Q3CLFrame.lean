module

public import CFSG.ClassicalInvolution.Q3.Q3CLStd

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G]

structure Std8Frame (Ω : Set (Subgroup G)) (K J : Subgroup G) (S : Sylow 2 G) (R T W : Subgroup G)
    (z t : G) : Prop where
  hyp : HypOmegaGen Ω
  mem : K ∈ Ω
  trans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J
  noTwins : ∀ K' ∈ twinSet Ω K, K' = K
  hz : IsUniqueInvolution K z
  hJ : J ∈ omegaNbr Ω K
  ht : IsUniqueInvolution J t
  hR : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)
  hT : T ∈ RSet Ω ∧ T ≤ J ∧ T ≤ (S : Subgroup G)
  hW : W ∈ WSet Ω ∧ W ≤ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), conjSub s W = W

variable {Ω : Set (Subgroup G)} {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem Std8Core.toFrame (hs : Std8Core Ω K J S R T W z t) : Std8Frame Ω K J S R T W z t :=
  ⟨hs.stand.hyp, hs.stand.mem, hs.stand.trans, hs.noTwins, hs.hz, hs.hJ, hs.ht, hs.hR, hs.hT,
    hs.hW⟩

end CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem AscStand.toCore (h : AscStand p f Ω K) : T8R.Loc.AscStandCore p f Ω K :=
  ⟨h.odd, h.five, h.hyp, h.aEmpty, h.mem, h.trans⟩

theorem Std8.toStd8Core (hs : Std8 p f Ω K J S R T W z t) : T8R.Loc.Std8Core p f Ω K J S R T W z t :=
  ⟨hs.stand.toCore, hs.noTwins, hs.hz, hs.hJ, hs.ht, hs.hR, hs.hT, hs.hW⟩

theorem T8R.Loc.Std8Core.toFrame (hs : T8R.Loc.Std8Core p f Ω K J S R T W z t) :
    Std8Frame Ω K J S R T W z t :=
  hs.toGen.toFrame

theorem Std8.toFrame (hs : Std8 p f Ω K J S R T W z t) : Std8Frame Ω K J S R T W z t :=
  hs.toStd8Core.toFrame

end CFSG.ClassicalInvolution.Asc77
