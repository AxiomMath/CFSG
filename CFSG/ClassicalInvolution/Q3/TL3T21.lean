module

public import CFSG.ClassicalInvolution.Q3.TL3T20
public import CFSG.ClassicalInvolution.Q3.Q3T8P1Seven

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G] [Finite G]

structure ThmDHyp (r : ℕ) (Ω : Set (Subgroup G)) : Prop where
  hyp : HypOmegaGen Ω
  two : ∀ J ∈ Ω, IsPGroup 2 J
  card : ∀ J ∈ Ω, Nat.card J = 2 ^ r
  aEmpty : ∀ J ∈ Ω, AEmpty Ω J
  gen : pSpan Ω = ⊤
  trans : ∀ L ∈ Ω, ∀ L' ∈ Ω, ∃ g : G, conjSub g L = L'
  odd : classicalInvolutionOddCore G = ⊥
  inO2 : ∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u →
    ∃ Q : Subgroup G, Q.Normal ∧ IsPGroup 2 Q ∧ u ∈ Q

@[expose] def ThmDConcl (Ω : Set (Subgroup G)) : Prop :=
  (∀ L ∈ Ω, ∀ L' ∈ Ω, L = L') ∨
    (∃ W : Subgroup G, WSet Ω = {W}) ∨ (∃ E : Subgroup G, E8Struct ⊤ E) ∨
    Nonempty (AEIdentOn Ω 7 AE.e64Sets AE.e64Sub) ∨
    (∃ n : ℕ, 5 ≤ n ∧ Nonempty (AEIdent Ω n)) ∨
    Nonempty (AEIdentOn Ω 8 AE.e29Sets AE.e29Sub)

theorem thmDAbsAt_iff {r : ℕ} :
    ThmDAbsAt r G ↔ ∀ Ω : Set (Subgroup G), ThmDHyp r Ω → ThmDConcl Ω := by
  constructor
  · intro h Ω hD
    exact h Ω hD.hyp hD.two hD.card hD.aEmpty hD.gen hD.trans hD.odd hD.inO2
  · intro h Ω h1 h2 h3 h4 h5 h6 h7 h8
    exact h Ω ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

structure DCex (r : ℕ) (IH : ℕ → Prop) (Ω : Set (Subgroup G)) : Prop extends ThmDHyp r Ω where
  below : ThmDAbsBelow r (Nat.card G)
  ih : IH (Nat.card G)
  not : ¬ ThmDConcl Ω

@[expose] def DStarConn (Ω : Set (Subgroup G)) : Prop :=
  ∀ K ∈ Ω, ∀ J ∈ Ω, J ∈ dstarComp Ω K

end CFSG.ClassicalInvolution.Q3.TC.Thin

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

@[expose] def DLeafZ (r : ℕ) (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), DCex r IH Ω →
    Subgroup.center G = ⊥

@[expose] def DLeafC (r : ℕ) (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), DCex r IH Ω →
    Subgroup.center G = ⊥ → ¬ Disconnected.DConnected Ω

@[expose] def DLeafCls (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), ThmDHyp r Ω →
    Q3CL.ClassicalClause Ω

@[expose] def DLeafE4 (r : ℕ) (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), DCex r IH Ω →
    Subgroup.center G = ⊥ → ¬ Disconnected.DConnected Ω → ∀ W ∈ WSet Ω, ¬ MuIsoE4 Ω W

@[expose] def DLeafStar (r : ℕ) (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), DCex r IH Ω →
    Subgroup.center G = ⊥ → ¬ Disconnected.DConnected Ω → (∀ W ∈ WSet Ω, ¬ MuIsoE4 Ω W) →
      DStarConn Ω

@[expose] def DLeafEnd (r : ℕ) (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), DCex r IH Ω →
    Subgroup.center G = ⊥ → ¬ Disconnected.DConnected Ω → DStarConn Ω →
      (∀ W ∈ WSet Ω, MuIsoS3 Ω W ∨ MuIsoS4 Ω W ∨ MuIsoWylD4 Ω W) → False

variable {G : Type} [Group G] [Finite G]

theorem DCex.mu {r : ℕ} {IH : ℕ → Prop} {Ω : Set (Subgroup G)} (hc : DCex r IH Ω)
    (hcls : Q3CL.ClassicalClause Ω) (hdisc : ¬ Disconnected.DConnected Ω)
    (hstar : DStarConn Ω) : ∀ W ∈ WSet Ω, MuIsoS3 Ω W ∨ MuIsoS4 Ω W ∨ MuIsoWylD4 Ω W := by
  intro W hW
  have hP : Q3T8.Asc77.PartIHyp Ω := ⟨hc.hyp, hcls, hc.aEmpty⟩
  obtain ⟨K, hK, J, hJ, hKJ⟩ : ∃ K ∈ Ω, ∃ J ∈ Ω, J ∉ dComp Ω K := by
    by_contra hcon
    push Not at hcon
    exact hdisc fun K hK J hJ => hcon K hK J hJ
  have hne : dComp Ω K ≠ dstarComp Ω K := by
    intro heq
    apply hKJ
    rw [heq]
    exact hstar K hK J hJ
  exact Q3T8.Asc77.l7_10_proved G Ω hP W hW (Q3T8.Asc77.thompsonGraphAll G Ω hP hK hne hW)

theorem thmDAbsBelow_succ {r : ℕ} {IH : ℕ → Prop} (hZ : DLeafZ r IH) (hC : DLeafC r IH)
    (hcls : DLeafCls r) (hE4 : DLeafE4 r IH) (hstar : DLeafStar r IH) (hend : DLeafEnd r IH)
    {n : ℕ} (hih : IH n) (hb : ThmDAbsBelow r n) : ThmDAbsBelow r (n + 1) := by
  intro G _ _ hG
  rcases Nat.lt_succ_iff_lt_or_eq.mp hG with hlt | heq
  · exact hb G hlt
  rw [thmDAbsAt_iff]
  intro Ω hD
  by_contra hnot
  have hc : DCex r IH Ω := ⟨hD, heq ▸ hb, heq ▸ hih, hnot⟩
  have hz := hZ G Ω hc
  have hdisc := hC G Ω hc hz
  have hcl := hcls G Ω hD
  have hnE4 := hE4 G Ω hc hz hdisc
  have hst := hstar G Ω hc hz hdisc hnE4
  exact hend G Ω hc hz hdisc hst (hc.mu hcl hdisc hst)

theorem thmDAbs_of_leaves {r : ℕ} {IH : ℕ → Prop} (hZ : DLeafZ r IH) (hC : DLeafC r IH)
    (hcls : DLeafCls r) (hE4 : DLeafE4 r IH) (hstar : DLeafStar r IH) (hend : DLeafEnd r IH)
    (hih : ∀ n, IH n) : ThmDAbs r := by
  have hall : ∀ n, ThmDAbsBelow r n := by
    intro n
    induction n with
    | zero => exact fun G _ _ hG => absurd hG (Nat.not_lt_zero _)
    | succ n ih => exact thmDAbsBelow_succ hZ hC hcls hE4 hstar hend (hih n) ih
  intro G _ _
  exact hall (Nat.card G + 1) G (Nat.lt_succ_self _)

end CFSG.ClassicalInvolution.Q3.TC.Thin
