module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFFusion
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B69Comp
public import CFSG.GroupTheory.ABGLocalTools.Constraint

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

variable {G : Type*} [Group G]

@[expose] def FFConclusion (M T V : Subgroup G) : Prop :=
  ∃ hU : IsElemAbelian 2 V, IsTwoReducedIn M V ∧
    ∃ I : Finset (Subgroup (MulAut (IntMod V hU))),
      IsSylowTwoOf (autI hU (thompsonJ T)) (autI hU (thompsonJ M)) ∧
      autI hU (thompsonJ M) = ⨆ L ∈ I, L ∧
      (∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) ∧
      (∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥) ∧
      (∀ L ∈ I, ActsAsNaturalL2 L (commV L)) ∧
      fixV (autI hU (thompsonJ M)) ⊔ ⨆ L ∈ I, commV L = ⊤ ∧
      fixV (autI hU (thompsonJ M)) ⊓ ⨆ L ∈ I, commV L = ⊥ ∧
      (∀ L ∈ I, commV L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), commV L' = ⊥) ∧
      (∀ g ∈ autI hU M, ∀ L ∈ I, B1.conjAut g L ∈ I ∧
        (commV L).map g.toMonoidHom = commV (B1.conjAut g L))

@[expose] def AGL81I59 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T V : Subgroup G), IsKGroup ↥M → CharTwo M →
    IsSylowTwoOf T M → V = conjClosure (quasithinOmegaOneCenter T) M →
    CFSG.ABGLocalTools.IsPConstrained 3 ↥(autOn M V) →
    ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) → FFConclusion M T V

theorem ffConclusion_of_solvable [Finite G] {M T V : Subgroup G} (hF : CharTwo M)
    (hsolv : Group.IsSolvable ↥(autOn M V)) (hT : IsSylowTwoOf T M)
    (hV : V = conjClosure (quasithinOmegaOneCenter T) M)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) : FFConclusion M T V := by
  obtain ⟨hU, hred, hcase, -⟩ := B2_16_of_quot hF hsolv hT hV
  rcases hcase with ⟨hJ', -⟩ | ⟨-, I, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  · exact absurd hJ' hJ
  · exact ⟨hU, hred, I, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem exists_family_of_ffConclusion [Finite G] {M T V : Subgroup G}
    (hT : IsSylowTwoOf T M) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (h : FFConclusion M T V) :
    ∃ hU : IsElemAbelian 2 V, M ≤ Subgroup.normalizer (V : Set G) ∧
      ∃ I : Finset (Subgroup (MulAut (IntMod V hU))), I.Nonempty ∧
        (∀ L ∈ I, Nat.card L = 6) ∧ autI hU (thompsonJ M) = ⨆ L ∈ I, L ∧
        IsSylowTwoOf (autI hU (thompsonJ T)) (autI hU (thompsonJ M)) ∧
        (∀ g ∈ autI hU M, ∀ L ∈ I, B1.conjAut g L ∈ I) ∧ S3Family I := by
  obtain ⟨hU, hred, I, hSyl, hI, hcomm, -, hnat, htop, -, hinter, hperm⟩ := h
  have hMN : M ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hne : I.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    have hbot : autI hU (thompsonJ M) = ⊥ := by simpa using hI
    have hJM : thompsonJ M ≤ Subgroup.centralizer (V : Set G) :=
      (autI_eq_bot_iff hU ((thompsonJ_le_self M).trans hMN)).1 hbot
    exact hJ ((thompsonJ_le_thompsonJ_of_isSylowTwoOf hT).trans hJM)
  have hcard : ∀ L ∈ I, Nat.card L = 6 := by
    intro L hL
    obtain ⟨e, -⟩ := hnat L hL
    rw [Nat.card_congr e.toEquiv]
    exact B69.card_sl2
  refine ⟨hU, hMN, I, hne, hcard, hI, hSyl, fun g hg L hL => (hperm g hg L hL).1,
    ⟨hcomm, hinter, ?_, hnat⟩⟩
  rw [← hI]
  exact htop

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
