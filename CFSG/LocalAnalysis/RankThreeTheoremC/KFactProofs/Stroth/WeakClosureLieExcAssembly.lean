module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcMove

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped commutatorElement

variable {τ : Tag}

@[expose] def SylowFrame (τ : Tag) (F : Type) [Field F] [Finite F] (p : ℕ) (w : WeylGroup τ) :
    Prop :=
  ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (Fr : L →+* L) (D : LangDatum τ L),
    (∀ c, Fr c = c ^ Nat.card F) ∧ D.Φ = Units.map (entrywiseHom Fr) ∧
    D.n = canonicalRep (coxeterSystem τ) L w ∧ Nonempty (adjointGroup τ F ≃* D.Γ) ∧
    ∃ S₀ : Sylow p D.Γ, (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ

@[expose] def SylowFrameM (τ : Tag) (F : Type) [Field F] [Finite F] (p : ℕ) (w : WeylGroup τ) :
    Prop :=
  ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (Fr : L →+* L) (D : LangDatum τ L),
    (∀ c, Fr c = c ^ Nat.card F) ∧ D.Φ = Units.map (entrywiseHom Fr) ∧
    D.n = canonicalRep (coxeterSystem τ) L w ∧ D.model ≤ D.Γ ∧
    Nonempty (adjointGroup τ F ≃* D.Γ) ∧
    ∃ S₀ : Sylow p D.Γ, (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ

@[expose] def TorusFpf (τ : Tag) (q p : ℕ) (w u : WeylGroup τ) : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] (Fr : L →+* L), (∀ c, Fr c = c ^ q) →
    ∀ β : Fin τ.rank → Lˣ, rootDiagUnit τ β ∈
      twistedTorusOf (canonicalRep (coxeterSystem τ) L w) (Units.map (entrywiseHom Fr)) →
    rootDiagUnit τ β ^ p = 1 → weylTuple u β = β → rootDiagUnit τ β = 1

@[expose] def TorusFpf2 (τ : Tag) (q p : ℕ) (w u₁ u₂ : WeylGroup τ) : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] (Fr : L →+* L), (∀ c, Fr c = c ^ q) →
    ∀ β : Fin τ.rank → Lˣ, rootDiagUnit τ β ∈
      twistedTorusOf (canonicalRep (coxeterSystem τ) L w) (Units.map (entrywiseHom Fr)) →
    rootDiagUnit τ β ^ p = 1 → weylTuple u₁ β = β → weylTuple u₂ β = β → rootDiagUnit τ β = 1

theorem SylowFrameM.toSylowFrame {F : Type} [Field F] [Finite F] {p : ℕ} {w : WeylGroup τ}
    (h : SylowFrameM τ F p w) : SylowFrame τ F p w := by
  obtain ⟨L, _, _, Fr, D, hFr, hΦ, hn, -, he, hS⟩ := h
  exact ⟨L, inferInstance, inferInstance, Fr, D, hFr, hΦ, hn, he, hS⟩

theorem wcOn_adjoint_of_nm {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] {L : Type}
    [Field L] (D : LangDatum τ L) (e : adjointGroup τ F ≃* D.Γ) (S₀ : Sylow p D.Γ)
    (hnm : NormalizerMovesLines p (S₀ : Subgroup D.Γ)) : WCOn p (adjointGroup τ F) := by
  haveI : Finite (ModGL τ F) := finite_modGL
  haveI : Finite D.Γ := Finite.of_equiv _ e.toEquiv
  exact WCOn.of_mulEquiv e (WCOn.of_normalizerMovesLines S₀ fun _ _ => hnm)

theorem SylowFrame.wcOn_dc {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    {w a b c d : WeylGroup τ} (hF : SylowFrame τ F p w)
    (ha : a ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hb : b ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hc : c ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hd : d ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hfpf : TorusFpf τ (Nat.card F) p w ⁅⁅a, b⁆, ⁅c, d⁆⁆) : WCOn p (adjointGroup τ F) := by
  obtain ⟨L, _, _, Fr, D, hFr, hΦ, hn, ⟨e⟩, S₀, hS₀⟩ := hF
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  refine wcOn_adjoint_of_nm D e S₀ ?_
  refine normalizerMovesLines_of_nfix_dc D hq hFr hΦ hn S₀ hS₀ ha hb hc hd ?_
  intro β hβ hβp hfix
  refine hfpf Fr hFr β ?_ hβp hfix
  rw [torus_eq_twistedTorus D hΦ, hn] at hβ
  exact hβ

theorem SylowFrame.wcOn_dc2 {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    {w a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : WeylGroup τ} (hF : SylowFrame τ F p w)
    (ha₁ : a₁ ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hb₁ : b₁ ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hc₁ : c₁ ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hd₁ : d₁ ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (ha₂ : a₂ ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hb₂ : b₂ ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hc₂ : c₂ ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hd₂ : d₂ ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hfpf : TorusFpf2 τ (Nat.card F) p w ⁅⁅a₁, b₁⁆, ⁅c₁, d₁⁆⁆ ⁅⁅a₂, b₂⁆, ⁅c₂, d₂⁆⁆) :
    WCOn p (adjointGroup τ F) := by
  obtain ⟨L, _, _, Fr, D, hFr, hΦ, hn, ⟨e⟩, S₀, hS₀⟩ := hF
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  refine wcOn_adjoint_of_nm D e S₀ ?_
  refine normalizerMovesLines_of_nfix_dc2 D hq hFr hΦ hn S₀ hS₀ ha₁ hb₁ hc₁ hd₁ ha₂ hb₂ hc₂ hd₂ ?_
  intro β hβ hβp hfix₁ hfix₂
  refine hfpf Fr hFr β ?_ hβp hfix₁ hfix₂
  rw [torus_eq_twistedTorus D hΦ, hn] at hβ
  exact hβ

theorem SylowFrameM.wcOn_c {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    {w a b : WeylGroup τ} (hF : SylowFrameM τ F p w)
    (ha : a ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hb : b ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hfpf : TorusFpf τ (Nat.card F) p w ⁅a, b⁆) : WCOn p (adjointGroup τ F) := by
  obtain ⟨L, _, _, Fr, D, hFr, hΦ, hn, hMΓ, ⟨e⟩, S₀, hS₀⟩ := hF
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  refine wcOn_adjoint_of_nm D e S₀ ?_
  refine normalizerMovesLines_of_nfix_c D hq hFr hΦ hMΓ hn S₀ hS₀ ha hb ?_
  intro β hβ hβp hfix
  refine hfpf Fr hFr β ?_ hβp hfix
  rw [torus_eq_twistedTorus D hΦ, hn] at hβ
  exact hβ

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw
