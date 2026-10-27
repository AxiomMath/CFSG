module

public import CFSG.CGT.PushingUpLit.A78.Sp4Frame
public import CFSG.Timmesfeld.Transvection.GenerateFrameLarge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExterior
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.CGT.PushingUpLit.A78

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

@[expose] def NoSU4Abelian : Prop :=
  ∀ {G : Type} [Group G] {f : ℕ}, 1 ≤ f →
    ∀ Φ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (2 * 2)) →* G,
      Function.Surjective Φ → Φ.ker = Subgroup.center _ →
        ∃ E : Subgroup G, (∀ x ∈ E, ∀ y ∈ E, Commute x y) ∧ (∀ x ∈ E, x * x = 1) ∧
          2 ^ (3 * f) < Nat.card E

variable {G : Type} [Group G] [Finite G] {Z : Subgroup G} {e : ℕ}

theorem Sp4Local.sp4_endgame (h : Sp4Local G Z e) (hL1 : SylowOppositeSL2) (hS1 : SylowCountSL2)
    (hL3 : NoSU4Abelian) : Nonempty (G ≃* StatedSp 2 (GaloisField 2 e)) := by
  obtain ⟨P, Q, hfr⟩ := h.exists_smallFrame hL1 hS1
  obtain ⟨f, hf, hcard, hconc⟩ := transvectionStatementFrameLarge G (zClass Z)
    (h.transvectionHyp hL1) (h.meetsLines hS1) (fun A hA => h.four_le_card_member hA) 2 le_rfl
    P Q 0 hfr
  have hfe : f = e :=
    Nat.pow_right_injective (le_refl 2) ((hcard Z (self_mem_zClass Z)).symm.trans h.card)
  subst hfe
  rcases hconc with ⟨Φ, hΦ, -⟩ | ⟨Φ, hΦs, hker, -⟩
  · exact ⟨(MulEquiv.ofBijective Φ hΦ).symm⟩
  · exfalso
    obtain ⟨E, hEc, hEs, hEcard⟩ := hL3 hf Φ hΦs hker
    have := h.abelian_le E hEc hEs
    omega

section Bridge

open CFSG.Assembly.RankThreeEven (projSp)

noncomputable def sp4StatedEquivProjSp (k : Type) [Field k] [CharP k 2] :
    StatedSp 2 k ≃* projSp 2 k :=
  (CFSG.ComponentClassification.UnbalancedCatalog.SpChain.projSpEquiv k).trans
    (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk (StatedSp 2 k))

theorem Sp4Local.sp4_endgame_projSp (h : Sp4Local G Z e) (hL1 : SylowOppositeSL2)
    (hS1 : SylowCountSL2) (hL3 : NoSU4Abelian) :
    Nonempty (G ≃* CFSG.Assembly.RankThreeEven.projSp 2 (GaloisField 2 e)) := by
  obtain ⟨φ⟩ := h.sp4_endgame hL1 hS1 hL3
  exact ⟨φ.trans (sp4StatedEquivProjSp (GaloisField 2 e))⟩

end Bridge

end CFSG.CGT.PushingUpLit.A78
