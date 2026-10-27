module

public import CFSG.HardMathSupport.Dickson.Bal207.CompShapeOn
public import CFSG.HardMathSupport.Dickson.Bal207.D4EightField
public import CFSG.HardMathSupport.Dickson.Bal207.D4EightUniform
public import CFSG.HardMathSupport.Dickson.Bal207.SU38Frame
import all CFSG.HardMathSupport.Dickson.Bal207.CompShapeW
import CFSG.HardMathSupport.Dickson.Bal207.SU38Exc

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux CFSG.HardMathSupport.Dickson.I271
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

@[expose] def NotNineteenDvdCard (Q : Type) [Group Q] : Prop := ¬ 19 ∣ Nat.card Q

theorem isoInvariant_notNineteenDvdCard : IsoInvariant NotNineteenDvdCard := by
  intro Q Q' _ _ e h h'
  exact h (by rwa [Nat.card_congr e.toEquiv])

theorem compShape_notNineteenDvdCard_field {S : Type} [Group S] {F₀ : Type} [Field F₀]
    [Finite F₀] (hF₀ : Nat.card F₀ = 8)
    (e₀ : S ≃* StatedProj (StatedOmega (StatedQuadPlus 4 F₀))) {β : MulAut S} (hβ : β ^ 3 = 1)
    (hout : ∀ a : S, MulAut.conj a ≠ β)
    (hE : MulAut.congr (coordinatePlusWitnessEquiv F₀ e₀) β ∈
      CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixProjectiveImage
        (coordinateQuadPlus 4 F₀)) :
    CompShape NotNineteenDvdCard β := by
  obtain ⟨hl, J, hJ, hZ, hM⟩ := d4Eight_field_comps hF₀ e₀ hβ hout hE
  refine ⟨hl, fun L hL => ?_, fun ω hω L hL => ?_⟩
  · obtain rfl := hJ L hL
    have hcard : Nat.card ↥L = CFSG.Open.ordD 4 (2 ^ 1) :=
      (CFSG.Timmesfeld.card_statedClassicalModel_two hM).2.2.2.1 rfl
    show ¬ 19 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L)
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).toEquiv, hcard]
    decide
  · exact (hJ _ (isComponentOf_map_of_commute_w hω hL)).trans (hJ L hL).symm

theorem not_isSU38Comp_of_outer {X : Type} [Group X] [Finite X] {K B : Subgroup X}
    (hK : IsLieQuot ↥K IsD4EightIdx) (hN : NoTrialityOn NonSemilinD4Eight B K)
    (hB : ∀ b ∈ B, b ^ 3 = 1) {a : X} (haB : a ∈ B) (ha : a ∈ Subgroup.normalizer (K : Set X))
    (hout : ∀ s, MulAut.conj s ≠ actHom K ⟨a, ha⟩) {J : Subgroup X}
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J) : ¬ IsSU38Comp J := by
  intro hsu
  obtain ⟨F₀, _, _, hF₀, ⟨e₀⟩⟩ := exists_d4Eight_model hK
  have hβ : actHom K ⟨a, ha⟩ ∈ autImage B K := mem_autImage.2 ⟨a, ha, haB, rfl⟩
  have hβ3 : actHom K ⟨a, ha⟩ ^ 3 = 1 := by
    have ha3 : (⟨a, ha⟩ : Subgroup.normalizer (K : Set X)) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hB a haB)
    rw [← map_pow, ha3, map_one]
  have hE := mulAut_congr_mem_image_of_noTrialityOn hN hB hF₀
    (coordinatePlusWitnessEquiv F₀ e₀) hβ
  have hS := compShape_notNineteenDvdCard_field hF₀ e₀ hβ3 hout hE
  obtain ⟨-, h19, -⟩ := compShapeOn_lift isoInvariant_notNineteenDvdCard Nat.prime_three ha
    (hS.compShapeOn 3 ⊤) hJ
  exact h19 (nineteen_dvd_card_quot_of_isSU38Comp hsu)

theorem su38FrameD4_of_inner
    (hInner : ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (K B A : Subgroup X),
      Bal207PlusCtx NonSemilinD4Eight 3 K B A → IsLieQuot ↥K IsD4EightIdx →
      NoTrialityOn NonSemilinD4Eight B K → Bal207PlusIH NonSemilinD4Eight A →
      ∀ a ∈ A, a ≠ 1 → ∀ (ha : a ∈ Subgroup.normalizer (K : Set X))
        (s : ↥K ⧸ Subgroup.center ↥K), MulAut.conj s = actHom K ⟨a, ha⟩ → ∀ J : Subgroup X,
        GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J → IsSU38Comp J →
          B ≤ Subgroup.normalizer (J : Set X) → SU38FrameConclusion B J) :
    SU38FrameD4 NonSemilinD4Eight := by
  intro X _ _ hKG K B A ctx hK hN hIH a haA ha1 J hJ hsu hBJ
  have haB : a ∈ B := ctx.le haA
  by_cases hin : ∃ s, MulAut.conj s = actHom K ⟨a, ctx.norm haB⟩
  · obtain ⟨s, hs⟩ := hin
    exact hInner X hKG K B A ctx hK hN hIH a haA ha1 (ctx.norm haB) s hs J hJ hsu hBJ
  · push Not at hin
    exact absurd hsu (not_isSU38Comp_of_outer hK hN (fun b hb => ctx.scp.2.1.2 b hb) haB
      (ctx.norm haB) hin hJ)

end CFSG.HardMathSupport.Dickson.Bal207

end
