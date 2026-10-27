module

public import CFSG.HardMathSupport.Dickson.Bal207.CompShapeOn
public import CFSG.HardMathSupport.Dickson.Bal207.D4EightField
public import CFSG.HardMathSupport.Dickson.Bal207.D4EightUniform
public import CFSG.HardMathSupport.Dickson.Bal207.Glue
public import CFSG.Open.GriessAllModelsStatement
import CFSG.HardMathSupport.Dickson.Bal207.D4Eight

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux CFSG.HardMathSupport.Dickson.I271
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

theorem CompShapeOn.mono {p : ℕ} {T : ∀ (Q : Type) [Group Q], Prop} {S : Type} [Group S]
    {H H' : Subgroup (MulAut S)} {β : MulAut S} (h : CompShapeOn p T H β) (hle : H' ≤ H) :
    CompShapeOn p T H' β :=
  ⟨h.layer, h.type, fun ω hω => h.norm ω (hle hω), h.moved⟩

theorem center_eq_bot_of_d4Eight {S : Type} [Group S] {F₀ : Type} [Field F₀] [Finite F₀]
    (e₀ : S ≃* StatedProj (StatedOmega (StatedQuadPlus 4 F₀))) : Subgroup.center S = ⊥ := by
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus 4 F₀ (by norm_num)
  obtain ⟨hsimp, a, b, hab⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonalSubfield.matrix_simple_nonabelian (by norm_num : 0 < 2 * 4)
      hnd hT
  let ψ := coordinatePlusWitnessEquiv F₀ e₀
  have : IsSimpleGroup S := ψ.isSimpleGroup
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S)).resolve_right
    fun htop => hab ?_
  have h1 : ψ.symm a ∈ Subgroup.center S := htop ▸ Subgroup.mem_top _
  exact ψ.symm.injective (by rw [map_mul, map_mul]; exact (Subgroup.mem_center_iff.1 h1 _).symm)

theorem orderOf_eq_three_of_conj {S : Type} [Group S] (hZ : Subgroup.center S = ⊥) {s : S}
    (h1 : MulAut.conj s ≠ 1) (h3 : MulAut.conj s ^ 3 = 1) : orderOf s = 3 := by
  have hinj : ∀ g : S, MulAut.conj g = 1 → g = 1 := by
    intro g hg
    have hc : g ∈ Subgroup.center S := Subgroup.mem_center_iff.2 fun x => by
      have h := congrArg (fun φ : MulAut S => φ x) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc x * g = g * x * g⁻¹ * g := by rw [h]
        _ = g * x := by group
    rw [hZ] at hc
    exact Subgroup.mem_bot.1 hc
  have hs3 : s ^ 3 = 1 := hinj _ (by rw [map_pow, h3])
  have hs1 : s ≠ 1 := fun h => h1 (by rw [h, map_one])
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime hs3 hs1

theorem bal207PlusFamD4Eight_of_inner (hGA : GriessAllModelsStatement)
    (hInner : ∀ (S : Type) [Group S] (F₀ : Type) [Field F₀] [Finite F₀], Nat.card F₀ = 8 →
      ∀ (e₀ : S ≃* StatedProj (StatedOmega (StatedQuadPlus 4 F₀))) (s : S), orderOf s = 3 →
        CompShapeOn 3 D4EightCompType ((matrixProjectiveImage (coordinateQuadPlus 4 F₀)).comap
          (MulAut.congr (coordinatePlusWitnessEquiv F₀ e₀)).toMonoidHom) (MulAut.conj s)) :
    Bal207PlusFamD4Eight NonSemilinD4Eight := by
  intro X _ _ hKG K B A ctx hK hN hIH
  obtain ⟨F₀, _, _, hF₀, ⟨e₀⟩⟩ := exists_d4Eight_model hK
  have hB : ∀ b ∈ B, b ^ 3 = 1 := fun b hb => ctx.scp.2.1.2 b hb
  have hBH : autImage B K ≤ (matrixProjectiveImage (coordinateQuadPlus 4 F₀)).comap
      (MulAut.congr (coordinatePlusWitnessEquiv F₀ e₀)).toMonoidHom := fun φ hφ =>
    mulAut_congr_mem_image_of_noTrialityOn hN hB hF₀ _ hφ
  refine bal207PlusFamClauses_of_compShapeOn_b2 ctx isoInvariant_d4EightCompType hBH ?_ ?_ ?_
  · intro β hβ hβ1
    have hβ3 : β ^ 3 = 1 := by
      obtain ⟨b, hbN, hbB, rfl⟩ := mem_autImage.1 hβ
      have hb3 : (⟨b, hbN⟩ : Subgroup.normalizer (K : Set X)) ^ 3 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow]; exact hB b hbB)
      rw [← map_pow, hb3, map_one]
    by_cases hin : ∃ s, MulAut.conj s = β
    · obtain ⟨s, rfl⟩ := hin
      exact hInner _ F₀ hF₀ e₀ s (orderOf_eq_three_of_conj (center_eq_bot_of_d4Eight e₀) hβ1 hβ3)
    · push Not at hin
      exact (compShape_d4Eight_field hF₀ e₀ hβ3 hin (hBH hβ)).compShapeOn 3 _
  · have hcop := d4Eight_coprime_center hGA ctx.comp.2.2 hK
    exact fun h => (by norm_num : (3 : ℕ) ≠ 1) (Nat.Coprime.eq_one_of_dvd hcop h)
  · intro a haA ha1 J hJ hcomp hTJ hsmall hBJ
    obtain ⟨d, hd, hJd⟩ := hTJ
    rcases hd with hi | hi | hi
    · exact Glue.stronglyLocallyOneBalanced_of_ih ctx hIH haA ha1 hJ hcomp.2.2 hBJ
        (Glue.bal207PlusHyp_of_isLieQuot
          (Glue.isLieQuot_subgroupOf (hJ.1.trans inf_le_right) ⟨d, hi, hJd⟩))
    · exact absurd (Or.inr (Or.inl ⟨d, hi, hJd⟩)) hsmall
    · exact absurd (Or.inr (Or.inr ⟨d, hi, hJd⟩)) hsmall

end CFSG.HardMathSupport.Dickson.Bal207

end
