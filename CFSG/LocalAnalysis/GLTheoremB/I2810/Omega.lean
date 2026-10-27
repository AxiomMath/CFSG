module

public import CFSG.LieType.ChevTwo.Defs
import CFSG.LocalAnalysis.GLTheoremB.I2810.OmegaAux
import CFSG.LocalAnalysis.GLTheoremB.I2810.OmegaSmall
import CFSG.LocalAnalysis.GLTheoremB.I2810.OmegaFinal
import CFSG.LocalAnalysis.GLTheoremB.I2810.OmegaPrim
public import CFSG.LocalAnalysis.GLTheoremB.I2810.OmegaHeart
import CFSG.LocalAnalysis.GLTheoremB.I2810.OmegaCard
import CFSG.LocalAnalysis.GLTheoremB.I2810.Heart
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaFour
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Bridge

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open CFSG.LieType.ChevTwo
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

section CaseOneTwo
open CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem omega_n_two (h : Setup28 W K S) (hR : Red28 W K S) (h1 : Hyp28One W K S) {a : X}
    {U₁ U₂ : Subgroup X} (hm : OmegaModel W K a U₁ U₂) :
    ∃ n : ℕ, 2 ≤ n ∧ OmegaAny W K a U₁ U₂ n := by
  obtain ⟨n, hn1, hΩ⟩ := hm
  by_cases hn : 2 ≤ n
  · exact ⟨n, hn, hΩ⟩
  exfalso
  obtain rfl : n = 1 := by omega
  rcases hΩ with hp | hmi
  · obtain ⟨θ, t, hθs, hθW, -⟩ := hp
    haveI := OmegaSmall.solvable_plus_two
    haveI := OmegaSmall.nontrivial_plus_two
    exact not_subsingleton _
      (OmegaSmall.subsingleton_of_perfect_solvable (InducedAux.commutator_K h) θ hθs)
  · obtain ⟨θ, t, hθs, hθW, -⟩ := hmi
    let e := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedOmega_quadMinus_two_mulEquiv_alt5
    refine OmegaAux.false_of_alt_quotient hR h1 (m := 5) le_rfl (e.toMonoidHom.comp θ)
      (e.surjective.comp hθs) fun k hk => ?_
    simp only [MonoidHom.comp_apply, hθW k hk, map_one]

theorem alt_not_hyp1 (h : Setup28 W K S) (hR : Red28 W K S) (h1 : Hyp28One W K S) {a : X}
    {U₁ U₂ : Subgroup X} (hm : AltModel W K a U₁ U₂) : False := by
  obtain ⟨m, θ, σ, hm5, hθs, hθW, -⟩ := hm
  exact OmegaAux.false_of_alt_quotient hR h1 hm5 θ hθs hθW

theorem coatom_cent_plus (n : ℕ) (hn : 2 ≤ n) (t : GL (Fin (n + 1) ⊕ Fin (n + 1)) (ZMod 2))
    (ht : IsTransvection t) (hQt : ∀ x, StatedQuadPlus (n + 1) (ZMod 2)
      (Matrix.mulVec (t : Matrix _ _ (ZMod 2)) x) = StatedQuadPlus (n + 1) (ZMod 2) x)
    (htn : t ∈ Subgroup.normalizer (StatedOmega (StatedQuadPlus (n + 1) (ZMod 2)) : Set _))
    (H : Subgroup (GL (Fin (n + 1) ⊕ Fin (n + 1)) (ZMod 2)))
    (hHΩ : H ≤ StatedOmega (StatedQuadPlus (n + 1) (ZMod 2)))
    (hHC : ∀ g ∈ StatedOmega (StatedQuadPlus (n + 1) (ZMod 2)), t * g * t⁻¹ = g → g ∈ H)
    (hH : ∃ g ∈ H, t * g * t⁻¹ ≠ g) : H = StatedOmega (StatedQuadPlus (n + 1) (ZMod 2)) := by
  obtain ⟨v, f, hv, hf, hfv, htx⟩ := ht
  exact OmegaPrim.coatom_matrix (CFSG.LieType.Universal.Spin.quadPlus (n + 1) (ZMod 2)) _
    (CFSG.LieType.Universal.Spin.coe_quadPlus (n + 1) (ZMod 2))
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus (n + 1) (ZMod 2))
    (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
    (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedOmega_quadPlus_eq_map_elementaryGroup
      (K := ZMod 2) (m := n + 1) (by omega))
    t v f hv hf hfv htx hQt H hHΩ hHC hH

theorem coatom_cent_minus (n : ℕ) (hn : 2 ≤ n)
    (t : GL (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2) (ZMod 2)) (ht : IsTransvection t)
    (hQt : ∀ x, StatedQuadMinus (n + 1) (ZMod 2) 1 1 (Matrix.mulVec (t : Matrix _ _ (ZMod 2)) x) =
      StatedQuadMinus (n + 1) (ZMod 2) 1 1 x)
    (htn : t ∈ Subgroup.normalizer (StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1) : Set _))
    (H : Subgroup (GL (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2) (ZMod 2)))
    (hHΩ : H ≤ StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1))
    (hHC : ∀ g ∈ StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1), t * g * t⁻¹ = g → g ∈ H)
    (hH : ∃ g ∈ H, t * g * t⁻¹ ≠ g) : H = StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1) := by
  obtain ⟨v, f, hv, hf, hfv, htx⟩ := ht
  exact OmegaPrim.coatom_matrix (CFSG.LieType.Universal.Spin.quadMinus (n + 1) (ZMod 2) 1 1) _
    (CFSG.LieType.Universal.Spin.coe_quadMinus (n + 1) (ZMod 2) 1 1)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (n + 1) (ZMod 2)
      CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.irreducible_one_one)
    (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
    (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedOmega_quadMinus_eq_map_elementaryGroup
      (K := ZMod 2) (m := n + 1) (by omega))
    t v f hv hf hfv htx hQt H hHΩ hHC hH

theorem omega_final (h : Setup28 W K S) (hR : Red28 W K S) {U₁ U₂ : Subgroup X}
    (sf : SingleFactor K (vOf W K S) U₁ U₂)
    (hE : ∀ k ∈ K, ∀ w ∈ kerAct W K S, ⁅k, w⁆ ∈ vOf W K S)
    (hZ : Subgroup.center ↥(bar W K) = ⊥) (hS2 : Nat.card ↥(indAut W K S) = 2)
    (hblock : IsGLBlock (⊤ : Subgroup X) K) {a : X} (haS : a ∈ S) (hna : a ∉ kerAct W K S) {n : ℕ}
    (hΩ : OmegaAny W K a U₁ U₂ n) :
    Concl28aWith (StatedQuadPlus (n + 1) (ZMod 2)) W K S ∨
      Concl28aWith (StatedQuadMinus (n + 1) (ZMod 2) 1 1) W K S := by
  rcases hΩ with hp | hmi
  · exact Or.inl (OmegaFinal.concl_of_model _ h hR sf hE hZ hS2 hblock haS hna hp)
  · exact Or.inr (OmegaFinal.concl_of_model _ h hR sf hE hZ hS2 hblock haS hna hmi)

section Variants

theorem c1_cardS_of_one_le (hL1 : OmegaTwoAutTwoPart) (h : Setup28 W K S) (hR : Red28 W K S)
    (h1 : Hyp28One W K S) {A : Subgroup X} (hA : Off28 W K S A)
    (hc : Nat.card ↥(indAut W K A) = 2) {a : X} {U₁ U₂ : Subgroup X} {n : ℕ} (hn : 1 ≤ n)
    (hΩ : OmegaAny W K a U₁ U₂ n) : Nat.card ↥(indAut W K S) = 2 :=
  OmegaCard.c1_cardS_aux hL1 h hR h1 hA hc hn hΩ

theorem omega_three_plus (n : ℕ) (hn : 2 ≤ n) : OmegaHeart.Three (StatedQuadPlus (n + 1) (ZMod 2)) := by
  intro t ht hQt
  obtain ⟨v, f, hv, hf, hfv, htx⟩ := ht
  exact OmegaPrim.three_matrix (CFSG.LieType.Universal.Spin.quadPlus (n + 1) (ZMod 2)) _
    (CFSG.LieType.Universal.Spin.coe_quadPlus (n + 1) (ZMod 2))
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus (n + 1) (ZMod 2))
    (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
    (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedOmega_quadPlus_eq_map_elementaryGroup
      (K := ZMod 2) (m := n + 1) (by omega))
    t v f hv hf hfv htx hQt

theorem omega_three_minus (n : ℕ) (hn : 2 ≤ n) :
    OmegaHeart.Three (StatedQuadMinus (n + 1) (ZMod 2) 1 1) := by
  intro t ht hQt
  obtain ⟨v, f, hv, hf, hfv, htx⟩ := ht
  exact OmegaPrim.three_matrix (CFSG.LieType.Universal.Spin.quadMinus (n + 1) (ZMod 2) 1 1) _
    (CFSG.LieType.Universal.Spin.coe_quadMinus (n + 1) (ZMod 2) 1 1)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (n + 1) (ZMod 2)
      CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.irreducible_one_one)
    (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
    (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedOmega_quadMinus_eq_map_elementaryGroup
      (K := ZMod 2) (m := n + 1) (by omega))
    t v f hv hf hfv htx hQt

theorem centMax_of_omega_of_centre (h : Setup28 W K S) (hR : Red28 W K S) {a : X}
    {U₁ U₂ : Subgroup X} (hts : TransSection K (vOf W K S) U₁ U₂ a)
    (hZ : Subgroup.center ↥(bar W K) = ⊥) (haS : a ∈ S) (hna : a ∉ kerAct W K S)
    (hS2 : Nat.card ↥(indAut W K S) = 2) {n : ℕ} (hn : 2 ≤ n) (hΩ : OmegaAny W K a U₁ U₂ n) :
    CentMax W K S a := by
  have hS2' := S_cases h haS hna hS2
  rcases hΩ with hp | hmi
  · exact OmegaHeart.centMax_of_model _ (fun t ht hQ htn H hHΩ hHC hH =>
      coatom_cent_plus n hn t ht hQ htn H hHΩ hHC hH) h hR hts.toSingleFactor hZ haS hna hS2' hp
  · exact OmegaHeart.centMax_of_model _ (fun t ht hQ htn H hHΩ hHC hH =>
      coatom_cent_minus n hn t ht hQ htn H hHΩ hHC hH) h hR hts.toSingleFactor hZ haS hna hS2' hmi

theorem threeElt_of_omega_of_centre (h : Setup28 W K S) (hR : Red28 W K S) {a : X}
    {U₁ U₂ : Subgroup X} (hts : TransSection K (vOf W K S) U₁ U₂ a)
    (hZ : Subgroup.center ↥(bar W K) = ⊥) (haS : a ∈ S) {n : ℕ} (hn : 2 ≤ n)
    (hΩ : OmegaAny W K a U₁ U₂ n) : ThreeElt W K S a := by
  rcases hΩ with hp | hmi
  · exact OmegaHeart.threeElt_of_model _ (omega_three_plus n hn) h hR hts.toSingleFactor hZ haS hp
  · exact OmegaHeart.threeElt_of_model _ (omega_three_minus n hn) h hR hts.toSingleFactor hZ haS hmi

end Variants

end CaseOneTwo

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810
