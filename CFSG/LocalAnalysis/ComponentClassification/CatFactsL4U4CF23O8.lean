module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovL4U4O8Core
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CF23Wit
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthFamily
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Neg
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Base

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation
open CFSG.ComponentClassification.OddClassSelector

theorem o8_socle_false {H : Type} [Group H] {W : Subgroup H} [W.Normal]
    (hCW : centralizer (W : Set H) = ⊥) {a : H} (ha : orderOf a = 2) {L : Subgroup H}
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a}))
    (hstd : CFSG.IsStandardSubgroup L) (hs : SmallSource L) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hexc : ¬ LieModel (↥L ⧸ center ↥L) .PSL 2 p (2 * (2 * f)))
    (hM : LieModel W .POmegaMinus 4 p f) : False := by
  classical
  have hW := OddClassSelector.statedClassicalModel_of_lieModel hM
    (by simp [chevalleyExceptionalTags]) (by simp [reeTitsTags]) (by decide)
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id hW
  obtain ⟨-, hnd, -⟩ := coordinate_model_witness_minus hW K hK b c hirr e
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaMinus
    (Or.inr (Or.inr rfl)) hW (by norm_num) K hK b c hirr e
  have h14 : 1 ≤ 4 := by norm_num
  set θ := coordinateMinusWitnessEquiv K h14 b c e with hθ
  have : IsSimpleGroup W :=
    (ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaMinus W 4 p f hW).2
  have : IsSimpleGroup (matrixProjectiveDerived
      (coordinateQuadMinus 4 K h14 b c)) := θ.symm.isSimpleGroup
  have hnab : ∃ x y : matrixProjectiveDerived (coordinateQuadMinus 4 K h14 b c),
      x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    have hWle : W ≤ centralizer (W : Set H) := by
      intro w hw
      rw [mem_centralizer_iff]
      intro v hv
      have h1 := hcon (θ ⟨v, hv⟩) (θ ⟨w, hw⟩)
      rw [← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (θ.injective h1)
    rw [hCW] at hWle
    obtain ⟨x, hx⟩ := exists_ne (1 : W)
    apply hx
    exact Subtype.ext (mem_bot.mp (hWle x.2))
  have hZ := OutcomeLocal.center_eq_bot_of_isSimpleGroup hnab
  obtain ⟨ρ, X, hinj, hinn, hX, hLX, ⟨eLX⟩⟩ := fixed_component_of_socle hCW θ hZ hLCW
  have hNT := noTightWitness_of_isStandardSubgroup hinj hinn (conj_injective hZ) hstd hLX
  have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  have hαα : ρ a * ρ a = 1 := by
    rw [← map_mul, ← pow_two, ha2, map_one]
  have hα1 : ρ a ≠ 1 := by
    intro h1
    have h2 : orderOf (ρ a) = orderOf a := orderOf_injective ρ hinj a
    rw [h1, orderOf_one, ha] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨β, g, hβg, hσ2, ⟨c', hc'⟩, hlin, -⟩ := hrep.2 (ρ a) hαα hα1
  have hX₁ := isComponentOf_map_symm β hX
  rw [hβg] at hX₁
  let eL := eLX.trans (X.equivMapOfInjective β.symm.toMonoidHom β.symm.injective)
  obtain ⟨E', _, _, hE', ⟨eE⟩⟩ := GSThmB.Cov.orth_core_minus8 hp hp2 hf hK (d := 2 * 4)
    (by norm_num) hnd
    (fun ⟨U, hU, hUQ⟩ => Catalog7Std.Om8.not_isPlusType_coordinateQuadMinus 4 (by norm_num) hirr
      ⟨U, by rw [hU, Module.finrank_fin_fun], hUQ⟩)
    g hσ2 c' hc' hlin hX₁ (smallSource_of_mulEquiv eL hs) (hNT.map β.symm)
  apply hexc
  have hE : Nat.card E' = p ^ (2 * (2 * f)) := by
    rw [hE', hK, ← pow_mul]
    congr 1
    ring
  have hodd : Odd (p ^ (2 * (2 * f))) := (hp.odd_of_ne_two hp2).pow
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have h9 : 9 ≤ p ^ (2 * (2 * f)) :=
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      _ ≤ p ^ (2 * (2 * f)) := Nat.pow_le_pow_right hp.pos (by omega)
  have hm := OddSelector.statedClassicalModel_psl_two hp (by omega) hE
    (fun h2 => by rw [h2] at hodd; exact (Nat.not_odd_iff_even.mpr even_two) hodd) (by omega)
  exact LieType.CurtisTits.lieModel_of_mulEquiv
    (((QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)).trans eE).trans
      (projectiveSpecialLinearGroupEquivStatedProj 2 E')).symm (Or.inl ⟨by decide, hm⟩)

theorem cf23InnerFusionFor_POmegaMinus8 :
    CF23InnerFusionFor fun Y _ => ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      LieModel Y .POmegaMinus 4 p f := by
  intro G _ _ N hN hC hτ α J hα hJN hJα hJ hstd hsm hZ hexc
  exfalso
  obtain ⟨p, f, hp, hp2, hf, hM⟩ := hτ
  have := hN
  exact o8_socle_false hC hα (isComponentOf_of_cf23 hJN hJα hJ) hstd (smallSource_of_cf23 hsm hZ)
    hp hp2 hf (fun h => hexc (Or.inr (Or.inl ⟨p, 2 * f, hp, hp2, by omega, h,
      Or.inr (Or.inr (Or.inl ⟨f, rfl, hM⟩))⟩))) hM

end CFSG.ComponentClassification.GSThmB.CF23I
