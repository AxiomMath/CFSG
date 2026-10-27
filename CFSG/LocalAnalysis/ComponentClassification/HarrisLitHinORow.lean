module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinOCore
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSpOdd
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinCls
public import CFSG.LocalAnalysis.ComponentClassification.EvenOrthSelector

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open Subgroup Module QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.OddClassSelector
open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare (orthogonalOmega)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem hinConcl_orth_model {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y] {K : Type}
    [Field K] [Finite K] {d ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (hd : 7 ≤ d) {Q : QuadraticForm K (Fin d → K)}
    (hQ : Q.polarBilin.Nondegenerate) (hP : ThreePairs Q)
    (hd8 : d = 8 → (∃ U : Submodule K (Fin d → K), finrank K U = 4 ∧ ∀ x ∈ U, Q x = 0) ∨
      ∀ x ∈ orthogonalOmega Q, ∀ r : K, (∀ v, x v = r • v) → x = 1)
    (hrep : CatalogueBOrthogonalInvolutionRepresentation.SemilinearRepresentation Q)
    (θ : Y ≃* matrixProjectiveDerived Q) {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (h16 : 16 ∣ p ^ (2 * m) - 1) {τ : MulAut Y} (hτ : orderOf τ = 2)
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m) :
    HinConcl Y p m τ := by
  classical
  set α := MulAut.congr θ τ with hαdef
  have hcomm0 : ∀ x, θ (τ x) = α (θ x) := fun x => by
    rw [hαdef, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  have hfix0 : (fixedPoints τ).map θ.toMonoidHom = fixedSubgroup α := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change α (θ x) = θ x
      rw [← hcomm0, show τ x = x from hx]
    · intro hy
      refine ⟨θ.symm y, ?_, by simp⟩
      change τ (θ.symm y) = θ.symm y
      apply θ.injective
      rw [hcomm0, MulEquiv.apply_symm_apply]
      exact hy
  have hτ2 : τ * τ = 1 := by
    have := pow_orderOf_eq_one τ
    rwa [hτ, pow_two] at this
  have hα2 : α * α = 1 := by rw [hαdef, ← map_mul, hτ2, map_one]
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hτ
    norm_num at hτ
  have hα1 : α ≠ 1 := fun h => hτ1 ((MulAut.congr θ).injective (by rw [← hαdef, h, map_one]))
  have hX0 : CFSG.Assembly.IsComponentOf ((GSThmB.layerIn (fixedPoints τ)).map θ.toMonoidHom)
      (fixedSubgroup α) := by
    rw [← hfix0]
    exact SymmetricLocal.isComponentOf_map_of_injective _ θ.injective (isComponentOf_layerIn hL)
  have hs0 : SmallSource ((GSThmB.layerIn (fixedPoints τ)).map θ.toMonoidHom) :=
    smallSource_of_mulEquiv ((GSThmB.layerIn (fixedPoints τ)).equivMapOfInjective _ θ.injective)
      (smallSource_layerIn hp hp2 hm h16 hL)
  obtain ⟨β, g, hβg, hσ2, ⟨c, hc⟩, hlin, -⟩ := hrep.2 α hα2 hα1
  have hX := isComponentOf_map_symm β hX0
  rw [hβg] at hX
  have hs := smallSource_of_mulEquiv
    (((GSThmB.layerIn (fixedPoints τ)).map θ.toMonoidHom).equivMapOfInjective
      (MulEquiv.symm β).toMonoidHom (MulEquiv.symm β).injective) hs0
  set ε : Y ≃* matrixProjectiveDerived Q := θ.trans (MulEquiv.symm β) with hεdef
  have hfix : (fixedPoints τ).map ε.toMonoidHom =
      fixedSubgroup (matrixProjectiveConjugationHom Q g) := by
    rw [← hβg, ← map_symm_fixedSubgroup, ← hfix0, Subgroup.map_map]
    rfl
  rcases orth_rank_of_component hℓ hℓ2 he hK hd hQ hP hd8 hrep.1 g hσ2 c hc hlin hX hs with
    ⟨E, hE, hE2, hE16⟩ | ⟨hout, E, hE, hE2, hE8⟩
  · exact hinConcl_of_rank
      (fun _ => not_sectionalTwoRankLE_of_equiv ε hfix hE hE2 (by omega))
      (fun _ => not_sectionalTwoRankLE_of_equiv ε hfix hE hE2 (by omega))
  · refine hinConcl_of_rank (fun hin => ?_)
      (fun _ => not_sectionalTwoRankLE_of_equiv ε hfix hE hE2 (by omega))
    exfalso
    obtain ⟨y, hy⟩ := hin
    apply hout
    refine ⟨β.symm (θ y), ?_⟩
    rw [← hβg]
    refine MulEquiv.ext fun z => ?_
    simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]
    rw [hαdef, MulAut.congr_apply, ← hy]
    simp

theorem hinFor_orthogonal_odd : HinFor fun Y _ => ∃ (t : Assembly.LowTwoRank.StatedLieTag)
    (n ℓ f : ℕ), ℓ ≠ 2 ∧ (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) ∧
      Assembly.LowTwoRank.StatedClassicalModel Y t n ℓ f := by
  intro Y _ _ _ ⟨t, n, ℓ, f, hℓ2, ht, h⟩ hnab p m hp hp2 hm h16 _ τ hτ hL
  have hrepM :=
    CatalogueBOrthogonalInvolutionRepresentation.odd_orthogonal_involution_semilinear_representation
      t ht h
  rcases ht with rfl | rfl | rfl
  · obtain ⟨⟨hℓ, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := id h
    obtain ⟨-, hnd, -⟩ := CatalogueBOrthogonalPointData.coordinate_model_witness_odd h K hK e
    exact hinConcl_orth_model hℓ hℓ2 hf hK (by omega) hnd (threePairs_coordinateQuadOdd K hn)
      (fun h8 => absurd h8 (by omega)) (hrepM K hK e)
      (CatalogueBOrthogonalPointData.coordinateOddWitnessEquiv K e) hp hp2 hm h16 hτ hL
  · obtain ⟨⟨hℓ, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := id h
    obtain ⟨-, hnd, -⟩ := CatalogueBOrthogonalPointData.coordinate_model_witness_plus h K hK e
    refine hinConcl_orth_model hℓ hℓ2 hf hK (by omega) hnd
      (threePairs_coordinateQuadPlus K (by omega)) (fun h8 => Or.inl ?_) (hrepM K hK e)
      (CatalogueBOrthogonalPointData.coordinatePlusWitnessEquiv K e) hp hp2 hm h16 hτ hL
    obtain ⟨U, hU, hUQ⟩ := exists_totallySingular_coordinateQuadPlus n hnd
    exact ⟨U, by omega, hUQ⟩
  · obtain ⟨⟨hℓ, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id h
    have hn1 : 1 ≤ n := by omega
    have : CharP K ℓ := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      hℓ hf hK
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K ℓ]; exact hℓ2)
    obtain ⟨-, hnd, -⟩ :=
      CatalogueBOrthogonalPointData.coordinate_model_witness_minus h K hK b c hirr e
    refine hinConcl_orth_model hℓ hℓ2 hf hK (by omega) hnd
      (threePairs_coordinateQuadMinus K hn b c) (fun h8 => Or.inr ?_)
      (hrepM hn1 K hK b c hirr e)
      (CatalogueBOrthogonalPointData.coordinateMinusWitnessEquiv K hn1 b c e) hp hp2 hm h16 hτ hL
    obtain rfl : n = 4 := by omega
    exact omega_scalar_trivial_minus h2 hirr

theorem hinFor_orthogonal_even : HinFor fun Y _ => ∃ (t : Assembly.LowTwoRank.StatedLieTag)
    (n f : ℕ), (t = .POmegaPlus ∨ t = .POmegaMinus) ∧
      Assembly.LowTwoRank.StatedClassicalModel Y t n 2 f := by
  intro Y _ _ _ ⟨t, n, f, ht, h⟩ hnab p m hp hp2 hm h16 _ τ hτ hL
  exfalso
  have := finite_mulAut (Y := Y)
  obtain ⟨eW, hWn, -, -, hWC, hLW⟩ := autSocle hnab
  have hZ : center Y = ⊥ := CatLeaf.center_eq_bot_of_simple hnab
  have hcomp := isComponentOf_map_conj_layer hZ hL
  have hLCW := LocalAnalysis.ComponentInitial.isComponentOf_of_le hcomp
    (le_inf (hLW τ) hcomp.1) inf_le_right
  have hn : 4 ≤ n := by
    rcases ht with rfl | rfl
    · exact h.1.2.2
    · exact h.1.2.2
  obtain ⟨K, _, _, Q, hK, hQ, hT, hE, hconj, ⟨θ⟩⟩ :=
    EvenOrthSelector.exists_coordinate_witness ht h
  exact EvenOrthSelector.false_of_coordinate hWC hτ hLCW
    (smallSource_layerMap hZ hp hp2 hm h16 hL) h.1.2.1 hK hn hQ hT hE hconj (eW.symm.trans θ)

theorem hinFor_orthogonal : HinFor fun Y _ => ∃ (t : Assembly.LowTwoRank.StatedLieTag)
    (n ℓ f : ℕ), (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) ∧
      Assembly.LowTwoRank.StatedClassicalModel Y t n ℓ f := by
  intro Y _ _ _ ⟨t, n, ℓ, f, ht, h⟩
  by_cases hℓ : ℓ = 2
  · subst hℓ
    rcases ht with rfl | rfl | rfl
    · exact (h.1.2.2.2 rfl).elim
    · exact hinFor_orthogonal_even Y ⟨_, n, f, Or.inl rfl, h⟩
    · exact hinFor_orthogonal_even Y ⟨_, n, f, Or.inr rfl, h⟩
  · exact hinFor_orthogonal_odd Y ⟨t, n, ℓ, f, hℓ, ht, h⟩

theorem hinFor_classicalRep :
    HinFor fun Y _ => Milestones.ClassicalRep Y :=
  hinFor_classicalRep_of_rows hinFor_symplectic_odd hinFor_orthogonal

end CFSG.ComponentClassification.HarrisLit.Hin
