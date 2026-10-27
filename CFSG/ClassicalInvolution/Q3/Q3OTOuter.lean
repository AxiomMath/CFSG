module

public import CFSG.ClassicalInvolution.Q3.Q3OTBase
public import CFSG.ClassicalInvolution.Q3.Q3NMRows
public import CFSG.ClassicalInvolution.Q3.Q3TY14
public import CFSG.ClassicalInvolution.Q3.Q3TY13
public import CFSG.ClassicalInvolution.Q3.Q3TWY1
public import CFSG.ClassicalInvolution.ModelFacts.TG3OrthTags
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinModel
public import CFSG.ClassicalInvolution.Q3.Q3NMOrth
public import CFSG.ClassicalInvolution.Q3.Q3TIRed
public import CFSG.ClassicalInvolution.Q3.Q3VF4Row
public import CFSG.LieType.Chevalley.E7SupportedBruhat

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OT

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.G2D4Models.Twin (LiftSimFr)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1


section Transport

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}

theorem twinOuterAlphaOn_of_spin3 (hodd : Odd (Nat.card F)) (hF3 : Nat.card F = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q)
    (hker2 : ∀ x ∈ (spinAction Q).ker, x * x = 1) (hV : 7 ≤ Module.finrank F (ι → F))
    (hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    (hlift : ∀ (H : Type) [Group H] [Finite H] (ψ : spinGroup Q →* H),
      ψ.ker ≤ Subgroup.center (spinGroup Q) → LiftSimFr Q ψ)
    {t : StatedLieTag} (D : UniversalRootDatum (spinGroup Q))
    (cq : CentralQuot3 (spinAction Q) (fundamentalSubgroups t D) (fundSet Q)
      (scalars F (ι → F)))
    (hinn : ∀ (H : Type) [Group H] [Finite H] (ψ : spinGroup Q →* H),
      ψ.ker ≤ Subgroup.center (spinGroup Q) → AutOddFreeInner ↥ψ.range)
    (hnc : ∀ R ∈ fundamentalSubgroups t D, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1) :
    TwinOuterAlphaOn t ⟨spinGroup Q, D⟩ := by
  intro H _ _ ψ R R' x x' hpair v hvR hvR' hy2 hy1 hyz
  classical
  have : Nontrivial (ι → F) := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have hZ3 := center_no_three hF3 hrange hZ hker2
  have hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1 := fun r hr h1 => cq.inj R hpair.mem r hr h1
  have hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1 := fun r hr h1 =>
    cq.inj R' hpair.mem' r hr h1
  obtain ⟨fr, hF₁, hF₁', hθx, -⟩ := Q3TY.swap_of_twin_pair3 hodd hrange hZ hproj
    (cq.map_inj hpair.mem hpair.mem') (cq.map_mem R hpair.mem) (cq.map_mem R' hpair.mem') hinj
    hinj' hpair.ne hpair.hx hpair.hx2 hpair.hx1 hpair.hx' hpair.hx'2 hpair.hx'1 ψ hpair.ker
    hpair.same
  have hv' : ∀ s : spinGroup Q, spinAction Q s ∈ fr.La.range ⊔ fr.swap.La.range →
      v * spinInd ψ s = spinInd ψ s * v := by
    intro s hs
    rw [← hF₁, ← hF₁'] at hs
    exact commute_spinInd_of_mem_map_sup (ker_spinAction_le_center Q) ψ v hvR hvR' hs
  have hα : ∀ s : spinGroup Q, spinAction Q s ∈ fr.La.range ⊔ fr.swap.La.range →
      ∀ g : ↥ψ.range, (v : MulAut ↥ψ.range) (ψ.rangeRestrict s * g * (ψ.rangeRestrict s)⁻¹) =
        ψ.rangeRestrict s * (v : MulAut ↥ψ.range) g * (ψ.rangeRestrict s)⁻¹ := by
    intro s hs g
    have h := congrArg (fun g' : ↥(inducedAutOn ψ.range) => ((g' : MulAut ↥ψ.range) g : ↥ψ.range))
      (hv' s hs)
    exact Subtype.ext (congrArg Subtype.val h)
  have hθk : ψ.rangeRestrict.ker ≤ Subgroup.center (spinGroup Q) :=
    ker_rangeRestrict_le ψ hpair.ker
  have hsq := sq_mem_inn_abs hodd hF3 hQ hrange hZ3 hV fr ψ.rangeRestrict_surjective hθk
    (v : MulAut ↥ψ.range) (hlift ↥ψ.range ψ.rangeRestrict hθk) hα
  have hxn : ψ x ∈ Subgroup.normalizer (ψ.range : Set H) := FrameVertex.mem_normalizer_range ψ x
  have hxL : ψ x ∈ ψ.range := ⟨x, rfl⟩
  have hb2 : FrameVertex.innerHom ψ x * FrameVertex.innerHom ψ x = 1 := by
    rw [← map_mul, hpair.hx2, map_one]
  have hvb : v * FrameVertex.innerHom ψ x = FrameVertex.innerHom ψ x * v := hvR x hpair.hx
  have hab : v * v * FrameVertex.innerHom ψ x = FrameVertex.innerHom ψ x * (v * v) := by
    rw [mul_assoc, hvb, ← mul_assoc, hvb, mul_assoc]
  have hb1 : FrameVertex.innerHom ψ x ≠ 1 := by
    intro h1
    apply hpair.hx1
    apply hnc R hpair.mem x hpair.hx
    refine mem_center_of_commutators_central fun y => hpair.ker ?_
    have h2 : ((FrameVertex.innerHom ψ x : ↥(inducedAutOn ψ.range)) : MulAut ↥ψ.range) = 1 :=
      congrArg (fun z : ↥(inducedAutOn ψ.range) => (z : MulAut ↥ψ.range)) h1
    have h3 := congrArg (fun φ : MulAut ↥ψ.range => ((φ (ψ.rangeRestrict y) : ↥ψ.range) : H)) h2
    simp only [MulAut.one_apply] at h3
    have h4 : ψ x * ψ y * (ψ x)⁻¹ = ψ y := h3
    rw [MonoidHom.mem_ker]
    show ψ (x * y * x⁻¹ * y⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h4, mul_inv_cancel]
  exact alphaOf_klein_inner3 ψ.range (hinn H ψ hpair.ker) hy2 hb2 hab hb1 hsq
    (toInducedAutOn_mem_innSubgroup ψ.range (ψ x) hxn hxL)

end Transport

section Tags

theorem twinOuterAlpha3_odd {n : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n 3 1) :
    TwinOuterAlpha 3 1 .POmegaOdd n := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hodd := ModelFacts.TG3.odd_natCard_galoisField_three
  have hF3 := ModelFacts.TG3.natCard_galoisField_three
  have h2 : (2 : 𝔽₃) ≠ 0 := ModelFacts.TG3.two_ne_zero_three
  have hdim : Module.finrank 𝔽₃ (Fin n ⊕ Fin n ⊕ Unit → 𝔽₃) = 2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  have : Group.IsPerfect (spinGroup (quadOdd n 𝔽₃)) := isPerfect_spinGroup_quadOdd h2 hn3
  have hD4 : ¬ (StatedLieTag.POmegaOdd = .POmegaPlus ∧ n = 4) := fun h => by cases h.1
  have hT : StatedLieTag.POmegaOdd ≠ .trialityD4 := by decide
  show TwinOuterAlphaOn .POmegaOdd ⟨spinGroup (quadOdd n 𝔽₃), oddDatum n 𝔽₃⟩
  exact twinOuterAlphaOn_of_spin3 hodd hF3 (nondegenerate_polarBilin_quadOdd n _ h2)
    (range_spinAction_quadOdd h2 hn3) (centerScalar_quadOdd h2 hn3)
    (ModelFacts.OrthAut.odd_hker2 h2 n) (by omega) (fun F₁ F₂ h => ModelFacts.TG3.hproj_odd F₁ F₂ h)
    (fun H _ _ ψ hψ =>
      liftSimFr_of_liftSim (liftSim_quadOdd (p := 3) (e := 1) (by norm_num) hn3 le_rfl ψ hψ)) _
    (Q3TWY.centralQuot3_odd hn3)
    (fun H _ _ ψ hψ => autOddFreeInnerTag_of_not_D4 hD4 hT hp trivial hadm ↥ψ.range
      ψ.rangeRestrict ψ.rangeRestrict_surjective (ker_rangeRestrict_le ψ hψ))
    (fun R hR r hr hrc => fund_noncentral_modelUniv (p := 3) (e := 1) (t := .POmegaOdd)
      (n := n) trivial hadm (by simp) R hR r hr hrc)

theorem twinOuterAlpha3_plus {n : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n 3 1)
    (hn5 : 5 ≤ n) : TwinOuterAlpha 3 1 .POmegaPlus n := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hodd := ModelFacts.TG3.odd_natCard_galoisField_three
  have hF3 := ModelFacts.TG3.natCard_galoisField_three
  have hdim : Module.finrank 𝔽₃ (Fin n ⊕ Fin n → 𝔽₃) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have : Group.IsPerfect (spinGroup (quadPlus n 𝔽₃)) := isPerfect_spinGroup_quadPlus hn3
  have hD4 : ¬ (StatedLieTag.POmegaPlus = .POmegaPlus ∧ n = 4) := fun h => by omega
  have hT : StatedLieTag.POmegaPlus ≠ .trialityD4 := by decide
  have hnc := fund_noncentral_modelUniv (p := 3) (e := 1) (t := .POmegaPlus) (n := n) trivial hadm
    (by simp)
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus n 𝔽₃), plusDatum n 𝔽₃ hn3⟩ →
      (∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, ∀ r ∈ R, r ∈ Subgroup.center M.K → r = 1) →
      (∀ (H : Type) [Group H] [Finite H] (ψ : M.K →* H), ψ.ker ≤ Subgroup.center M.K →
        AutOddFreeInner ↥ψ.range) → TwinOuterAlphaOn .POmegaPlus M := by
    intro M hM hnc' hinn
    subst hM
    exact twinOuterAlphaOn_of_spin3 hodd hF3 (nondegenerate_polarBilin_quadPlus n _)
      (range_spinAction_quadPlus hn3) (centerScalar_quadPlus hn3) (ModelFacts.OrthAut.plus_hker2 n)
      (by omega) (fun F₁ F₂ h => ModelFacts.TG3.hproj_plus hn5 F₁ F₂ h)
      (fun H _ _ ψ hψ =>
        liftSimFr_of_liftSim (liftSim_quadPlus (p := 3) (e := 1) (by norm_num) hn5 le_rfl ψ hψ)) _
      (Q3TY.centralQuot3_plus hn4) hinn hnc'
  exact key _ (ModelFacts.modelUniv_POmegaPlus hn3) hnc
    (fun H _ _ ψ hψ => autOddFreeInnerTag_of_not_D4 hD4 hT hp trivial hadm ↥ψ.range
      ψ.rangeRestrict ψ.rangeRestrict_surjective (ker_rangeRestrict_le ψ hψ))

theorem twinOuterAlpha3_minus {n : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 3 1) :
    TwinOuterAlpha 3 1 .POmegaMinus n := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hodd := ModelFacts.TG3.odd_natCard_galoisField_three
  have hF3 := ModelFacts.TG3.natCard_galoisField_three
  have hirr := minusCoeffs_irr 3 1
  have hdim : Module.finrank 𝔽₃ (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → 𝔽₃) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  have : Group.IsPerfect (spinGroup (quadMinus n 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) :=
    isPerfect_spinGroup_quadMinus hn4 hirr
  have hD4 : ¬ (StatedLieTag.POmegaMinus = .POmegaPlus ∧ n = 4) := fun h => by cases h.1
  have hT : StatedLieTag.POmegaMinus ≠ .trialityD4 := by decide
  show TwinOuterAlphaOn .POmegaMinus ⟨spinGroup (quadMinus n 𝔽₃ (minusCoeffs 3 1).1
    (minusCoeffs 3 1).2), Twisted.minusDatum n hirr⟩
  exact twinOuterAlphaOn_of_spin3 hodd hF3 (nondegenerate_polarBilin_quadMinus_of_finite n _ hirr)
    (range_spinAction_quadMinus hn4 hirr) (centerScalar_quadMinus hn4 hirr)
    (ModelFacts.OrthAut.minus_hker2 hirr) (by omega)
    (fun F₁ F₂ h => ModelFacts.TG3.hproj_minus hirr hn4 F₁ F₂ h)
    (fun H _ _ ψ hψ =>
      liftSimFr_of_liftSim (liftSim_quadMinus (p := 3) (e := 1) (by norm_num) hn4 le_rfl ψ hψ)) _
    (Q3TY.centralQuot3_minus hadm)
    (fun H _ _ ψ hψ => autOddFreeInnerTag_of_not_D4 hD4 hT hp trivial hadm ↥ψ.range
      ψ.rangeRestrict ψ.rangeRestrict_surjective (ker_rangeRestrict_le ψ hψ))
    (fun R hR r hr hrc => fund_noncentral_modelUniv (p := 3) (e := 1) (t := .POmegaMinus)
      (n := n) trivial hadm (by simp) R hR r hr hrc)

end Tags

end CFSG.ClassicalInvolution.Q3.Q3OT
