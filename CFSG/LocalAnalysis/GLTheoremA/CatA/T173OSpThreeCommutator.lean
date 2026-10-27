module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeFixed2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeUnitary2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeDelta
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortSp
public import CFSG.RankThree.PartOne.KC.SymplecticFullRankTwo
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Models.SymplecticPairs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173
open CFSG.LocalAnalysis.GLTheoremA.T173X
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCSpFull
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open CFSG.LieType.Steinberg (Sp.x)
open Polynomial Module
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F] {ℓ : ℕ}

private theorem finrank_quad_ne_zero [CharP F 2] (hF : Nat.card F = 2) {d : ↥(StatedSp ℓ F)}
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) :
    finrank F ↥(primaryComponent (spEnd d) (X ^ 2 + X + 1 : F[X])) ≠ 0 := by
  have hsq : Squarefree (minpoly F (spEnd d)) :=
    (CFSG.RankThree.Classical.altPrimaryData_spLin (p := 3) (x := d)
      (three_ne_zero_of_charP_two (F := F)) hd3).squarefree
  intro h0
  exact primaryComponent_ne_bot hsq (CFSG.StandardType.SpFin.h3_mem_primaryFactors hF hd3 hd1)
    (Submodule.finrank_eq_zero.mp h0)

private theorem finrank_quad_eq_two_of_isComponentOf (hF : Nat.card F = 2) {d : ↥(StatedSp 3 F)}
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) {Kb : Subgroup ↥(StatedSp 3 F)}
    (hcomp : IsComponentOf Kb (Subgroup.centralizer ({d} : Set ↥(StatedSp 3 F)))) :
    finrank F ↥(primaryComponent (spEnd d) (X ^ 2 + X + 1 : F[X])) = 2 := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have hsum := finrank_primaryComponent_fixed_add_quad (ℓ := 3) hd3
  obtain ⟨m, hm⟩ := finrank_quad_eq_two_mul hF (d := d)
  have hne := finrank_quad_ne_zero hF hd3 hd1
  rcases eq_or_of_isComponentOf_centralizer hF (by norm_num) hd3 hd1 hcomp with hK | hK
  · subst hK
    have hQ : CFSG.Open.IsQuasisimple ↥⁅CFSG.RankThree.PartOne.spFixedFactor d,
        CFSG.RankThree.PartOne.spFixedFactor d⁆ := hcomp.2.2
    have hs : CFSG.RankThree.PartOne.spFixedDim d = 2 * (3 - m) := by
      show finrank F ↥(primaryComponent (spEnd d) (X - 1 : F[X])) = 2 * (3 - m)
      omega
    have h2s := two_le_fixed_half hF (by norm_num) hd3 hd1 hQ
      (spPrimaryBlocks_of_order_three hF (by norm_num) hd3 hd1) hs
    omega
  · subst hK
    have h8 := eight_le_finrank_unitary hF hd3 hd1 hcomp.2.2
    omega

private theorem spEnd_commutator_transvection_of_mem_fixed [CharP F 2] {d : ↥(StatedSp ℓ F)}
    {u v : Fin ℓ ⊕ Fin ℓ → F} (hu : u ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1 : F[X]))
    (hv : v ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1 : F[X])) (huv : spForm ℓ F u v = 1)
    {x : Fin ℓ ⊕ Fin ℓ → F} (hx : x ∈ primaryComponent (spEnd d) (X - 1 : F[X])) :
    spEnd ⁅spTransvection u (1 : F), spTransvection v (1 : F)⁆ x = x := by
  rw [primaryComponent_quad_eq_normKer] at hu hv
  rw [primaryComponent_sub_one_eq_fixSub] at hx
  rw [spEnd_commutator_transvection huv x,
    CFSG.LieType.SeitzGeneration.spForm_fixSub_normKer (three_ne_zero_of_charP_two) d hx hu,
    CFSG.LieType.SeitzGeneration.spForm_fixSub_normKer (three_ne_zero_of_charP_two) d hx hv]
  simp

private theorem spEnd_eq_commutator_transvection_of_mem_quad [CharP F 2] {d : ↥(StatedSp ℓ F)}
    (h2 : finrank F ↥(primaryComponent (spEnd d) (X ^ 2 + X + 1 : F[X])) = 2)
    {w : Fin ℓ ⊕ Fin ℓ → F} (hw : w ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1 : F[X]))
    (hQ : spForm ℓ F w (spEnd d w) = 1) (hQ' : spForm ℓ F (spEnd d w) w = 1)
    {x : Fin ℓ ⊕ Fin ℓ → F} (hx : x ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1 : F[X])) :
    spEnd d x = spEnd ⁅spTransvection (spEnd d w) (1 : F), spTransvection w (1 : F)⁆ x := by
  have hdw := apply_mem_primaryComponent (Commute.refl (spEnd d)) hw
  have hc := fun y => spEnd_commutator_transvection hQ' y
  have hself : ∀ y : Fin ℓ ⊕ Fin ℓ → F, y + y = 0 := fun y => by
    have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
    calc y + y = (2 : F) • y := (two_smul F y).symm
      _ = 0 := by rw [h2F, zero_smul]
  have hli : LinearIndependent F ![w, spEnd d w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hA := congrArg (fun y => spForm ℓ F y w) hst
    have hB := congrArg (fun y => spForm ℓ F y (spEnd d w)) hst
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      spForm_isAlt.self_eq_zero, hQ, hQ', map_zero, LinearMap.zero_apply, mul_zero, mul_one,
      zero_add, add_zero] at hA hB
    exact ⟨hB, hA⟩
  have hspan : Submodule.span F (Set.range ![w, spEnd d w]) =
      primaryComponent (spEnd d) (X ^ 2 + X + 1 : F[X]) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hw
      · exact hdw
    · rw [finrank_span_eq_card hli, h2, Fintype.card_fin]
  rw [← hspan] at hx
  refine LinearMap.eqOn_span (f := spEnd d) (g := spEnd _) ?_ hx
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · show spEnd d w = spEnd _ w
    rw [hc, spForm_isAlt.self_eq_zero, hQ, one_smul, add_zero, one_smul, add_comm w,
      add_assoc, hself, add_zero]
  · show spEnd d (spEnd d w) = spEnd _ (spEnd d w)
    rw [hc, spEnd_sq_apply_of_mem_primary hw, spForm_isAlt.self_eq_zero, hQ', zero_smul,
      add_zero, zero_add, one_smul, add_comm]

private theorem exists_eq_commutator_of_finrank_quad_eq_two [CharP F 2] (hF : Nat.card F = 2)
    {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    (h2 : finrank F ↥(primaryComponent (spEnd d) (X ^ 2 + X + 1 : F[X])) = 2) :
    ∃ u : Fin ℓ ⊕ Fin ℓ → F, spForm ℓ F (spEnd d u) u = 1 ∧
      d = ⁅spTransvection (spEnd d u) (1 : F), spTransvection u (1 : F)⁆ := by
  have hne : primaryComponent (spEnd d) (X ^ 2 + X + 1 : F[X]) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨w, hw, hQ⟩ := exists_spForm_self_eq_one hF hd3 hne
  have hQ' : spForm ℓ F (spEnd d w) w = 1 := by
    rw [← spForm_isAlt.neg_eq w (spEnd d w), hQ]
    exact CharTwo.neg_eq 1
  refine ⟨w, hQ', ?_⟩
  apply spLin_injective
  refine Units.ext (LinearMap.ext fun x => ?_)
  change spEnd d x = spEnd _ x
  obtain ⟨hx1, hx3, hx⟩ := split_primary hd3 x
  rw [hx, map_add, map_add, spEnd_eq_self_of_mem_fixed hx1,
    spEnd_commutator_transvection_of_mem_fixed
      (apply_mem_primaryComponent (Commute.refl (spEnd d)) hw) hw hQ' hx1,
    spEnd_eq_commutator_transvection_of_mem_quad h2 hw hQ hQ' hx3]

private theorem spTransvection_single_inl_two [CharP F 2] :
    spTransvection (Pi.single (Sum.inl 2) 1 : Fin 3 ⊕ Fin 3 → F) (1 : F) =
      Sp.x 3 F (Pi.single 2 1) 1 := by
  rw [CFSG.ClassicalInvolution.Balance.x_simple_fst]
  have hidx : (CFSG.ClassicalInvolution.Balance.simpleIdx (n := 3) 2).1 = .positiveLong 2 := by
    simp [CFSG.ClassicalInvolution.Balance.simpleIdx]
  rw [hidx]
  apply spLin_injective
  refine Units.ext (LinearMap.ext fun y => ?_)
  change spEnd (spTransvection _ 1) y =
    spEnd (CFSG.LieType.Universal.Symplectic.SpExtras.elt (F := F) (.positiveLong 2) 1) y
  rw [spEnd_spTransvection,
    spEnd_apply (CFSG.LieType.Universal.Symplectic.SpExtras.elt (F := F) (.positiveLong 2) 1),
    ← CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply,
    CFSG.LieType.Universal.Symplectic.SpExtras.mat_elt]
  have hB : spForm 3 F y (Pi.single (Sum.inl 2) 1) = - y (Sum.inr 2) := by
    rw [spForm_apply]
    refine (CFSG.ClassicalInvolution.Models.SymplecticPairs.form_single_right y
      (Sum.inl 2)).trans ?_
    simp [CFSG.ClassicalInvolution.Models.SymplecticPairs.par,
      CFSG.ClassicalInvolution.Models.SymplecticPairs.sgn]
  rw [hB]
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [Matrix.add_mulVec, Matrix.mulVec, dotProduct, Matrix.single_apply, Matrix.one_apply,
      Fintype.sum_sum_type, Fin.sum_univ_three, Pi.single_apply,
      CFSG.LieType.Universal.Symplectic.SpExtras.E, CharTwo.neg_eq]

private theorem spTransvection_single_inr_two :
    spTransvection (Pi.single (Sum.inr 2) 1 : Fin 3 ⊕ Fin 3 → F) (1 : F) =
      Sp.x 3 F (-Pi.single 2 1) 1 := by
  rw [CFSG.ClassicalInvolution.Balance.x_simple_snd]
  have hidx : (CFSG.ClassicalInvolution.Balance.simpleIdx (n := 3) 2).2 = .negativeLong 2 := by
    simp [CFSG.ClassicalInvolution.Balance.simpleIdx]
  rw [hidx]
  apply spLin_injective
  refine Units.ext (LinearMap.ext fun y => ?_)
  change spEnd (spTransvection _ 1) y =
    spEnd (CFSG.LieType.Universal.Symplectic.SpExtras.elt (F := F) (.negativeLong 2) 1) y
  rw [spEnd_spTransvection,
    spEnd_apply (CFSG.LieType.Universal.Symplectic.SpExtras.elt (F := F) (.negativeLong 2) 1),
    ← CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply,
    CFSG.LieType.Universal.Symplectic.SpExtras.mat_elt]
  have hB : spForm 3 F y (Pi.single (Sum.inr 2) 1) = y (Sum.inl 2) := by
    rw [spForm_apply]
    refine (CFSG.ClassicalInvolution.Models.SymplecticPairs.form_single_right y
      (Sum.inr 2)).trans ?_
    simp [CFSG.ClassicalInvolution.Models.SymplecticPairs.par,
      CFSG.ClassicalInvolution.Models.SymplecticPairs.sgn]
  rw [hB]
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [Matrix.add_mulVec, Matrix.mulVec, dotProduct, Matrix.single_apply, Matrix.one_apply,
      Fintype.sum_sum_type, Fin.sum_univ_three, Pi.single_apply,
      CFSG.LieType.Universal.Symplectic.SpExtras.E] <;> ring

private theorem exists_conj_eq_commutator_x [CharP F 2] {u v : Fin 3 ⊕ Fin 3 → F}
    (huv : spForm 3 F u v = 1) :
    ∃ g : ↥(StatedSp 3 F), ⁅spTransvection u (1 : F), spTransvection v (1 : F)⁆ =
      g * ⁅Sp.x 3 F (Pi.single 2 1) 1, Sp.x 3 F (-Pi.single 2 1) 1⁆ * g⁻¹ := by
  obtain ⟨g₁, e1, e2⟩ : ∃ g : ↥(StatedSp 3 F), spEnd g (Pi.single (Sum.inl 0) 1) = u ∧
      spEnd g (Pi.single (Sum.inr 0) 1) = v :=
    CFSG.ClassicalInvolution.Models.SymplecticPairs.exists_sp_apply_eq (K := F) (m := 2)
      u v (by rw [spForm_apply] at huv; exact huv)
  have h22 : CFSG.ClassicalInvolution.Models.SymplecticPairs.form
      (Pi.single (Sum.inl 2) 1 : Fin 3 ⊕ Fin 3 → F) (Pi.single (Sum.inr 2) 1) = 1 := by
    rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.form_single_right]
    simp [CFSG.ClassicalInvolution.Models.SymplecticPairs.par,
      CFSG.ClassicalInvolution.Models.SymplecticPairs.sgn]
  obtain ⟨g₂, e3, e4⟩ : ∃ g : ↥(StatedSp 3 F),
      spEnd g (Pi.single (Sum.inl 0) 1) = Pi.single (Sum.inl 2) 1 ∧
      spEnd g (Pi.single (Sum.inr 0) 1) = Pi.single (Sum.inr 2) 1 :=
    CFSG.ClassicalInvolution.Models.SymplecticPairs.exists_sp_apply_eq (K := F) (m := 2) _ _ h22
  have hinv : ∀ (g : ↥(StatedSp 3 F)) y, spEnd g⁻¹ (spEnd g y) = y := fun g y => by
    rw [← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one, Module.End.one_apply]
  have hu : spEnd (g₁ * g₂⁻¹) (Pi.single (Sum.inl 2) 1) = u := by
    rw [spEnd_mul, Module.End.mul_apply, ← e3, hinv, e1]
  have hv : spEnd (g₁ * g₂⁻¹) (Pi.single (Sum.inr 2) 1) = v := by
    rw [spEnd_mul, Module.End.mul_apply, ← e4, hinv, e2]
  refine ⟨g₁ * g₂⁻¹, ?_⟩
  rw [← spTransvection_single_inl_two, ← spTransvection_single_inr_two]
  have hconj : ∀ (g a b : ↥(StatedSp 3 F)), g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
    intro g a b
    simp only [commutatorElement_def]
    group
  rw [hconj, CFSG.RankThree.PartOne.KCSpFull.spTransvection_conj,
    CFSG.RankThree.PartOne.KCSpFull.spTransvection_conj, hu, hv]

theorem exists_conj_eq_commutator_x_of_isComponentOf (hF : Nat.card F = 2)
    {d : ↥(StatedSp 3 F)} (hd1 : d ≠ 1) (hd3 : d ^ 3 = 1) {Kb : Subgroup ↥(StatedSp 3 F)}
    (hcomp : IsComponentOf Kb (Subgroup.centralizer ({d} : Set ↥(StatedSp 3 F)))) :
    ∃ g : ↥(StatedSp 3 F),
      d = g * ⁅Sp.x 3 F (Pi.single 2 1) 1, Sp.x 3 F (-Pi.single 2 1) 1⁆ * g⁻¹ := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  obtain ⟨u, hu, hdu⟩ := exists_eq_commutator_of_finrank_quad_eq_two hF hd3
    (finrank_quad_eq_two_of_isComponentOf hF hd3 hd1 hcomp)
  obtain ⟨g, hg⟩ := exists_conj_eq_commutator_x hu
  exact ⟨g, hdu.trans hg⟩

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
