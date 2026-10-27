module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IAutNat
import CFSG.ClassicalInvolution.ModelFacts.OrthAutSim
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesSimil

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Matrix CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LieType.Universal.Spin (quadOdd nondegenerate_quadOdd coe_quadOdd)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldEquiv)

theorem sec4I_exists_conj_of_mulAut_std
    (α : MulAut (omegaProj (nondegenerate_quadOdd 3 (ZMod 3)))) :
    ∃ A : OGroup (quadOdd 3 (ZMod 3)),
      ∀ p : omegaProj (nondegenerate_quadOdd 3 (ZMod 3)),
        ((α p : omegaProj (nondegenerate_quadOdd 3 (ZMod 3))) : ProjOrth (quadOdd 3 (ZMod 3))) =
          toProj (quadOdd 3 (ZMod 3)) A *
            ((p : omegaProj (nondegenerate_quadOdd 3 (ZMod 3))) : ProjOrth (quadOdd 3 (ZMod 3))) *
            (toProj (quadOdd 3 (ZMod 3)) A)⁻¹ := by
  classical
  have hQ := nondegenerate_quadOdd 3 (ZMod 3)
  have h7 : Module.finrank (ZMod 3) (Fin 3 ⊕ Fin 3 ⊕ Unit → ZMod 3) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card]
    decide
  obtain ⟨Φ, hΦ⟩ := sec4I_exists_statedProj_equiv (quadOdd 3 (ZMod 3)) hQ (by rw [h7]; norm_num)
    (StatedQuadOdd 3 (ZMod 3)) (coe_quadOdd 3 (ZMod 3))
  let β : MulAut (StatedProj (StatedOmega (StatedQuadOdd 3 (ZMod 3)))) :=
    Φ.trans (α.trans Φ.symm)
  have hadm : StatedLieAdmissible .POmegaOdd 3 3 1 := by
    unfold StatedLieAdmissible
    decide
  obtain ⟨A, φ, μ, hAμ, hy⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.OrthAut.exists_similarity_odd (n := 3) (p := 3) (f := 1)
      (F := ZMod 3) hadm (by simp) β
  have hφ : φ = RingEquiv.refl (ZMod 3) := Subsingleton.elim _ _
  subst hφ
  have hsim1 : ∀ v, quadOdd 3 (ZMod 3) (A.val *ᵥ v) =
      (μ : ZMod 3) * quadOdd 3 (ZMod 3) v := fun v => by simpa using hAμ v
  have hμ : μ = 1 := by
    rcases (by decide : ∀ u : (ZMod 3)ˣ, u = 1 ∨ u = -1) μ with h | h
    · exact h
    · exfalso
      have hs : IsSimilitude (quadOdd 3 (ZMod 3))
          (CFSG.ClassicalGroups.Orthogonal.toLinEquiv _ (ZMod 3) A) (-1) := by
        intro v
        rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, hsim1 v, h]
      have hev := (exists_isSimilitude_neg_one_iff hQ).mp ⟨_, hs⟩
      rw [h7] at hev
      exact absurd hev (by decide)
  subst hμ
  have hsA : IsSimilitude (quadOdd 3 (ZMod 3))
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv _ (ZMod 3) A) 1 := by
    intro v
    rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, hsim1 v]
  let gA : OGroup (quadOdd 3 (ZMod 3)) :=
    ⟨CFSG.ClassicalGroups.Orthogonal.toLinEquiv _ (ZMod 3) A, isSimilitude_one_iff.mp hsA⟩
  refine ⟨gA, fun p => ?_⟩
  obtain ⟨xA, hxA⟩ := QuotientGroup.mk_surjective (Φ.symm p)
  have hp : p = Φ (QuotientGroup.mk xA) := by
    rw [hxA]
    simp
  subst hp
  obtain ⟨gx, hgx, hΦx⟩ := hΦ (xA : GL _ (ZMod 3)) xA.2
  obtain ⟨y, hyA, hβy⟩ := hy xA
  obtain ⟨gy, hgy, hΦy⟩ := hΦ (y : GL _ (ZMod 3)) y.2
  have hαy : α (Φ (QuotientGroup.mk xA)) = Φ (QuotientGroup.mk y) := by
    rw [← hβy]
    simp [β]
  have hgy' : gy = gA * gx * gA⁻¹ := by
    apply Subtype.ext
    have hgl : glFieldEquiv (Fin 3 ⊕ Fin 3 ⊕ Unit) (RingEquiv.refl (ZMod 3)) xA.1 = xA.1 := by
      apply Units.ext
      ext i j
      rfl
    rw [hgy, hyA, hgl, map_mul, map_mul, map_inv, ← hgx]
    rfl
  rw [hαy, hΦy, hΦx, hgy', map_mul, map_mul, map_inv]

end CFSG.OddStandard.SmallF3.Omega
