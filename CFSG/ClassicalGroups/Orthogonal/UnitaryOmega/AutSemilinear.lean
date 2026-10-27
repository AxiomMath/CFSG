module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Defs
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Models
import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinear
import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarConj
import CFSG.RankThree.PartOne.S11d.LieCentralizerOrth

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.BorelTits
open CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCOrthogonalAut CFSG.GroupTheory.WeirSylow

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

theorem exists_semilinear_conj_of_mulAut {m : ℕ} (hm : 3 ≤ m) (α : MulAut (normOmega E m)) :
    ∃ (σ : F ≃+* F) (S : ((F × F) × (Fin m → K)) ≃+ ((F × F) × (Fin m → K))) (μ : F),
      (∀ (c : F) (v : (F × F) × (Fin m → K)), S (c • v) = σ c • S v) ∧ μ ≠ 0 ∧
      (∀ v, normHypForm E m (S v) = μ * σ (normHypForm E m v)) ∧
      ∀ (y : normOmega E m) (v : (F × F) × (Fin m → K)),
        ((α y : normOmega E m) : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
            (S v) =
          S ((y : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v) := by
  classical
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  have hQ := normHypForm_polarBilin_nondegenerate E m
  have hdim := finrank_normHypForm E m
  haveI : Nontrivial ((F × F) × (Fin m → K)) :=
    Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have hinj : Function.Injective (QuotientGroup.mk'
      ((scalars F ((F × F) × (Fin m → K))).subgroupOf (normOmega E m))) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgs := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff g).mp hg)
    exact Subtype.ext
      (CFSG.RankThree.PartOne.eq_one_of_mem_scalars_of_mem_orthDerived hQ g.2 hgs)
  let e : normOmega E m ≃* ProjOrthDerived (normHypForm E m) :=
    MulEquiv.ofBijective _ ⟨hinj, QuotientGroup.mk'_surjective _⟩
  have hD4 : Module.finrank F ((F × F) × (Fin m → K)) = 8 →
      ¬ ∃ U : Submodule F ((F × F) × (Fin m → K)),
        Module.finrank F U = 4 ∧ ∀ u ∈ U, normHypForm E m u = 0 := by
    rintro h8 ⟨U, hU, hUs⟩
    have hm3 : m = 3 := by omega
    have hplus : IsPlusType (normHypForm E m) := ⟨U, by omega, hUs⟩
    rw [isPlusType_normHypForm_iff E m, hm3] at hplus
    exact Nat.not_even_iff_odd.mpr ⟨1, rfl⟩ hplus
  obtain ⟨σ, S, hS, μ, hμ, hSQ, hind⟩ :=
    orthogonal_aut_semilinear (normHypForm E m) hQ (by omega) hD4 (MulAut.congr e α)
  refine ⟨σ, S, μ, hS, hμ, hSQ, fun y v => ?_⟩
  have hy' := semilinConj_mem_orthDerived S σ hS μ hSQ y.2
  have h := hind y ⟨_, hy'⟩ (fun w => semilinConj_apply S σ hS y w)
  have hα : α y = ⟨_, hy'⟩ := by
    apply e.injective
    have h1 : (MulAut.congr e α) (e y) = e (α y) := by
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        MulEquiv.trans_apply]
    rw [← h1]
    exact h
  rw [hα]
  exact (semilinConj_apply S σ hS _ (S v)).trans (by rw [AddEquiv.symm_apply_apply])

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

end
