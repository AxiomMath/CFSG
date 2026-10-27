module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUUnitary
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofSUData
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofAutSU
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291Out

open Matrix CFSG.Open CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry (Uid mem_Uid_iff)

section Aut

variable {n r f : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData r f K)

theorem congr_uConjAut (hn : 1 ≤ n) (A : uU hU n) :
    MulAut.congr (uTransport hU hn) (uConjAut hU hn A) = primeFormConjHom hU _ A :=
  (MulAut.congr (uTransport hU hn)).apply_symm_apply _

theorem congr_uFieldAut (hn : 1 ≤ n) (σ : K ≃+* K) :
    MulAut.congr (uTransport hU hn) (uFieldAut hU hn σ) = primeFormFieldHom hU uGram_one σ :=
  (MulAut.congr (uTransport hU hn)).apply_symm_apply _

theorem uni_outer_form [Fact r.Prime] [Finite K] [CharP K r] (hn : 5 ≤ n)
    (hK : Nat.card K = (r ^ f) ^ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut (StatedProj (StatedSU n (r ^ f) K))) (hα : α ^ p = 1)
    (hnot : ¬ ∃ B : Uid (unitaryInvolution K r f) n,
      CFSG.LocalAnalysis.RankFourTheoremC.l212in_suPhi hK B = α) :
    ∃ (H : uU hU n) (σ : K ≃+* K), σ ^ p = 1 ∧ σ ≠ 1 ∧
      α = uConjAut hU (by omega) H * uFieldAut hU (by omega) σ *
        (uConjAut hU (by omega) H)⁻¹ := by
  haveI : NeZero n := ⟨by omega⟩
  have hq : ¬ (n = 3 ∧ r ^ f = 2) := fun h => by omega
  obtain ⟨A, φ, hαeq⟩ := exists_uConjAut_mul_uFieldAut hU (by omega) hq α
  have hφ1 : φ ≠ 1 := by
    rintro rfl
    apply hnot
    have hAU : (A : GL (Fin n) K) ∈ Uid (unitaryInvolution K r f) n := by
      rw [mem_Uid_iff, CFSG.LocalAnalysis.RankFourTheoremC.AutSU.conjTr_unitaryInvolution hU]
      exact (mem_uU hU).1 A.2
    refine ⟨⟨A, hAU⟩, ?_⟩
    rw [hαeq, map_one, mul_one]
    refine MulEquiv.ext fun y => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [CFSG.LocalAnalysis.RankFourTheoremC.l212in_suPhi_mk]
    exact (uConjAut_proj hU (by omega) A g).symm
  have hα' : (primeFormConjHom hU _ A * primeFormFieldHom hU uGram_one φ) ^ p = 1 := by
    have h1 := congrArg (MulAut.congr (uTransport hU (by omega : 1 ≤ n))) hα
    rw [map_pow, hαeq, map_mul, congr_uConjAut, congr_uFieldAut, map_one] at h1
    exact h1
  obtain ⟨hord, H, hH⟩ := CFSG.StandardType.RecipeFieldSpU.primeForm_conj_of_pow_eq_one hU
    (d := n) (by omega) hq hp hp2 A φ hφ1 hα'
  refine ⟨H, φ, ?_, hφ1, ?_⟩
  · have h1 := pow_orderOf_eq_one φ
    rwa [hord] at h1
  · apply (MulAut.congr (uTransport hU (by omega : 1 ≤ n))).injective
    rw [hαeq, map_mul, map_mul, map_mul, map_inv, congr_uConjAut, congr_uFieldAut, congr_uConjAut,
      hH]

theorem coe_uLift_gl (A : uU hU n) (φ : K ≃+* K) (g : StatedSU n (r ^ f) K) :
    ((uLift hU A φ g : StatedSU n (r ^ f) K) : GL (Fin n) K) =
      (A : GL (Fin n) K) * glAut φ (g : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ :=
  rfl

theorem uni_lift (hn : 1 ≤ n) (H : uU hU n) (σ : K ≃+* K) :
    ∃ Ã : StatedSU n (r ^ f) K →* StatedSU n (r ^ f) K,
      (∀ s, projH (StatedSU n (r ^ f) K) (Ã s) =
        (uConjAut hU hn H * uFieldAut hU hn σ * (uConjAut hU hn H)⁻¹)
          (projH (StatedSU n (r ^ f) K) s)) ∧
      ∀ g : StatedSU n (r ^ f) K, glAut σ (g : GL (Fin n) K) = g →
        Ã (uLift hU H 1 g) = uLift hU H 1 g := by
  refine ⟨(uLift hU H 1).comp ((uLift hU 1 σ).comp (uLift hU H⁻¹ 1)), fun s => ?_, fun g hg => ?_⟩
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← uLift_proj hU hn, ← uLift_proj hU hn,
      ← uLift_proj hU hn]
    simp [MulAut.mul_apply]
  · apply Subtype.ext
    simp only [MonoidHom.comp_apply, coe_uLift_gl, map_one, MulAut.one_apply, Subgroup.coe_one,
      inv_one, one_mul, mul_one, Subgroup.coe_inv, inv_inv]
    have h1 : (H : GL (Fin n) K)⁻¹ * ((H : GL (Fin n) K) * g * (H : GL (Fin n) K)⁻¹) *
        (H : GL (Fin n) K) = g := by group
    rw [h1, hg]

end Aut

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291Out
