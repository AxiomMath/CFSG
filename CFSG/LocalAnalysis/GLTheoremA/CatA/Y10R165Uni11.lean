module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Uni10
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Uni2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCUnitaryModel
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

theorem su165EngineTwA_holds : SU165EngineTwA := by
  intro ℓ n p q F _ _ _ hcard hn hl2 hm0ne hp hp2 hq hq2 hqp hqdiv A hAe hmax h3
  classical
  have hUF : UnitaryFieldData 2 n F :=
    { prime := Nat.prime_two
      one_le := hn
      card := by
        rw [hcard, show ((2 : ℕ) ^ n) ^ 2 = 2 ^ (n * 2) from (pow_mul 2 n 2).symm,
          Nat.mul_comm n 2] }
  have hpRankStated : CFSG.Open.pRank p (⊤ : Subgroup ↥(StatedSU (ℓ + 1) (2 ^ n) F)) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥(sesqSpecialUnitaryGroupLE (idForm hUF (ℓ + 1)))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := p) hp.one_lt
      (statedSUEquivSesqLE hUF (ℓ + 1))
  set A' : Subgroup ↥(sesqSpecialUnitaryGroupLE (idForm hUF (ℓ + 1))) :=
    A.map (statedSUEquivSesqLE hUF (ℓ + 1)).toMonoidHom with hA'def
  have hA'e : IsElemAbelian p A' := CFSG.SectionRank.isElemAbelian_map hAe _
  have hpRankA' : CFSG.Open.pRank p A' = CFSG.Open.pRank p A :=
    CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective (p := p) hp.one_lt
      (statedSUEquivSesqLE hUF (ℓ + 1)).toMonoidHom (statedSUEquivSesqLE hUF (ℓ + 1)).injective A
  have hmax' : CFSG.Open.pRank p
      (⊤ : Subgroup ↥(sesqSpecialUnitaryGroupLE (idForm hUF (ℓ + 1)))) ≤
      CFSG.Open.pRank p A' := by
    rw [hpRankA', ← hpRankStated]
    exact hmax
  have h3' : 3 ≤ CFSG.Open.pRank p A' := by
    rw [hpRankA']
    exact h3
  have hZ : ∀ z ∈ ((StatedScalars (Fin (ℓ + 1)) F).subgroupOf
      (StatedSU (ℓ + 1) (2 ^ n) F)).map (statedSUEquivSesqLE hUF (ℓ + 1)).toMonoidHom,
      ∃ c : Fˣ,
        ((z : (Fin (ℓ + 1) → F) ≃ₗ[F] (Fin (ℓ + 1) → F)) :
          (Fin (ℓ + 1) → F) →ₗ[F] (Fin (ℓ + 1) → F)) = (c : F) • LinearMap.id := by
    rintro z ⟨z₀, hz₀, rfl⟩
    exact exists_eq_smul_id_of_mem_statedScalars hUF hz₀
  have hcore : Concl165Avoid ↥(sesqSpecialUnitaryGroupLE (idForm hUF (ℓ + 1))) p q A'
      (((StatedScalars (Fin (ℓ + 1)) F).subgroupOf
        (StatedSU (ℓ + 1) (2 ^ n) F)).map (statedSUEquivSesqLE hUF (ℓ + 1)).toMonoidHom) :=
    concl165Avoid_sesqSpecialUnitaryGroupLE (h := hUF) (by have := hl2; omega) hm0ne hp hp2 hq
      hq2 hqdiv A' hA'e hmax' h3' _ hZ
  exact concl165Avoid_of_mulEquiv hp hq (statedSUEquivSesqLE hUF (ℓ + 1)) hcore

section Certificate

theorem i165On_famTwA_holds : I165On i165FamTwA := i165On_famTwA_of_engine su165EngineTwA_holds

end Certificate

end CFSG.LocalAnalysis.GLTheoremA.Y10F
