module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Q1Twist
public import CFSG.GH74.GLS.Stage2.OddAut.LangR
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitRankOne

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.GH74.GLS.Stage2.OddAut
open scoped Matrix

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem mp_conj_z0_rootSpan {L : Type} [Field L] {g : ModGL TwistTag.D4.tag L}
    (hg : g ∈ rootSpan TwistTag.D4.tag L d4LongA2) :
    trialityOpposition L * g * (trialityOpposition L)⁻¹ ∈
      rootSpan TwistTag.D4.tag L d4LongA2 := by
  have hS : ∀ γ ∈ d4LongA2, IsRoot TwistTag.D4.tag γ := fun _ h => d4LongA2_isRoot h
  have h := map_conj_rootSpan_of_mem_monomialSubgroup (K := L)
    (trialityOpposition_mem_monomialSubgroup (K := L)) hS
  have hmem : trialityOpposition L * g * (trialityOpposition L)⁻¹ ∈
      (rootSpan TwistTag.D4.tag L d4LongA2).map
        (MulAut.conj (trialityOpposition L)).toMonoidHom := ⟨g, hg, rfl⟩
  rw [h] at hmem
  refine rootSpan_mono ?_ hmem
  rintro _ ⟨α, hα, rfl⟩
  beta_reduce
  rw [weylQuotientHom_trialityOpposition_smul]
  exact d4LongA2_neg_mem hα

theorem mp_F2_data {p f : ℕ} [Fact p.Prime] (hq : (p ^ f) % 3 = 2) {L : Type} [Field L]
    [CharP L p] [PerfectRing L p] {y ν : ModGL TwistTag.D4.tag L}
    (hy : y ∈ rootSpan TwistTag.D4.tag L d4LongA2) {a : Fin TwistTag.D4.tag.rank → Lˣ}
    (hya : y * ν * y⁻¹ = rootDiagUnit TwistTag.D4.tag a)
    (hcube : ∀ α ∈ d4LongA2, rootChar a α ^ 3 = 1)
    (hFν : trialityOpposition L * twistHom TwistTag.D4 L (iterateFrobenius L p f) ν *
      (trialityOpposition L)⁻¹ = ν) :
    ∃ b : Fin TwistTag.D4.tag.rank → Lˣ,
      trialityOpposition L * twistHom TwistTag.D4 L (iterateFrobenius L p f) y *
        (trialityOpposition L)⁻¹ * y⁻¹ ∈ rootSpan TwistTag.D4.tag L d4LongA2 ∧
      (trialityOpposition L * twistHom TwistTag.D4 L (iterateFrobenius L p f) y *
        (trialityOpposition L)⁻¹ * y⁻¹) * rootDiagUnit TwistTag.D4.tag a *
        (trialityOpposition L * twistHom TwistTag.D4 L (iterateFrobenius L p f) y *
          (trialityOpposition L)⁻¹ * y⁻¹)⁻¹ = rootDiagUnit TwistTag.D4.tag b ∧
      ∀ α ∈ d4LongA2, rootChar b α = rootChar a α := by
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  set F := twistHom TwistTag.D4 L Fr with hF
  set z : ModGL TwistTag.D4.tag L := trialityOpposition L with hz
  set a' : Fin TwistTag.D4.tag.rank → Lˣ :=
    fun i => Units.map Fr.toMonoidHom (a (TwistTag.D4.perm.symm i)) with ha'
  refine ⟨a'⁻¹, mul_mem (mp_conj_z0_rootSpan (twistHom_mem_rootSpan_d4LongA2 f hy)) (inv_mem hy),
    ?_, fun α hα => ?_⟩
  · have hFd : z * F (y * ν * y⁻¹) * z⁻¹ = (z * F y * z⁻¹) * ν * (z * F y * z⁻¹)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      calc z * (F y * F ν * (F y)⁻¹) * z⁻¹ =
          (z * F y * z⁻¹) * (z * F ν * z⁻¹) * (z * F y * z⁻¹)⁻¹ := by group
        _ = (z * F y * z⁻¹) * ν * (z * F y * z⁻¹)⁻¹ := by rw [hFν]
    have hFa : F (rootDiagUnit TwistTag.D4.tag a) = rootDiagUnit TwistTag.D4.tag a' :=
      twistHom_rootDiagUnit_eq a
    calc z * F y * z⁻¹ * y⁻¹ * rootDiagUnit TwistTag.D4.tag a * (z * F y * z⁻¹ * y⁻¹)⁻¹
        = z * F y * z⁻¹ * y⁻¹ * (y * ν * y⁻¹) * (z * F y * z⁻¹ * y⁻¹)⁻¹ := by rw [hya]
      _ = (z * F y * z⁻¹) * ν * (z * F y * z⁻¹)⁻¹ := by group
      _ = z * F (y * ν * y⁻¹) * z⁻¹ := hFd.symm
      _ = z * F (rootDiagUnit TwistTag.D4.tag a) * z⁻¹ := by rw [hya]
      _ = z * rootDiagUnit TwistTag.D4.tag a' * z⁻¹ := by rw [hFa]
      _ = rootDiagUnit TwistTag.D4.tag a'⁻¹ :=
          conj_rootDiagUnit_of_smul_eq_neg (trialityOpposition_mem_monomialSubgroup (K := L))
            weylQuotientHom_trialityOpposition_smul a'
  · have h1 : rootChar a' α = Units.map Fr.toMonoidHom (rootChar a α) := by
      rw [ha', rootChar_map_tuple Fr (fun i => a (TwistTag.D4.perm.symm i)) α,
        ← rootChar_permLattice a TwistTag.D4.perm.symm α,
        permLattice_symm_d4LongA2_fixed hα]
    rw [rootChar_inv_apply, h1, CTTorus.map_units_eq_pow hFr]
    have hq' : p ^ f = 3 * ((p ^ f) / 3) + 2 := by omega
    have h3 := hcube α hα
    rw [hq', pow_add, pow_mul, h3, one_pow, one_mul]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact h3)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
