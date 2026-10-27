module

public import CFSG.ClassicalInvolution.ModelFacts.TwistedLeviDescent
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnPerX
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem permLattice_d4LongA2_fixed {α : Fin TwistTag.D4.tag.rank → ℤ} (hα : α ∈ d4LongA2) :
    permLattice TwistTag.D4.perm α = α := by
  rw [d4LongA2_eq] at hα
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hα
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl <;> exact permLattice_d4LongVec _ _

theorem permLattice_symm_d4LongA2_fixed {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : α ∈ d4LongA2) : permLattice TwistTag.D4.perm.symm α = α := by
  have h := permLattice_symm_permLattice TwistTag.D4.perm α
  rwa [permLattice_d4LongA2_fixed hα] at h

theorem twistHom_mem_rootSpan_d4LongA2 {p : ℕ} [Fact p.Prime] (f : ℕ) {L : Type} [Field L]
    [CharP L p] [PerfectRing L p] {g : ModGL TwistTag.D4.tag L}
    (hg : g ∈ rootSpan TwistTag.D4.tag L d4LongA2) :
    twistHom TwistTag.D4 L (iterateFrobenius L p f) g ∈ rootSpan TwistTag.D4.tag L d4LongA2 := by
  have h := CFSG.ClassicalInvolution.ModelFacts.Levi.map_frobTwistGL_rootSpan_diagram p
    TwistTag.D4 (k := L) f (S := d4LongA2) (fun _ hα => d4LongA2_isRoot hα)
  have hsub : permLattice TwistTag.D4.perm '' d4LongA2 ⊆ d4LongA2 := by
    rintro _ ⟨α, hα, rfl⟩
    rw [permLattice_d4LongA2_fixed hα]
    exact hα
  have hle : (rootSpan TwistTag.D4.tag L d4LongA2).map
      (LieType.AlgebraicGroups.frobTwistGL TwistTag.D4.tag L p f (diagramMap TwistTag.D4 L)) ≤
      rootSpan TwistTag.D4.tag L d4LongA2 := by
    rw [h]
    exact rootSpan_mono hsub
  exact hle ⟨g, hg, rfl⟩

theorem q1_F_data {p f : ℕ} [Fact p.Prime] (hq : (p ^ f) % 3 = 1) {L : Type} [Field L]
    [CharP L p] [PerfectRing L p] {y ν : ModGL TwistTag.D4.tag L}
    (hy : y ∈ rootSpan TwistTag.D4.tag L d4LongA2) {a : Fin TwistTag.D4.tag.rank → Lˣ}
    (hya : y * ν * y⁻¹ = rootDiagUnit TwistTag.D4.tag a)
    (hcube : ∀ α ∈ d4LongA2, rootChar a α ^ 3 = 1)
    (hFν : twistHom TwistTag.D4 L (iterateFrobenius L p f) ν = ν) :
    ∃ b : Fin TwistTag.D4.tag.rank → Lˣ,
      twistHom TwistTag.D4 L (iterateFrobenius L p f) y * y⁻¹ ∈
        rootSpan TwistTag.D4.tag L d4LongA2 ∧
      (twistHom TwistTag.D4 L (iterateFrobenius L p f) y * y⁻¹) *
        rootDiagUnit TwistTag.D4.tag a *
        (twistHom TwistTag.D4 L (iterateFrobenius L p f) y * y⁻¹)⁻¹ =
        rootDiagUnit TwistTag.D4.tag b ∧
      ∀ α ∈ d4LongA2, rootChar b α = rootChar a α := by
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  set F := twistHom TwistTag.D4 L Fr with hF
  refine ⟨fun i => Units.map Fr.toMonoidHom (a (TwistTag.D4.perm.symm i)),
    mul_mem (twistHom_mem_rootSpan_d4LongA2 f hy) (inv_mem hy), ?_, fun α hα => ?_⟩
  · have hFd : F (y * ν * y⁻¹) = F y * ν * (F y)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hFν]
    calc F y * y⁻¹ * rootDiagUnit TwistTag.D4.tag a * (F y * y⁻¹)⁻¹
        = F y * y⁻¹ * (y * ν * y⁻¹) * (F y * y⁻¹)⁻¹ := by rw [hya]
      _ = F y * ν * (F y)⁻¹ := by group
      _ = F (y * ν * y⁻¹) := hFd.symm
      _ = F (rootDiagUnit TwistTag.D4.tag a) := by rw [hya]
      _ = _ := twistHom_rootDiagUnit_eq a
  · have h1 : rootChar (fun i => Units.map Fr.toMonoidHom (a (TwistTag.D4.perm.symm i))) α =
        Units.map Fr.toMonoidHom (rootChar a α) := by
      rw [rootChar_map_tuple Fr (fun i => a (TwistTag.D4.perm.symm i)) α,
        ← rootChar_permLattice a TwistTag.D4.perm.symm α,
        permLattice_symm_d4LongA2_fixed hα]
    rw [h1, CTTorus.map_units_eq_pow hFr]
    have hq' : p ^ f = 3 * ((p ^ f) / 3) + 1 := by omega
    rw [hq', pow_succ, pow_mul, hcube α hα, one_pow, one_mul]

end CFSG.GH74.GLS.Stage2.Bender.Thm1
