module

public import CFSG.LieType.SpecialLinear.NormalizerLift.SylowNormalization
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.GraphThree.Frobenius
public import CFSG.LieType.SpecialLinear.Block222.Borel.Aut

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LieType.SpecialLinear
open scoped MatrixGroups

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {H : Type*} [Group H]

omit [Finite F] [CharP F 2] in
theorem borelGraph_mem_unitriangular {q : SpecialLinearGroup (Fin n) F}
    (hq : q ∈ unitriangular n F) : borelGraph n F q ∈ unitriangular n F := by
  have hinv : q⁻¹ ∈ unitriangular n F := (unitriangular n F).inv_mem hq
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [coe_borelGraph_apply]
    exact hinv.1 _ _ (Fin.rev_lt_rev.mpr hij)
  · rw [coe_borelGraph_apply]
    exact hinv.2 _

theorem liftAut_eq_borelStd_of_normalizes
    {π : SpecialLinearGroup (Fin n) F →* H}
    (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n)
    (e : CFSG.LieType.SpecialLinear.rangeNormalizer π)
    (he : (e : H) ∈ Subgroup.normalizer ((unitriangular n F).map π : Set H)) :
    ∃ B : GL (Fin n) F, IsUpperGL B ∧ ∃ (τ : F ≃+* F) (ε : ℕ), ε ≤ 1 ∧
      CFSG.LieType.SpecialLinear.liftAut π hker hn e = borelStd n F B τ ε := by
  classical
  let d := CFSG.LieType.SpecialLinear.stdData π hker hn e
  have hlift : CFSG.LieType.SpecialLinear.liftAut π hker hn e =
      CFSG.QuasithinUnique.K1.stdAut d.1 d.2.1 d.2.2 :=
    CFSG.LieType.SpecialLinear.liftAut_eq_stdAut π hker hn e
  have hε : d.2.2 ≤ 1 := CFSG.LieType.SpecialLinear.stdData_eps_le_one π hker hn e
  have hU : ∀ u ∈ unitriangular n F,
      CFSG.QuasithinUnique.K1.stdAut d.1 d.2.1 d.2.2 u ∈ unitriangular n F := by
    intro u hu
    rw [← hlift]
    exact CFSG.LieType.SpecialLinear.liftAut_mapsTo_unitriangular π hker hn e he u hu
  have h01 : d.2.2 = 0 ∨ d.2.2 = 1 := by omega
  rcases h01 with h0 | h1
  · have hU0 : ∀ u ∈ unitriangular n F,
        CFSG.QuasithinUnique.K1.stdAut d.1 d.2.1 0 u ∈ unitriangular n F := by
      simpa [h0] using hU
    refine ⟨d.1, CFSG.LieType.SpecialLinear.isUpperGL_of_stdAut_zero_mapsTo d.1 d.2.1 hU0,
      d.2.1, 0, Nat.zero_le 1, ?_⟩
    rw [hlift, h0]
    exact (CFSG.LieType.SpecialLinear.borelStd_zero d.1 d.2.1).symm
  · have hU1 : ∀ u ∈ unitriangular n F,
        CFSG.QuasithinUnique.K1.stdAut d.1 d.2.1 1 u ∈ unitriangular n F := by
      simpa [h1] using hU
    let B : GL (Fin n) F := d.1 * (revGL n F)⁻¹
    have hB : B * revGL n F = d.1 := by
      dsimp only [B]
      group
    have hstdB : borelStd n F B d.2.1 1 =
        CFSG.QuasithinUnique.K1.stdAut d.1 d.2.1 1 := by
      rw [borelStd_one_eq_stdAut, hB]
    have hgraph : CFSG.QuasithinUnique.K1.stdAut d.1 d.2.1 1 =
        CFSG.QuasithinUnique.K1.stdAut B d.2.1 0 * borelGraph n F := by
      rw [← hstdB, CFSG.LieType.SpecialLinear.borelStd, pow_one]
    have hU' : ∀ u ∈ unitriangular n F,
        CFSG.QuasithinUnique.K1.stdAut B d.2.1 0 u ∈ unitriangular n F := by
      intro u hu
      have hvu : borelGraph n F u ∈ unitriangular n F := borelGraph_mem_unitriangular hu
      have hmem := hU1 (borelGraph n F u) hvu
      have hbb : (borelGraph n F) ((borelGraph n F) u) = u := by
        have h := congrArg (fun Φ : MulAut (SpecialLinearGroup (Fin n) F) => Φ u)
          (borelGraph_mul_self F n)
        simpa [MulAut.mul_apply] using h
      have h2 := congrArg (fun Φ : MulAut (SpecialLinearGroup (Fin n) F) =>
        Φ (borelGraph n F u)) hgraph
      rw [MulAut.mul_apply, hbb] at h2
      rw [← h2]
      exact hmem
    refine ⟨B, CFSG.LieType.SpecialLinear.isUpperGL_of_stdAut_zero_mapsTo B d.2.1 hU',
      d.2.1, 1, le_rfl, ?_⟩
    rw [hlift, h1, ← hstdB]

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL
