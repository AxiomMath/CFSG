module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OConj
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5E6Orb
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwoTorus
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeKit
public import CFSG.LieType.Chevalley.SingleEdgePerfect
public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173 CFSG.LocalAnalysis.GLTheoremA.T173X
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.E6TwoPilot
open CFSG.StandardType.E6ThreeEnd CFSG.StandardType.SmallExc
open scoped MatrixGroups

set_option maxRecDepth 100000 in
theorem exists_dot_eq_zero_normE6 : ∀ c : Fin 4 → ZMod 3, c ≠ 0 → ∀ z : ZMod 3, z ≠ 0 →
    ∃ w : Fin 4 → ZMod 3,
      c 0 * w 0 + c 1 * w 1 + c 2 * w 2 + c 3 * w 3 = 0 ∧ normE6 w = z := by
  set_option synthInstance.maxSize 512 in
  decide +kernel

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem isElemAbelian_range_torusE6Two (h2 : (2 : K) = 0) :
    IsElemAbelian 3 (torusE6Two (K := K) h2).range := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨_, a, rfl⟩ := x
    obtain ⟨_, b, rfl⟩ := y
    apply Subtype.ext
    show torusE6Two h2 a * torusE6Two h2 b = torusE6Two h2 b * torusE6Two h2 a
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have h3 : a ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      funext i
      have hzero : (3 : ZMod 3) = 0 := by decide
      simp [nsmul_eq_mul, hzero]
    rw [h3, map_one]

theorem card_range_torusE6Two (h2 : (2 : K) = 0) :
    Nat.card (torusE6Two (K := K) h2).range = 3 ^ 4 := by
  rw [Nat.card_congr (MonoidHom.ofInjective (torusE6Two_injective h2)).toEquiv.symm,
    Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem four_le_glaTwoLocalRank_three_E6 [Finite ↥(adjointGroup .E6 K)] :
    4 ≤ GLATwoLocalRank 3 ↥(adjointGroup .E6 K) := by
  obtain ⟨U, E, hU, hU2, hEU, hEel, hEcard, -⟩ :=
    CFSG.StandardType.TableBExc.E6Three.ggTorusLift_adjoint_E6_two (K := K)
      (adjointGroup .E6 K) (MonoidHom.id _) Function.surjective_id
      (by rw [MonoidHom.ker_id]; exact bot_le)
      (CFSG.LieType.Chevalley.single_edge_perfect .E6 K (Or.inr (Or.inr (Or.inl rfl))))
  have h := card_le_pow_glaTwoLocalRank Nat.prime_three hEel hU hU2 hEU
  rw [hEcard] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h

theorem exists_conj_mem_hyperplane_torusE6Two (h2 : (2 : K) = 0) {b : Fin 4 → ZMod 3} {m : ℕ}
    {z : ZMod 3} (hz : z ≠ 0) (hb : ∀ v : Fin 4 → ZMod 3, normE6 v = z → reachB b m v = true)
    {D : Subgroup ↥(torusE6Two (K := K) h2).range} (hD : D.index = 3) :
    ∃ n ∈ Subgroup.normalizer (((torusE6Two (K := K) h2).range : Subgroup (adjointGroup .E6 K)) :
        Set (adjointGroup .E6 K)),
      n * torusE6Two h2 (.ofAdd b) * n⁻¹ ∈ D.map (torusE6Two (K := K) h2).range.subtype := by
  haveI := Fact.mk Nat.prime_three
  have hB : D.map (torusE6Two (K := K) h2).range.subtype ≤ (torusE6Two (K := K) h2).range :=
    Subgroup.map_subtype_le D
  have hcard : Nat.card (D.map (torusE6Two (K := K) h2).range.subtype) * 3 = 3 ^ 4 := by
    calc Nat.card (D.map (torusE6Two (K := K) h2).range.subtype) * 3
        = Nat.card D * 3 := by
          rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      _ = Nat.card D * D.index := by rw [hD]
      _ = Nat.card ↥(torusE6Two (K := K) h2).range := D.card_mul_index
      _ = 3 ^ 4 := card_range_torusE6Two h2
  obtain ⟨f, hf, hfB⟩ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T.exists_dot_eq_zero_imp_mem
      (torusE6Two (K := K) h2) (torusE6Two_injective h2) hB hcard
  obtain ⟨w, hw0, hwz⟩ := exists_dot_eq_zero_normE6 f hf z hz
  obtain ⟨n, hn, hnw⟩ := inOrbit_of_reachB h2 b m w (hb w hwz)
  refine ⟨n, hn, ?_⟩
  rw [hnw]
  exact hfB w (by simpa [Fin.sum_univ_four] using hw0)

theorem stdVanishes_torusE6Two_of_inOrbit (h2 : (2 : K) = 0) {b v : Fin 4 → ZMod 3}
    (hbv : InOrbit h2 b v)
    (hb : IsStdElt 3 (torusE6Two (K := K) h2).range (torusE6Two h2 (.ofAdd b)) →
      StdVanishes (torusE6Two (K := K) h2).range (torusE6Two h2 (.ofAdd b)))
    (hv : IsStdElt 3 (torusE6Two (K := K) h2).range (torusE6Two h2 (.ofAdd v))) :
    StdVanishes (torusE6Two (K := K) h2).range (torusE6Two h2 (.ofAdd v)) := by
  obtain ⟨g, hg, hgb⟩ := hbv
  have hgb' : (MulAut.conj g) (torusE6Two h2 (.ofAdd b)) = torusE6Two h2 (.ofAdd v) := by
    simpa [MulAut.conj_apply] using hgb
  have hBg : ((torusE6Two (K := K) h2).range).map (MulAut.conj g).toMonoidHom =
      (torusE6Two (K := K) h2).range := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hstd : IsStdElt 3 (torusE6Two (K := K) h2).range (torusE6Two h2 (.ofAdd b)) := by
    have h := hv
    rw [← hgb', ← hBg] at h
    exact (isStdElt_map_iff (MulAut.conj g)).1 h
  have h := (stdVanishes_map_iff (MulAut.conj g)).2 (hb hstd)
  rwa [hBg, hgb'] at h

theorem not_isStdElt_of_inOrbit (h2 : (2 : K) = 0) {b v : Fin 4 → ZMod 3} (hbv : InOrbit h2 b v)
    (hb : ¬ IsStdElt 3 (torusE6Two (K := K) h2).range (torusE6Two h2 (.ofAdd b))) :
    ¬ IsStdElt 3 (torusE6Two (K := K) h2).range (torusE6Two h2 (.ofAdd v)) := by
  intro hv
  obtain ⟨g, hg, hgb⟩ := hbv
  have hgb' : (MulAut.conj g) (torusE6Two h2 (.ofAdd b)) = torusE6Two h2 (.ofAdd v) := by
    simpa [MulAut.conj_apply] using hgb
  have hBg : ((torusE6Two (K := K) h2).range).map (MulAut.conj g).toMonoidHom =
      (torusE6Two (K := K) h2).range := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  apply hb
  have h := hv
  rw [← hgb', ← hBg] at h
  exact (isStdElt_map_iff (MulAut.conj g)).1 h

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
