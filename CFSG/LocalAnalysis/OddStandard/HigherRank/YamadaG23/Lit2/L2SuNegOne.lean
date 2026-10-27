module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2PslM

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup Matrix

theorem l2_su_neg_one {K : Type} [Field K] {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (hn : 0 < n) (he : Even n) (hq : Odd (p ^ f)) :
    ∃ m : ↥(CFSG.Open.StatedSU n (p ^ f) K),
      ((m : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = -1 ∧ m ≠ 1 ∧
      m * m = 1 ∧
      m ∈ (CFSG.Open.StatedScalars (Fin n) K).subgroupOf (CFSG.Open.StatedSU n (p ^ f) K) ∧
      ∀ u ∈ (CFSG.Open.StatedScalars (Fin n) K).subgroupOf
          (CFSG.Open.StatedSU n (p ^ f) K), u * u = 1 → u = 1 ∨ u = m := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero 2 (pow_ne_zero f hp.ne_zero))
  have hqmod : Nat.card K % 2 = 1 := by
    rw [hK]
    exact Nat.odd_iff.mp hq.pow
  have h2 : (2 : K) ≠ 0 := l2_two_ne_zero hqmod
  have hneg : (-1 : K) ≠ 1 := by
    intro h
    apply h2
    have h' : (-1 : K) - 1 = 0 := sub_eq_zero.mpr h
    rw [show (-1 : K) - 1 = -(2 : K) by ring] at h'
    exact neg_eq_zero.mp h'
  have hn1 : 1 ≤ n := hn
  let c : Kˣ := -1
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ CFSG.Open.StatedSU n (p ^ f) K := by
    rw [CFSG.LinearGroups.scalar_mem_statedSU_iff hp hK hn1 c]
    exact ⟨by simpa [c] using Even.neg_one_pow (α := Kˣ) he,
      by simpa [c] using Even.neg_one_pow (α := Kˣ) hq.add_one⟩
  let m : ↥(CFSG.Open.StatedSU n (p ^ f) K) :=
    ⟨Matrix.GeneralLinearGroup.scalar (Fin n) c, hmem⟩
  have hmval : ((m : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = -1 := by
    change Matrix.scalar (Fin n) (c : K) = -1
    rw [show (c : K) = -1 by simp [c]]
    ext i j
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h
      simp
    · simp [h]
  have hmne : m ≠ 1 := by
    intro h
    apply hneg
    have h' := congrArg (fun x : ↥(CFSG.Open.StatedSU n (p ^ f) K) =>
      ((x : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) h
    rw [hmval] at h'
    simpa using h'
  have hmm : m * m = 1 := by
    apply Subtype.ext
    change Matrix.GeneralLinearGroup.scalar (Fin n) c *
      Matrix.GeneralLinearGroup.scalar (Fin n) c = 1
    rw [← map_mul, show c * c = 1 by simp [c, neg_mul_neg], map_one]
  have hinj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin n) : Kˣ →* Matrix.GeneralLinearGroup (Fin n) K) := by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    intro a b hab
    have h := congrArg (fun g : Matrix.GeneralLinearGroup (Fin n) K =>
      (g : Matrix (Fin n) (Fin n) K)) hab
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_inj] at h
    exact Units.ext h
  refine ⟨m, hmval, hmne, hmm, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact MonoidHom.mem_range.mpr ⟨c, rfl⟩
  · intro u hu huu
    rw [Subgroup.mem_subgroupOf] at hu
    obtain ⟨r, hr⟩ : ∃ r : Kˣ,
        Matrix.GeneralLinearGroup.scalar (Fin n) r = (u : Matrix.GeneralLinearGroup (Fin n) K) :=
      MonoidHom.mem_range.mp (show (u : Matrix.GeneralLinearGroup (Fin n) K) ∈
        (Matrix.GeneralLinearGroup.scalar (Fin n)).range from hu)
    have huu' : (u : Matrix.GeneralLinearGroup (Fin n) K) *
        (u : Matrix.GeneralLinearGroup (Fin n) K) = 1 := by
      have := congrArg (fun x : ↥(CFSG.Open.StatedSU n (p ^ f) K) =>
        (x : Matrix.GeneralLinearGroup (Fin n) K)) huu
      simpa using this
    have hrr : r * r = 1 := by
      refine hinj ?_
      rw [map_mul, hr, huu', map_one]
    have hval : (r : K) * (r : K) = 1 := by
      have := congrArg (fun x : Kˣ => (x : K)) hrr
      simpa using this
    rcases mul_self_eq_one_iff.mp hval with h1 | h1
    · left
      have hr1 : r = 1 := by
        apply Units.ext
        simpa using h1
      apply Subtype.ext
      change (u : Matrix.GeneralLinearGroup (Fin n) K) = 1
      rw [← hr, hr1, map_one]
    · right
      have hrc : r = c := by
        apply Units.ext
        rw [h1]
        simp [c]
      apply Subtype.ext
      change (u : Matrix.GeneralLinearGroup (Fin n) K) =
        Matrix.GeneralLinearGroup.scalar (Fin n) c
      rw [← hr, hrc]

end CFSG.OddStandard.HigherRank.YamadaG23
