module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterTorus
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterDiag
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterCore

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291Out

open Matrix CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.LieType.Universal.Unitary (conjTr SUid_eq_statedSU mem_SUid)

section Uni

variable {n r f : ℕ} [Fact r.Prime] {K : Type} [Field K] [Finite K] [CharP K r]

theorem diagGL_mem_statedSU (hK : Nat.card K = (r ^ f) ^ 2) {p : ℕ} (hpq : p ∣ r ^ f + 1)
    (d : Fin n → Kˣ) (hd : ∀ j, d j ^ p = 1) (hdet : ∏ j, d j = 1) :
    (diagGL d : GL (Fin n) K) ∈ StatedSU n (r ^ f) K := by
  rw [← SUid_eq_statedSU hK n, mem_SUid, coe_diagGL]
  refine ⟨?_, ?_⟩
  · rw [det_diagonal, ← Units.coe_prod, hdet, Units.val_one]
  · rw [conjTr, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal]
    have h1 : ∀ j, (d j : K) ^ (r ^ f + 1) = 1 := fun j => by
      obtain ⟨m, hm⟩ := hpq
      rw [← Units.val_pow_eq_pow_val, hm, pow_mul, hd j, one_pow, Units.val_one]
    have h2 : (fun j => (unitaryInvolution K r f) ((d j : Kˣ) : K) * ((d j : Kˣ) : K)) =
        fun _ => (1 : K) := funext fun j => by
      rw [unitaryInvolution_apply, ← pow_succ]
      exact h1 j
    rw [h2]
    exact Matrix.diagonal_one

theorem exists_uni_torus (hK : Nat.card K = (r ^ f) ^ 2) {p : ℕ} (hp : p.Prime) (hn : 5 ≤ n)
    (hpq : p ∣ r ^ f + 1) {σ : K ≃+* K} (hσ : σ ^ p = 1) :
    ∃ F : (Fin 3 → Multiplicative (ZMod p)) →* StatedSU n (r ^ f) K,
      Function.Injective ((QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf
        (StatedSU n (r ^ f) K))).comp F) ∧
      ∀ x, glAut σ ((F x : StatedSU n (r ^ f) K) : GL (Fin n) K) =
        ((F x : StatedSU n (r ^ f) K) : GL (Fin n) K) := by
  have hpK : p ∣ Nat.card K - 1 := by
    have h2 : (r ^ f) ^ 2 - 1 = (r ^ f + 1) * (r ^ f - 1) := by
      have := Nat.sq_sub_sq (r ^ f) 1
      rwa [one_pow] at this
    rw [hK, h2]
    exact hpq.mul_right _
  obtain ⟨κ, hκp, hκdet, hκinj⟩ := exists_diag_torus (K := K) hp hn hpK
  let F : (Fin 3 → Multiplicative (ZMod p)) →* StatedSU n (r ^ f) K :=
    ((diagGL : (Fin n → Kˣ) →* GL (Fin n) K).comp κ).codRestrict (StatedSU n (r ^ f) K)
      (fun x => diagGL_mem_statedSU hK hpq (κ x) (hκp x) (hκdet x))
  have hFcoe : ∀ x, (((F x : StatedSU n (r ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal (fun j => ((κ x j : Kˣ) : K)) := fun x => rfl
  refine ⟨F, ?_, fun x => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    have h1 := (QuotientGroup.eq_one_iff _).1 hx
    obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.1 h1 : _ ∈ StatedScalars (Fin n) K)
    refine hκinj x c fun j => Units.ext ?_
    have h3 : ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (((F x : StatedSU n (r ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
      congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hc
    have h4 := congrFun (congrFun h3 j) j
    rw [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq, hFcoe x,
      diagonal_apply_eq] at h4
    exact h4.symm
  · refine Units.ext ?_
    rw [coe_glAut, hFcoe]
    ext i j
    rw [Matrix.map_apply]
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
      exact fixed_of_pow_eq_one hp hσ (hκp x i)
    · rw [diagonal_apply_ne _ hij, map_zero]

end Uni

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291Out
