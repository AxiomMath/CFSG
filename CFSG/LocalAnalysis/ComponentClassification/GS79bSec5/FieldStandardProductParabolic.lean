module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseBPerfect
import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Basic

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree.CaseBNotation

open Subgroup

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : CFSG.OddStandard.Seitz77.Datum A}
  {Vi : Subgroup G} {q : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {w : WData d Vi q}
  {D : LeviData A Vi K}

omit [Finite G] [Finite K] [CharP K 2] in
private theorem sup_map_conj_le (N : CaseBNotation w D) :
    N.M₁ ⊔ N.M₁.map (MulAut.conj d.t).toMonoidHom ≤ w.N := by
  refine sup_le N.M₁_le fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := hx
  have h : d.t * y * d.t⁻¹ ∈ w.N :=
    mul_mem (mul_mem w.t_norm (N.M₁_le hy)) (inv_mem w.t_norm)
  simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    inv_eq_of_mul_eq_one_right d.t_mul_self] using h

omit [Finite G] in
private theorem commutator_sup_map_conj (N : CaseBNotation w D) (hK3 : 3 ≤ Nat.card K) :
    ⁅N.M₁ ⊔ N.M₁.map (MulAut.conj d.t).toMonoidHom,
      N.M₁ ⊔ N.M₁.map (MulAut.conj d.t).toMonoidHom⁆ =
      N.M₁ ⊔ N.M₁.map (MulAut.conj d.t).toMonoidHom := by
  refine le_antisymm (Subgroup.commutator_le_self _) (sup_le ?_ ?_)
  · have h := Subgroup.commutator_mono
      (le_sup_left : N.M₁ ≤ N.M₁ ⊔ N.M₁.map (MulAut.conj d.t).toMonoidHom)
      (le_sup_left : N.M₁ ≤ N.M₁ ⊔ N.M₁.map (MulAut.conj d.t).toMonoidHom)
    rwa [N.commutator_M₁ hK3] at h
  · have hB : ⁅N.M₁.map (MulAut.conj d.t).toMonoidHom,
        N.M₁.map (MulAut.conj d.t).toMonoidHom⁆ =
        N.M₁.map (MulAut.conj d.t).toMonoidHom := by
      rw [← Subgroup.map_commutator, N.commutator_M₁ hK3]
    have h := Subgroup.commutator_mono
      (le_sup_right : N.M₁.map (MulAut.conj d.t).toMonoidHom ≤
        N.M₁ ⊔ N.M₁.map (MulAut.conj d.t).toMonoidHom)
      (le_sup_right : N.M₁.map (MulAut.conj d.t).toMonoidHom ≤
        N.M₁ ⊔ N.M₁.map (MulAut.conj d.t).toMonoidHom)
    rwa [hB] at h

theorem perfectResidualOf_N_eq (N : CaseBNotation w D) (hB : w.CaseB D.lev.range) {f : ℕ}
    (hf : 2 ≤ f) (hKc : Nat.card K = 2 ^ f) :
    CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf w.N =
      N.M₁ ⊔ N.M₁.map (MulAut.conj d.t).toMonoidHom := by
  have hK3 : 3 ≤ Nat.card K := by
    rw [hKc]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine le_antisymm ?_ ?_
  · exact N.perfect_le_M_sup hB hf hKc
      (CFSG.OddStandard.Seitz77.CaseB45.perfectResidualOf_le' w.N)
      (CFSG.OddStandard.Seitz77.CaseB45.perfectResidualOf_perfect w.N)
  · exact CFSG.OddStandard.Seitz77.CaseB45.le_perfectResidualOf_of_perfect
      (sup_map_conj_le N) (commutator_sup_map_conj N hK3)

theorem card_perfectResidualOf_N (N : CaseBNotation w D) (hB : w.CaseB D.lev.range) {f : ℕ}
    (hf : 2 ≤ f) (hKc : Nat.card K = 2 ^ f) (hKq : Nat.card K = q) :
    Nat.card (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf w.N) =
      (q ^ 3 * (q ^ 2 - 1)) ^ 2 := by
  rw [N.perfectResidualOf_N_eq hB hf hKc,
    card_sup_of_commute N.M₁_comm N.M₁_inf,
    Subgroup.card_map_of_injective (MulAut.conj d.t).injective, N.card_M₁ hKq]
  ring

end CFSG.LocalAnalysis.EvenBN.LinearThree.CaseBNotation
