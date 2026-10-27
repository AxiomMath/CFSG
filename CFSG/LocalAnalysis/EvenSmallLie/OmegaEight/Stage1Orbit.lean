module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Coord
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Check

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem qfV_genMat (ε : Eps) (i : Fin 6) (v : V6) : qfV ε (genMat ε i *ᵥ v) = qfV ε v := by
  have h := (checks ε).1
  simp only [genCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  rw [qfV, qfV, genMat, vecBits_mulVec, (h i i.isLt).2 _ (vecBits_lt v)]

theorem genMat_mul_genInvMat (ε : Eps) (i : Fin 6) : genMat ε i * genInvMat ε i = 1 := by
  have h := (checks ε).1
  simp only [genCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  rw [genMat, genInvMat, ← toMat_bmul]
  exact toMat_eq_one_of_bIsId (h i i.isLt).1.1

theorem genInvMat_mul_genMat (ε : Eps) (i : Fin 6) : genInvMat ε i * genMat ε i = 1 := by
  have h := (checks ε).1
  simp only [genCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  rw [genMat, genInvMat, ← toMat_bmul]
  exact toMat_eq_one_of_bIsId (h i i.isLt).1.2

variable {G : Type*} [Group G]

namespace RadicalData

variable {ε : Eps} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  (hR : RadicalData ε L U Q P a ψ p)
include hR

theorem qfV_lin {x : G} (hx : x ∈ P) (v : V6) : qfV ε (lin ψ x v) = qfV ε v := by
  have key : ∀ y ∈ closure ((Q : Set G) ∪ Set.range p),
      ∀ v, qfV ε (lin ψ y v) = qfV ε v := by
    intro y hy
    induction hy using closure_induction with
    | mem y hy =>
      rcases hy with hy | ⟨i, rfl⟩
      · intro v; rw [hR.lin_of_mem_Q hy]
      · intro v; rw [hR.lin_p, qfV_genMat]
    | one => intro v; rw [hR.lin_one]
    | mul y z hy hz ihy ihz =>
      intro v
      rw [hR.lin_mul (hR.closure_le_normalizer hy) (hR.closure_le_normalizer hz), ihy, ihz]
    | inv y hy ihy =>
      intro v
      conv_rhs => rw [← hR.lin_inv (hR.closure_le_normalizer hy) v]
      rw [ihy]
  exact key x (hR.P_le hx) v

theorem exists_lin_eq_base {v : V6} (hv : v ≠ 0) :
    ∃ x ∈ P, lin ψ x (toVec 6 (if qfB ε (vecBits v) then n0 ε else 1)) = v := by
  have h := (checks ε).2.1
  simp only [orbitCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
  have hv0 : vecBits v ≠ 0 := by
    intro h0
    apply hv
    rw [← toVec_vecBits v, h0, ← vecBits_zero, toVec_vecBits]
  refine ⟨wordElt p ((orbitWords ε).getD (vecBits v) []), hR.wordElt_mem _, ?_⟩
  rw [hR.lin_wordElt, ((h _ (vecBits_lt v)).resolve_left hv0), toVec_vecBits]

theorem exists_lin_eq {v w : V6} (hv : v ≠ 0) (hw : w ≠ 0) (h : qfV ε v = qfV ε w) :
    ∃ x ∈ P, lin ψ x v = w := by
  obtain ⟨x, hx, hxv⟩ := hR.exists_lin_eq_base hv
  obtain ⟨y, hy, hyw⟩ := hR.exists_lin_eq_base hw
  have hb : qfB ε (vecBits v) = qfB ε (vecBits w) := by
    rw [qfV, qfV] at h
    revert h
    cases qfB ε (vecBits v) <;> cases qfB ε (vecBits w) <;> simp [bz]
  refine ⟨y * x⁻¹, mul_mem hy (inv_mem hx), ?_⟩
  have h1 : lin ψ x⁻¹ v = toVec 6 (if qfB ε (vecBits v) then n0 ε else 1) := by
    have := hR.lin_inv' (hR.P_le_normalizer hx) (toVec 6 (if qfB ε (vecBits v) then n0 ε else 1))
    rwa [hxv] at this
  rw [hR.lin_mul (hR.P_le_normalizer hy) (hR.P_le_normalizer (inv_mem hx)), h1, hb, hyw]

end RadicalData

end CFSG.EvenSmallLie.OmegaEight.Stage1
