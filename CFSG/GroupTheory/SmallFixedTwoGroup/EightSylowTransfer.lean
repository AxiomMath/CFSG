module

public import CFSG.LargeExtraspecial.GLRTransfer
public import CFSG.GF2Type.Aschbacher1976Full.HSBurnside

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open Subgroup

theorem false_of_fixed_involution {E : Type*} [Group E] [Finite E]
    (hE : ∀ N : Subgroup E, N.index ≠ 2) (P : Sylow 2 E)
    (hab : ∀ a ∈ (P : Subgroup E), ∀ b ∈ (P : Subgroup E), a * b = b * a)
    {p : E} (hpP : p ∈ (P : Subgroup E)) (hp2 : p * p = 1)
    (hfix : ∀ n ∈ normalizer ((P : Subgroup E) : Set E), n * p * n⁻¹ = p)
    {M : Subgroup E} (hMP : M ≤ (P : Subgroup E)) (hM : M.relIndex (P : Subgroup E) = 2)
    (hpM : p ∉ M) : False := by
  classical
  obtain ⟨y, hyM, -⟩ :=
    CFSG.LargeExtraspecial.GLR.exists_extremal_conj_mem_of_sq_eq (G := E) hE
      (T := (P : Subgroup E)) (U := M) P.isPGroup' P.not_dvd_index hMP hM hpP hpM hp2
      (by simp) (fun x _ => by simpa using M.one_mem)
  have hweak : ∀ g : E, CFSG.conjugate (P : Subgroup E) g ≤ (P : Subgroup E) →
      CFSG.conjugate (P : Subgroup E) g = (P : Subgroup E) := by
    intro g hg
    refine Subgroup.eq_of_le_of_card_ge hg ?_
    rw [CFSG.conjugate, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  obtain ⟨n, hnN, hn⟩ :=
    CFSG.GF2Type.Aschbacher1976Full.HS.burnside_fusion (p := 2) (a := p) (g := y⁻¹)
      P (P : Subgroup E) le_rfl hab hweak hpP (hMP (by simpa using hyM))
  have hnp : n * p * n⁻¹ = y⁻¹ * p * y := by simpa using hn
  rw [hfix n hnN] at hnp
  exact hpM (hnp.symm ▸ hyM)

end CFSG.GroupTheory.SmallFixedTwoGroup
