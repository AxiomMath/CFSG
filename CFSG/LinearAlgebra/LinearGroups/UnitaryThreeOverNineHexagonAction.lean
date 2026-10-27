module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineHexagonGraph

public section

namespace CFSG.LinearGroups.UnitaryThreeOverNine

open CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F]

@[expose] noncomputable def incAut (hF : Nat.card F = 9) (g : StatedSU 3 3 F) :
    incGraph F ≃g incGraph F where
  toFun := Sum.map (lineAct hF g) (lineActLin hF g)
  invFun := Sum.map (lineAct hF g⁻¹) (lineActLin hF g⁻¹)
  left_inv := by
    rintro (p | T)
    · rw [Sum.map_inl, Sum.map_inl, ← lineAct_mul, inv_mul_cancel, lineAct_one]
    · rw [Sum.map_inr, Sum.map_inr, ← lineActLin_mul, inv_mul_cancel, lineActLin_one]
  right_inv := by
    rintro (p | T)
    · rw [Sum.map_inl, Sum.map_inl, ← lineAct_mul, mul_inv_cancel, lineAct_one]
    · rw [Sum.map_inr, Sum.map_inr, ← lineActLin_mul, mul_inv_cancel, lineActLin_one]
  map_rel_iff' := by
    rintro (p | T) (q | T')
    · simp only [Equiv.coe_fn_mk, Sum.map_inl, not_incGraph_adj_inl_inl]
    · simp only [Equiv.coe_fn_mk, Sum.map_inl, Sum.map_inr, incGraph_adj_inl_inr]
      exact lineAct_mem_lineActLin hF g T' p
    · simp only [Equiv.coe_fn_mk, Sum.map_inl, Sum.map_inr, incGraph_adj_inr_inl]
      exact lineAct_mem_lineActLin hF g T q
    · simp only [Equiv.coe_fn_mk, Sum.map_inr, not_incGraph_adj_inr_inr]

theorem incAut_inl (hF : Nat.card F = 9) (g : StatedSU 3 3 F) (p : NonisoLine F) :
    incAut hF g (Sum.inl p) = Sum.inl (lineAct hF g p) :=
  rfl

theorem incAut_inr (hF : Nat.card F = 9) (g : StatedSU 3 3 F) (T : HexLine F) :
    incAut hF g (Sum.inr T) = Sum.inr (lineActLin hF g T) :=
  rfl

@[expose] noncomputable def incAction (hF : Nat.card F = 9) :
    StatedSU 3 3 F →* (incGraph F ≃g incGraph F) where
  toFun := incAut hF
  map_one' := RelIso.ext fun v => by
    rcases v with p | T
    · rw [incAut_inl, lineAct_one]
      rfl
    · rw [incAut_inr, lineActLin_one]
      rfl
  map_mul' g g' := RelIso.ext fun v => by
    rcases v with p | T
    · rw [incAut_inl, lineAct_mul, RelIso.mul_apply, incAut_inl, incAut_inl]
    · rw [incAut_inr, lineActLin_mul, RelIso.mul_apply, incAut_inr, incAut_inr]

theorem incAction_apply (hF : Nat.card F = 9) (g : StatedSU 3 3 F) :
    incAction hF g = incAut hF g :=
  rfl

theorem incAction_injective (hF : Nat.card F = 9) : Function.Injective (incAction hF) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  refine eq_one_of_lineAct_eq hF g fun L => ?_
  have := DFunLike.congr_fun hg (Sum.inl L)
  rw [incAction_apply, incAut_inl, RelIso.one_apply, Sum.inl.injEq] at this
  rw [this]

end CFSG.LinearGroups.UnitaryThreeOverNine
