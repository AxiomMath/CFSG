module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBLocal

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.Monster.Generated CFSG.Monster.B.Pinned
open _root_.Timmesfeld.M3B (F3 Vec Mat E AD vget vofFn zeroV mget aget B0 LA)

section Generic

variable {n : ℕ} (B : Fin n → Fin n → ZMod 3)

theorem ecomm_fst (x y : Elt n) : (ecomm B x y).1 = 0 := by
  simp only [ecomm, emul, epow, eone]
  funext i
  simp only [Pi.add_apply, Pi.zero_apply, zero_add]
  have : (3 : ZMod 3) = 0 := rfl
  linear_combination (x.1 i + y.1 i) * this

end Generic

section Datum

theorem orderOf_tbw : orderOf tbw = 3 := tbCommData.orderOf_z

theorem tbw_pow_val_inj {e e' : ZMod 3} (h : tbw ^ e.val = tbw ^ e'.val) : e = e' := by
  have h' := pow_eq_pow_iff_modEq.1 h
  rw [orderOf_tbw] at h'
  have := (ZMod.natCast_eq_natCast_iff' e.val e'.val 3).2 h'
  simpa using this

theorem nf_injective {x y : Elt 12} (h : tbSys.nf x = tbSys.nf y) : x = y := by
  have h1 : x.1 = y.1 := by rw [← coord_nf x, ← coord_nf y, h]
  refine Prod.ext h1 ?_
  have h2 : tbSys.nf (x.1, x.2) = tbSys.nf (x.1, y.2) := by
    rw [h]; rw [show y = (y.1, y.2) from rfl, ← h1]
  unfold Sys.nf at h2
  exact tbw_pow_val_inj (mul_left_cancel h2)

theorem conj_tbw_eq {g : Gmat} {D₀ : Fin 12 → Elt 12}
    (h : ∀ i, g⁻¹ * tbq i * g = tbSys.nf (D₀ i)) :
    g⁻¹ * tbw * g = tbSys.nf (ecomm tbSys.B (D₀ 1) (D₀ 0)) := by
  have e1 : g⁻¹ * tbw * g = (g⁻¹ * tbq 1 * g)⁻¹ * (g⁻¹ * tbq 0 * g)⁻¹ * (g⁻¹ * tbq 1 * g) *
      (g⁻¹ * tbq 0 * g) := by
    rw [tbw_eq_bcomm]; group
  have h1 : g⁻¹ * tbq 1 * g = tbSys.nf (D₀ 1) := h 1
  have h0 : g⁻¹ * tbq 0 * g = tbSys.nf (D₀ 0) := h 0
  rw [e1, h1, h0, Sys.nf_ecomm tbSys_good]

theorem nf_zero_fst (x : Elt 12) (hx : x.1 = 0) : tbSys.nf x = tbw ^ x.2.val := by
  rw [show x = (0, x.2) by rw [← hx]]
  exact tbSys_nf_zero x.2

theorem exists_isAct {g : Gmat} (hg : g ∈ tbL) : ∃ D : ActD 12, IsAct tbSys g D := by
  have hrow : ∀ i, ∃ e : Elt 12, g⁻¹ * tbq i * g = tbSys.nf e := fun i =>
    exists_nf_of_mem (tbL_conj g hg _ (tbq_mem i))
  choose D₀ hD₀ using hrow
  refine ⟨(D₀, (ecomm tbSys.B (D₀ 1) (D₀ 0)).2), hD₀, ?_⟩
  show g⁻¹ * tbw * g = tbw ^ (ecomm tbSys.B (D₀ 1) (D₀ 0)).2.val
  rw [conj_tbw_eq hD₀, nf_zero_fst _ (ecomm_fst _ _ _)]

theorem isAct_unique {g : Gmat} {D D' : ActD 12} (h : IsAct tbSys g D) (h' : IsAct tbSys g D') :
    D = D' := by
  refine Prod.ext (funext fun i => nf_injective ((h.1 i).symm.trans (h'.1 i))) ?_
  exact tbw_pow_val_inj (h.2.symm.trans h'.2)

theorem mul_inv_mem_centralizer {a b : Gmat} {D : ActD 12} (ha : IsAct tbSys a D)
    (hb : IsAct tbSys b D) : a * b⁻¹ ∈ Subgroup.centralizer (QQ : Set Gmat) := by
  have hgen : ∀ i, (a * b⁻¹) * tbq i = tbq i * (a * b⁻¹) := by
    intro i
    have e : a⁻¹ * tbq i * a = b⁻¹ * tbq i * b := (ha.1 i).trans (hb.1 i).symm
    calc a * b⁻¹ * tbq i = a * (b⁻¹ * tbq i * b) * b⁻¹ := by group
      _ = a * (a⁻¹ * tbq i * a) * b⁻¹ := by rw [e]
      _ = tbq i * (a * b⁻¹) := by group
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hc : Commute h (a * b⁻¹) := by
    induction hh using Subgroup.closure_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact (hgen i).symm
    | one => exact Commute.one_left _
    | mul x y _ _ hx hy => exact hx.mul_left hy
    | inv x _ hx => exact hx.inv_left
  exact hc.eq

end Datum

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
