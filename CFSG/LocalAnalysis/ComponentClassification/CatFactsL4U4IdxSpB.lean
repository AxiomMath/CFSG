module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4FixQS
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace IdxSp

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup CFSG.ComponentClassification.CatFactsSp4

variable {K : Type} [Field K]

theorem two_mul_card_le_of_inner [Finite K] (hodd : Odd (Nat.card K))
    {u : StatedProj (StatedSp 2 K)} (hu : orderOf u = 2)
    {X : Subgroup (StatedProj (StatedSp 2 K))} (hXC : X ≤ centralizer {u}) (hXp : ⁅X, X⁆ = X) :
    2 * Nat.card X ≤ (Nat.card (Matrix.SpecialLinearGroup (Fin 2) K)) ^ 2 := by
  have h2 := two_ne_zero_of_odd_card hodd
  obtain ⟨g, hg⟩ := exists_conj_of_orderOf_eq_two hodd hu
  set c : MulAut (StatedProj (StatedSp 2 K)) := MulAut.conj g⁻¹ with hc
  set X' := X.map c.toMonoidHom with hX'
  have hX'card : Nat.card X' = Nat.card X := card_map_of_injective c.injective
  have hX'p : ⁅X', X'⁆ = X' := by rw [hX', ← map_commutator, hXp]
  have hconj : ∀ v, g⁻¹ * u * g = v → X' ≤ centralizer {v} := by
    rintro v hv _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff, ← hv]
    have hxu : x * u = u * x := mem_centralizer_singleton_iff.mp (hXC hx)
    simp only [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * x * g * (g⁻¹ * u * g) = g⁻¹ * (x * u) * g := by group
      _ = g⁻¹ * (u * x) * g := by rw [hxu]
      _ = g⁻¹ * u * g * (g⁻¹ * x * g) := by group
  set s := Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) with hs
  have hs1 : 1 ≤ s := Nat.card_pos
  rcases hg with hg | hg
  · have hle : X' ≤ X0 K := perfect_le_map_centralizer (T1 K) (hconj _ hg) hX'p
    have h1 : Nat.card (X0 K) * 2 = Nat.card (centralizer ({T1 K} : Set (StatedSp 2 K))) := by
      have := card_map_fixOf_mul_two h2 (MulAut.conj (T1 K)) (fun z hz => by
        rw [MulAut.conj_apply, mem_center_iff.mp (mem_center_of_mem_spScalars hz) (T1 K),
          mul_inv_cancel_right])
      rwa [fixOf_conj] at this
    have h3 : Nat.card (centralizer ({T1 K} : Set (StatedSp 2 K))) ≤ s * s := by
      have e : centralizer ({T1 K} : Set (StatedSp 2 K)) = (blkSL K).range := by
        ext x
        exact mem_centralizer_T1_iff h2
      rw [e, ← Nat.card_prod]
      exact Nat.card_le_card_of_surjective _ (blkSL K).rangeRestrict_surjective
    have h4 := Subgroup.card_le_of_le hle
    rw [← hX'card]
    nlinarith
  · have hle : X' ≤ Lsub K := perfect_le_L h2 (hconj _ hg) hX'p
    have h3 : Nat.card (Lsub K) ≤ s := by
      have e : Lsub K = ((proj 2 K).comp (diagSL K)).range := by
        rw [Lsub, MonoidHom.range_comp]
      rw [e]
      exact Nat.card_le_card_of_surjective _ ((proj 2 K).comp (diagSL K)).rangeRestrict_surjective
    have h4 := Subgroup.card_le_of_le hle
    have hs2 : 2 ≤ s := by
      rw [hs, GorensteinWalter.sl2_card_formula]
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      have h3 : 3 ≤ Nat.card K := by
        obtain ⟨k, hk⟩ := hodd
        omega
      have h9 : 9 ≤ Nat.card K ^ 2 := by nlinarith
      have h8 : 8 ≤ Nat.card K ^ 2 - 1 := by omega
      calc 2 ≤ 3 * 8 := by norm_num
        _ ≤ Nat.card K * (Nat.card K ^ 2 - 1) := Nat.mul_le_mul h3 h8
    rw [← hX'card]
    nlinarith

end IdxSp

end CFSG.ComponentClassification.CatFactsL4U4
