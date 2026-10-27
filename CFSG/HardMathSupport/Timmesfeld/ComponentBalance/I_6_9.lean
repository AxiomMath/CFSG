module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_8
public import CFSG.LocalAnalysis.GLTheoremB.UniqInputs
public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Elem

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem mem_of_mem_centralizer_orderOf_eq_prime {X : Type*} [Group X] {p : ℕ}
    {B : Subgroup X} (hB : IsSCp p ⊤ B) {x : X} (hx : x ∈ Subgroup.centralizer (B : Set X))
    (hord : orderOf x = p) : x ∈ B := by
  have hxp : x ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one x
  have hc : ∀ b ∈ B, ∀ k ∈ Subgroup.zpowers x, b * k = k * b :=
    GL83.CompFam.zpowers_commute fun b hb => Subgroup.mem_centralizer_iff.1 hx b hb
  have hE := GL83.PiGen.isElemAbelian_sup hB.2.1 (GL83.PiGen.isElemAbelian_zpowers hxp) hc
  have hEB := hB.2.2 _ (le_top) hE le_sup_left
  rw [← hEB]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

theorem hasNormalPComplement_centralizer_of_isSCp {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2) {B : Subgroup X} (hB : IsSCp p ⊤ B) :
    CFSG.HasNormalPComplement p (Subgroup.centralizer (B : Set X)) := by
  have : Fact p.Prime := ⟨hp⟩
  refine hasNormalPComplement_of_central_order_p hodd fun x hx => ?_
  have hxB : (x : X) ∈ B := mem_of_mem_centralizer_orderOf_eq_prime hB x.2
    (by rw [Subgroup.orderOf_coe]; exact hx)
  rw [Subgroup.mem_center_iff]
  intro c
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.1 c.2 _ hxB).symm

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
