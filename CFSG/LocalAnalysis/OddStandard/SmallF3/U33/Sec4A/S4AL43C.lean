module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL43A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL43B

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem pow_four_mem_twoCore_of_mem_ctxW (h : Ctx t L S x₁ x₂ lam rho tau) {w : G}
    (hw : w ∈ ctxW t x₁ x₂) : w ^ 4 ∈ twoCore t := by
  haveI : IsMulCommutative (ctxW t x₁ x₂) := h.toCtx0.abelian_W
  have hbase_le_W : baseGrp x₁ x₂ ≤ ctxW t x₁ x₂ := le_sup_right
  have hcommW : ∀ a ∈ ctxW t x₁ x₂, ∀ b ∈ ctxW t x₁ x₂, a * b = b * a := by
    intro a ha b hb
    simpa using congrArg Subtype.val
      (mul_comm' (⟨a, ha⟩ : ctxW t x₁ x₂) (⟨b, hb⟩ : ctxW t x₁ x₂))
  have hbase_le_L : baseGrp x₁ x₂ ≤ L := by
    obtain ⟨hx₁, hx₂, -⟩ := generators_mem_L h.toCtx0
    refine (Subgroup.closure_le (K := L)).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hx₁
    · exact hx₂
  have hbase_pow : ∀ b ∈ baseGrp x₁ x₂, b ^ 4 = 1 := by
    intro b hb
    change b ∈ closure ({x₁, x₂} : Set G) at hb
    refine Subgroup.closure_induction (p := fun b _ => b ^ 4 = 1) ?_ ?_ ?_ ?_ hb
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · rw [← h.wreath.ord_x₁, pow_orderOf_eq_one]
      · rw [← h.wreath.ord_x₂, pow_orderOf_eq_one]
    · simp
    · intro x y hx hy ihx ihy
      have hxW : x ∈ ctxW t x₁ x₂ := hbase_le_W (show x ∈ baseGrp x₁ x₂ from hx)
      have hyW : y ∈ ctxW t x₁ x₂ := hbase_le_W (show y ∈ baseGrp x₁ x₂ from hy)
      have hc : Commute x y := hcommW x hxW y hyW
      rw [hc.mul_pow 4, ihx, ihy, mul_one]
    · intro x hx ihx
      simpa [ihx] using inv_pow x 4
  have hcomm_P_B : ∀ a ∈ twoCore t, ∀ b ∈ baseGrp x₁ x₂, a * b = b * a :=
    fun a ha b hb => twoCore_commute h.hyp a ha b (hbase_le_L hb)
  obtain ⟨q, hq, b, hb, hwb⟩ := (mem_sup_iff_of_commute hcomm_P_B).mp hw
  have hc : Commute q b := hcomm_P_B q hq b hb
  rw [hwb, hc.mul_pow 4, hbase_pow b hb, mul_one]
  exact Subgroup.pow_mem (twoCore t) hq 4

theorem false_of_eight_le_card (h : Ctx t L S x₁ x₂ lam rho tau) (h2 : 2 ∣ S.index)
    (h8 : 8 ≤ Nat.card (twoCore t)) : False := by
  obtain ⟨p, hp, hp4⟩ := exists_fourth_root_of_eight_le_card h.hyp h8
  obtain ⟨n, hn, hnt⟩ := exists_swap_of_l42 h h2
  have hpW : p ∈ ctxW t x₁ x₂ := Subgroup.mem_sup_left hp
  have hwW : n * p * n⁻¹ ∈ ctxW t x₁ x₂ := conj_mem_ctxW_of_mem_normalizer h hn hpW
  have hw4 : (n * p * n⁻¹) ^ 4 ∈ twoCore t := pow_four_mem_twoCore_of_mem_ctxW h hwW
  have htz : (n * p * n⁻¹) ^ 4 = t * (x₁ * x₂) ^ 2 := by
    rw [conj_pow, hp4, hnt]
  have htz_mem : t * (x₁ * x₂) ^ 2 ∈ twoCore t := by
    rwa [htz] at hw4
  have hz_mem : (x₁ * x₂) ^ 2 ∈ twoCore t := by
    have hmem : t⁻¹ * (t * (x₁ * x₂) ^ 2) ∈ twoCore t :=
      Subgroup.mul_mem (twoCore t) (Subgroup.inv_mem (twoCore t) h.hyp.mem_twoCore) htz_mem
    simpa using hmem
  have hz_inf : (x₁ * x₂) ^ 2 ∈ twoCore t ⊓ L := ⟨hz_mem, (y_z_mem_L h.toCtx0).2⟩
  rw [h.hyp.twoCore_inf, Subgroup.mem_bot] at hz_inf
  exact (z_mul_self_ne_one h.toCtx0).2 hz_inf

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
