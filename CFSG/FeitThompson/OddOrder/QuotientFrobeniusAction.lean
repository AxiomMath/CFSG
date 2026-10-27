module

public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Local.QuadraticActionsDescendSections
import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
import CFSG.FeitThompson.OddOrder.FreeActionKernelCongruence
import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup
import CFSG.FeitThompson.Foundations.AbelianSolvable

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {U B : Type*} [Group U] [Group B]

theorem apply_eq_self_of_mem_zpowers (ρ : B →* MulAut U) {b : B} {x : U} (hx : ρ b x = x) {a : B}
    (ha : a ∈ Subgroup.zpowers b) : ρ a x = x := by
  obtain ⟨n, rfl⟩ := ha
  have hstab : ρ b ∈ MulAction.stabilizer (MulAut U) x := hx
  have h := zpow_mem hstab n
  rw [map_zpow]
  exact h

theorem zpowers_eq_top_of_ne_one {q : ℕ} (hq : q.Prime) (hB : Nat.card B = q) {b : B}
    (hb : b ≠ 1) : Subgroup.zpowers b = ⊤ := by
  have : Fact (Nat.card B).Prime := ⟨hB ▸ hq⟩
  rcases (Subgroup.zpowers b).eq_bot_or_eq_top_of_prime_card with h | h
  · exact absurd (Subgroup.mem_bot.1 (h ▸ Subgroup.mem_zpowers b)) hb
  · exact h

theorem fixedPoints_range_eq_bot_iff_fixedPointFree (ρ : B →* MulAut U) {b : B}
    (hb : Subgroup.zpowers b = ⊤) :
    FixedPoints.subgroup ρ.range U = ⊥ ↔ MonoidHom.FixedPointFree (ρ b : U → U) := by
  rw [Subgroup.eq_bot_iff_forall]
  exact ⟨fun h u hu => h u ((mem_fixedPoints_range_iff ρ).2 fun a =>
      apply_eq_self_of_mem_zpowers ρ hu (hb ▸ Subgroup.mem_top a)),
    fun h u hu => h u ((mem_fixedPoints_range_iff ρ).1 hu b)⟩

theorem coprime_natCard_of_forall_fixedPointFree [Finite U] [Finite B] (ρ : B →* MulAut U)
    (h : ∀ a : B, a ≠ 1 → MonoidHom.FixedPointFree (ρ a : U → U)) :
    (Nat.card B).Coprime (Nat.card U) := by
  let _inst : MulDistribMulAction B U := MulDistribMulAction.compHom U ρ
  have hdvd : Nat.card B ∣ Nat.card U - 1 :=
    card_dvd_card_sub_one_of_smul_eq_self B U fun k hk a ha => by
      by_contra hane; exact hk (h a hane k ha)
  refine Nat.eq_one_of_dvd_one ?_
  have h3 := Nat.dvd_sub (Nat.gcd_dvd_right (Nat.card B) (Nat.card U))
    ((Nat.gcd_dvd_left (Nat.card B) (Nat.card U)).trans hdvd)
  rwa [Nat.sub_sub_self (Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne')] at h3

section Main

variable [Finite U] {q : ℕ} {ρ : B →* MulAut U} {b : B} {C : Subgroup U}

omit [Group B] in
private theorem finite_of_natCard_eq_prime (hq : q.Prime) (hB : Nat.card B = q) : Finite B :=
  Nat.finite_of_card_ne_zero (by rw [hB]; exact hq.pos.ne')

theorem coprime_natCard_of_fixedPointFree (hq : q.Prime) (hB : Nat.card B = q)
    (hfree : MonoidHom.FixedPointFree (ρ b : U → U)) : q.Coprime (Nat.card U) := by
  have : Finite B := finite_of_natCard_eq_prime hq hB
  rw [← hB]
  exact coprime_natCard_of_forall_fixedPointFree ρ fun a ha u hu => hfree u
    (apply_eq_self_of_mem_zpowers ρ hu (zpowers_eq_top_of_ne_one hq hB ha ▸ Subgroup.mem_top b))

theorem coprime_natCard_quotient_of_fixedPointFree (hq : q.Prime) (hB : Nat.card B = q)
    (hfree : MonoidHom.FixedPointFree (ρ b : U → U)) (C : Subgroup U) [C.Normal] :
    q.Coprime (Nat.card (U ⧸ C)) :=
  (coprime_natCard_of_fixedPointFree hq hB hfree).coprime_dvd_right C.card_quotient_dvd_card

variable [Group.IsSolvable U] [C.Normal]

theorem fixedPoints_quotientAut_range_eq_bot (hq : q.Prime) (hB : Nat.card B = q)
    (hb : Subgroup.zpowers b = ⊤) (hfree : MonoidHom.FixedPointFree (ρ b : U → U))
    (hC : IsInvariantSubgroup ρ C) :
    FixedPoints.subgroup hC.quotientAut.range (U ⧸ C) = ⊥ := by
  have : Finite B := finite_of_natCard_eq_prime hq hB
  have : Fact q.Prime := ⟨hq⟩
  have hcyc : IsCyclic B := isCyclic_of_prime_card hB
  have := hcyc.isMulCommutative
  have : Group.IsSolvable B := isSolvable_of_isMulCommutative
  have hcop : (Nat.card B).Coprime (Nat.card U) :=
    hB ▸ coprime_natCard_of_fixedPointFree hq hB hfree
  rw [fixedPoints_quotientAut_range hC hcop,
    (fixedPoints_range_eq_bot_iff_fixedPointFree ρ hb).2 hfree, Subgroup.map_bot]

theorem fixedPointFree_quotientAut (hq : q.Prime) (hB : Nat.card B = q)
    (hb : Subgroup.zpowers b = ⊤) (hfree : MonoidHom.FixedPointFree (ρ b : U → U))
    (hC : IsInvariantSubgroup ρ C) :
    MonoidHom.FixedPointFree (hC.quotientAut b : U ⧸ C → U ⧸ C) :=
  (fixedPoints_range_eq_bot_iff_fixedPointFree hC.quotientAut hb).1
    (fixedPoints_quotientAut_range_eq_bot hq hB hb hfree hC)

theorem mem_of_inv_mul_apply_mem (hq : q.Prime) (hB : Nat.card B = q)
    (hb : Subgroup.zpowers b = ⊤) (hfree : MonoidHom.FixedPointFree (ρ b : U → U))
    (hC : IsInvariantSubgroup ρ C) {u : U} (hu : u⁻¹ * ρ b u ∈ C) : u ∈ C := by
  have h : hC.quotientAut b (QuotientGroup.mk u : U ⧸ C) = QuotientGroup.mk u := by
    rw [hC.quotientAut_mk]
    exact (QuotientGroup.eq.2 hu).symm
  have := fixedPointFree_quotientAut hq hB hb hfree hC _ h
  rwa [QuotientGroup.eq_one_iff] at this

theorem fixedPoints_quotientAut_range_eq_bot_and_coprime (hq : q.Prime) (hB : Nat.card B = q)
    (hb : Subgroup.zpowers b = ⊤) (hfree : MonoidHom.FixedPointFree (ρ b : U → U))
    (hC : IsInvariantSubgroup ρ C) :
    FixedPoints.subgroup hC.quotientAut.range (U ⧸ C) = ⊥ ∧ q.Coprime (Nat.card (U ⧸ C)) :=
  ⟨fixedPoints_quotientAut_range_eq_bot hq hB hb hfree hC,
    coprime_natCard_quotient_of_fixedPointFree hq hB hfree C⟩

end Main

end CFSG.FeitThompson
