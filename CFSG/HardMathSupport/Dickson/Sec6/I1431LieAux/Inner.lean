module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Outer

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

theorem Y1431Cfg.mem_innerAut_of_outDerived {Y P : Type} [Group Y] [Finite Y] [Group P]
    {Â : Subgroup (MulAut Y)} {ξ : MulAut Y} {J : Subgroup Y} {q : ℕ}
    (c : Y1431Cfg d4Vocab Y Â ξ J q) (e : (Y ⧸ Subgroup.center Y) ≃* P)
    (hOut : ¬ IsD4Type Y → ∀ τ ∈ innAutDerived P, τ ^ 3 = 1 → IsInnerAut τ) :
    ∀ a ∈ Â, a ∈ innerAut Y := by
  intro a ha
  have h := c.inn a ha
  simp only [d4Vocab] at h
  split_ifs at h with hd
  · exact h
  · haveI : Group.IsPerfect Y := ⟨c.quasisimple.1⟩
    have h1 : MulAut.congr e (centerDescend Y a) ∈ innAutDerived P :=
      (mem_innAutDerived_congr e).2 (centerDescend_mem_innAutDerived h)
    have h3 : (MulAut.congr e (centerDescend Y a)) ^ 3 = 1 := by
      rw [← map_pow, ← map_pow, c.elemAbelian.2 a ha, map_one, map_one]
    exact isInnerAut_of_isInnerAut_centerDescend ((isInnerAut_congr e _).1 (hOut hd _ h1 h3))

theorem Y1431Cfg.exists_inner_pair {V : InndiagVocab} {Y : Type} [Group Y] [Finite Y]
    {Â : Subgroup (MulAut Y)} {ξ : MulAut Y} {J : Subgroup Y} {q : ℕ}
    (c : Y1431Cfg V Y Â ξ J q) (hin : ∀ a ∈ Â, a ∈ innerAut Y) :
    ∃ x z : Y, ξ = MulAut.conj x ∧ MulAut.conj z ∈ Â ∧
      MulAut.conj z ∉ Subgroup.zpowers ξ ∧ x ^ 3 ∈ Subgroup.center Y ∧
      z ^ 3 ∈ Subgroup.center Y ∧ ⁅x, z⁆ ∈ Subgroup.center Y := by
  have hξ3 : ξ ^ 3 = 1 := c.pow_three
  have hξo : orderOf ξ = 3 := orderOf_eq_prime hξ3 c.ne_one
  have hzc : Nat.card (Subgroup.zpowers ξ) = 3 := by rw [Nat.card_zpowers, hξo]
  haveI : Finite (Subgroup.zpowers ξ) := Nat.finite_of_card_ne_zero (by rw [hzc]; norm_num)
  obtain ⟨η, hη, hηξ⟩ : ∃ η ∈ Â, η ∉ Subgroup.zpowers ξ := by
    by_contra hcon
    push Not at hcon
    have hle : Â ≤ Subgroup.zpowers ξ := hcon
    have := Subgroup.card_le_of_le hle
    rw [c.card, hzc] at this
    omega
  obtain ⟨x, hx⟩ := hin ξ c.mem
  obtain ⟨z, hz⟩ := hin η hη
  have hxz : MulAut.conj x * MulAut.conj z = MulAut.conj z * MulAut.conj x := by
    have habel : ∀ u ∈ Â, ∀ v ∈ Â, u * v = v * u := fun u hu v hv => by
      have := c.elemAbelian.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩
      exact congrArg Subtype.val this
    rw [hx, hz]
    exact habel _ c.mem _ hη
  have hcen : ∀ w : Y, MulAut.conj w = 1 → w ∈ Subgroup.center Y := fun w hw => by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut Y => φ g) hw
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * w = (w * g * w⁻¹) * w := by rw [this]
      _ = w * g := by group
  refine ⟨x, z, hx.symm, hz ▸ hη, hz ▸ hηξ, hcen _ ?_, hcen _ ?_, hcen _ ?_⟩
  · rw [map_pow, hx, hξ3]
  · have hη3 : η ^ 3 = 1 := c.elemAbelian.2 η hη
    rw [map_pow, hz, hη3]
  · rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 hxz

end CFSG.HardMathSupport.Dickson.Sec6.I1431
