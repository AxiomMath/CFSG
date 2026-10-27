module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2Field

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Ree CFSG.RankThree.PartTwo.KFacts CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem g2_fixSub_outer_involution {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = p ^ f)
    {t : MulAut (adjointGroup Tag.G2 K)} (ht : orderOf t = 2) (htinn : ¬ IsInnerAut t) :
    ∃ e : ℕ, 1 ≤ e ∧ f = 2 * e ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = p ^ e ∧ Nonempty (↥(fixSub t) ≃* adjointGroup Tag.G2 k) ∧
        IsSimpleGroup ↥(fixSub t) ∧ Subgroup.center ↥(fixSub t) = ⊥ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  obtain ⟨hrf, i, δ, τ, hτc, hτord, hδ⟩ := g2_field_descent_of_nf hp hp2 hf K hK Nat.prime_two
    ht htinn (g2_nf_of_ne_three hp hp2 hf K hK hp3 t)
  have hΦ1 : g2FieldHom K τ ≠ 1 := by
    intro h
    have hτ1 : τ = 1 := g2FieldHom_faithful hp hp2 hf K hK τ ⟨1, by rw [h, map_one]⟩
    rw [hτ1, orderOf_one] at hτord
    exact absurd hτord (by norm_num)
  have hti : t ^ i = t := by
    rcases Nat.even_or_odd i with ⟨m, hm⟩ | ⟨m, hm⟩
    · exfalso
      apply hΦ1
      rw [← hδ, hm, ← two_mul, pow_mul, ← ht, pow_orderOf_eq_one, one_pow]
      group
    · rw [hm, pow_succ, pow_mul, ← ht, pow_orderOf_eq_one, one_pow, one_mul]
  rw [hti] at hδ
  obtain ⟨e, he⟩ := hrf
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; omega
    · exact h
  have hfe : f / 2 = e := by omega
  have hkcard : Nat.card (fixSubfield τ) = p ^ e := by
    rw [card_fixSubfield hp hf hK hτord, hfe]
  have hk3 : 3 ≤ Nat.card (fixSubfield τ) := by
    rw [hkcard]
    have h5 : 3 ≤ p := by
      have := hp.two_le
      omega
    calc 3 ≤ p := h5
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he1
  obtain ⟨e₁⟩ := fixSub_conj_equiv t δ
  obtain ⟨e₂⟩ := g2_fixSub_equiv (K := K) τ
  have eqv : ↥(fixSub t) ≃* adjointGroup Tag.G2 (fixSubfield τ) :=
    e₁.trans ((MulEquiv.subgroupCongr (congrArg fixSub hδ)).trans e₂.symm)
  have hcenterk : Subgroup.center (adjointGroup Tag.G2 (fixSubfield τ)) = ⊥ :=
    center_adjointGroup_eq_bot
  have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card (fixSubfield τ) hk3
  have hsimple : IsSimpleGroup ↥(adjointGroup Tag.G2 (fixSubfield τ)) :=
    CFSG.LieType.Simplicity.isSimpleGroup_of_mulEquiv hq
      ((QuotientGroup.quotientMulEquivOfEq hcenterk).trans QuotientGroup.quotientBot).symm
  have := hsimple
  refine ⟨e, he1, he, fixSubfield τ, inferInstance, inferInstance, hkcard, ⟨eqv⟩,
    eqv.isSimpleGroup, ?_⟩
  rw [eq_bot_iff]
  intro x hx
  have hx' : eqv x ∈ Subgroup.center (adjointGroup Tag.G2 (fixSubfield τ)) := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    have h1 := congrArg eqv (hx (eqv.symm y))
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
    exact h1
  rw [hcenterk, Subgroup.mem_bot] at hx'
  exact Subgroup.mem_bot.2 (eqv.injective (hx'.trans (map_one eqv).symm))

end CFSG.GH74.GLS.Stage2.Bender.Thm1
