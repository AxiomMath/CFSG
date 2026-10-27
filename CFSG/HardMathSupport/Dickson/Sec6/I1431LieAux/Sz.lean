module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Outer
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Split

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.ComponentClassification.CatLeaf
open CFSG.HardMathSupport.Dickson.Sec6.I923 (FamSz FamOK noL2OuterAt_sz
  not_three_dvd_suzuki_numerator)

theorem eq_one_of_conj_pow_three {Y : Type} [Group Y] (h3S : ¬ 3 ∣ Nat.card (Y ⧸ Subgroup.center Y))
    [Finite Y] {y : Y} (hy : (MulAut.conj y) ^ 3 = 1) : MulAut.conj y = 1 := by
  have hz : y ^ 3 ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun a : MulAut Y => a g) hy
    simp only [← map_pow, MulAut.conj_apply, MulAut.one_apply] at this
    calc g * y ^ 3 = (y ^ 3 * g * (y ^ 3)⁻¹) * y ^ 3 := by rw [this]
      _ = y ^ 3 * g := by group
  have h1 : (QuotientGroup.mk y : Y ⧸ Subgroup.center Y) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 hz
  have hord : orderOf (QuotientGroup.mk y : Y ⧸ Subgroup.center Y) = 1 := by
    have hd3 : orderOf (QuotientGroup.mk y : Y ⧸ Subgroup.center Y) ∣ 3 := orderOf_dvd_of_pow_eq_one h1
    rcases (Nat.dvd_prime Nat.prime_three).1 hd3 with h | h
    · exact h
    · exact absurd (h ▸ orderOf_dvd_natCard _) h3S
  have hy1 : (QuotientGroup.mk y : Y ⧸ Subgroup.center Y) = 1 := orderOf_eq_one_iff.1 hord
  have hyc : y ∈ Subgroup.center Y := (QuotientGroup.eq_one_iff y).1 hy1
  ext g
  simp only [MulAut.conj_apply, MulAut.one_apply]
  rw [← (Subgroup.mem_center_iff.1 hyc) g]
  group

theorem y1431_noCfg_sz
    (hO : LieOrderFormulasInput) : Y1431NoCfgAt FamSz := by
  intro Y _ _ Â ξ J q c t n p f hadm ht hF hm q0 hq0 hqq
  obtain rfl := hF
  have hq := c.quasisimple
  haveI : Group.IsPerfect Y := ⟨hq.1⟩
  obtain ⟨hfin, hM, -⟩ := hO _ .twistedB2 n p f hadm hm
  have h3S : ¬ 3 ∣ Nat.card (Y ⧸ Subgroup.center Y) := by
    obtain ⟨-, -, hn0, hp2, hfodd, -⟩ := hadm
    subst hn0
    subst hp2
    have hdiv : lieOrderDivisor .twistedB2 0 (2 ^ f) = 1 := by simp [lieOrderDivisor]
    rw [hdiv, mul_one] at hM
    rw [hM]
    exact not_three_dvd_suzuki_numerator hfodd
  have hP : FamOK (Y ⧸ Subgroup.center Y) := fun ψ hψ3 hninn =>
    ⟨1, ψ, by simp, noL2OuterAt_sz _ _ n p f hadm ht rfl hm ψ hψ3 hninn⟩
  have hinn := c.inner_of_famOK hq0 hqq (MulEquiv.refl _) hP
  have hinn' : IsInnerAut ξ :=
    isInnerAut_of_isInnerAut_centerDescend ((isInnerAut_congr (MulEquiv.refl _) _).1 hinn)
  obtain ⟨y, hy⟩ := hinn'
  have hy3 : (MulAut.conj y) ^ 3 = 1 := by rw [hy]; exact c.pow_three
  exact c.ne_one (hy ▸ eq_one_of_conj_pow_three h3S hy3)

end CFSG.HardMathSupport.Dickson.Sec6.I1431
