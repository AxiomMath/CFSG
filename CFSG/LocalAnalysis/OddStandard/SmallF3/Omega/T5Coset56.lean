module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Step56
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverActConv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CosetOmega
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5LiftConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem mul_self_eq_one_of_orderOf_eq_two' {A : Type*} [Group A] {a : A}
    (h : orderOf a = 2) : a * a = 1 := by
  rw [← pow_two, ← h, pow_orderOf_eq_one]

theorem asc82Coset56_of (hS : Asc82SchurU43) : Asc82Coset56 := by
  intro G _ _ L hL t ht ht2 b e hb2 he2 hInd hue
  obtain ⟨u, huL, hue⟩ := hue
  have hb2' : b * b = 1 := mul_self_eq_one_of_orderOf_eq_two' hb2
  have he2' : e * e = 1 := mul_self_eq_one_of_orderOf_eq_two' he2
  obtain ⟨α, V, i1, i2, i3, Q, hQ, e₀, x, hdim, hsgn, hind, hsim⟩ := hInd
  letI := i1
  letI := i2
  letI := i3
  obtain ⟨φ, h, he₀⟩ := t5_cover_of_model hS hL hdim hsgn e₀
  obtain ⟨y, hyx, _, s, hss, hsty, hsy⟩ := hsim
  have hs3 : invDim s = 3 := congrArg Prod.fst hsty
  have hx' : (QuotientGroup.mk (orthToSim Q s) : ProjSim Q) = x := by
    rw [← projOrthToProjSim_toProj (Q := Q) s, hsy, hyx]
  have hb : CoverAct L φ b (orthToSim Q s) :=
    t5_coverAct_of_inducesViaP hL h he₀ hind hx'
  subst e
  let ū : omegaGroup hQ := φ ⟨u, huL⟩
  let g : OGroup Q := (ū : OGroup Q) * s
  have he : CoverAct L φ (u * b) (orthToSim Q g) := t5_coverAct_mul_left hb huL
  have hg2 : g * g = 1 ∨ g * g = piOrth Q := t5_sq_mem_pi_of_coverAct h he2' he
  have hcos : g * g = 1 ∧
      ((invType g = invType s ∧ ∃ c ∈ omegaGroup hQ, c * s * c⁻¹ = g) ∨
        invDim g = 1 ∨ invDim g = 5) :=
    t5_coset_omega hQ hdim hsgn hss hs3 hg2 ⟨ū, ū.2, rfl⟩
  rcases hcos.2 with hA | hcase
  · obtain ⟨_, c, hcΩ, hc⟩ := hA
    rcases t5_conj_of_coverAct hL h ht ht2 hb2' he2' ⟨u, huL, rfl⟩ hb he (c := ⟨c, hcΩ⟩) hc
      with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · have hne : toProj Q g ≠ 1 := by
      intro hg1
      have hmem : g ∈ piGroup Q := (QuotientGroup.eq_one_iff (N := piGroup Q) g).mp hg1
      rcases mem_piGroup_iff.mp hmem with h1 | h1
      · rw [h1] at hcase
        have h1d : invDim (1 : OGroup Q) = 0 := by
          simp only [invDim]
          rw [commSp_one, finrank_bot]
        rw [h1d] at hcase
        rcases hcase with h | h <;> omega
      · rw [h1] at hcase
        have hpi : invDim (piOrth Q) = Module.finrank (ZMod 3) V := by
          simp only [invDim]
          rw [commSp_piOrth, finrank_top]
        rw [hpi, hdim] at hcase
        rcases hcase with h | h <;> omega
    rcases hcase with h1 | h5
    · have htype : invType g = (1, invSign g) := by
        simp only [invType]
        exact Prod.ext h1 rfl
      refine Or.inr (Or.inr ⟨invSign g, V, i1, i2, i3, Q, hQ, e₀,
        QuotientGroup.mk (orthToSim Q g), hdim, hsgn,
        t5_inducesViaP_of_coverAct he₀ he, ?_⟩)
      exact ⟨toProj Q g, projOrthToProjSim_toProj g, hne, g, hcos.1, htype, rfl⟩
    · have hdim' : invDim (piOrth Q * g) = 1 := by
        have hh := congrArg Prod.fst (invType_piOrth_mul hQ hcos.1)
        simp only [invType] at hh
        rw [hdim, h5] at hh
        omega
      have htype : invType (piOrth Q * g) = (1, invSign (piOrth Q * g)) := by
        simp only [invType]
        exact Prod.ext hdim' rfl
      refine Or.inr (Or.inr ⟨invSign (piOrth Q * g), V, i1, i2, i3, Q, hQ, e₀,
        QuotientGroup.mk (orthToSim Q g), hdim, hsgn,
        t5_inducesViaP_of_coverAct he₀ he, ?_⟩)
      exact ⟨toProj Q g, projOrthToProjSim_toProj g, hne, piOrth Q * g,
        piOrth_mul_mul_self hcos.1, htype, by
          rw [map_mul, toProj_piOrth, one_mul]⟩

end CFSG.OddStandard.SmallF3.Omega
