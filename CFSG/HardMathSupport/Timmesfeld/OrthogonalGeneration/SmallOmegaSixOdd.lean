module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaFour
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

theorem alt_aut_odd_inner (n : ℕ) (hn : 5 ≤ n) (hn6 : n ≠ 6) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (σ : MulAut ↥(alternatingGroup (Fin n))) (h : σ ^ p = 1) :
    ∃ y : ↥(alternatingGroup (Fin n)), σ = MulAut.conj y := by
  obtain ⟨τ, rfl⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    n hn hn6).2 σ
  have hτ : τ ^ p = 1 := by
    apply (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6).1
    rw [map_pow, h, map_one]
  have hsign : Equiv.Perm.sign τ = 1 := by
    have h1 : (Equiv.Perm.sign τ) ^ p = 1 := by rw [← map_pow, hτ, map_one]
    have hodd : Odd p := hp.odd_of_ne_two hp2
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h2 | h2
    · exact h2
    · rw [h2, hodd.neg_one_pow] at h1
      exact absurd h1 (by decide)
  refine ⟨⟨τ, Equiv.Perm.mem_alternatingGroup.2 hsign⟩, ?_⟩
  ext x
  rfl

theorem aut_odd_inner_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (p : ℕ)
    (hH : ∀ σ : MulAut H, σ ^ p = 1 → ∃ y : H, σ = MulAut.conj y)
    (σ : MulAut G) (h : σ ^ p = 1) : ∃ y : G, σ = MulAut.conj y := by
  obtain ⟨y, hy⟩ := hH (MulAut.congr e σ) (by rw [← map_pow, h, map_one])
  refine ⟨e.symm y, ?_⟩
  ext x
  have := congrArg (fun τ : MulAut H => (τ (e x))) hy
  simp only [MulAut.congr_apply, MulEquiv.coe_trans, Function.comp_apply,
    MulAut.conj_apply] at this
  apply e.injective
  simpa using this

theorem statedOmega_quadMinus_two_aut_odd_inner {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (σ : MulAut ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 2 (ZMod 2) 1 1)))
    (h : σ ^ p = 1) : ∃ y, σ = MulAut.conj y :=
  aut_odd_inner_of_mulEquiv statedOmega_quadMinus_two_mulEquiv_alt5 p
    (fun τ hτ => alt_aut_odd_inner 5 le_rfl (by decide) p hp hp2 τ hτ) σ h

theorem statedOmega_quadPlus_three_aut_odd_inner {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (σ : MulAut ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 3 (ZMod 2))))
    (h : σ ^ p = 1) : ∃ y, σ = MulAut.conj y :=
  aut_odd_inner_of_mulEquiv statedOmega_quadPlus_three_mulEquiv_alt8 p
    (fun τ hτ => alt_aut_odd_inner 8 (by decide) (by decide) p hp hp2 τ hτ) σ h

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

