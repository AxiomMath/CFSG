module

public import CFSG.GH74.Generic.BProg.B2.PumpupTableOutL3
public import CFSG.GH74.Generic.BProg.B2.PumpupTableOutU3
public import CFSG.GH74.Generic.S3.V1InnerLib

import CFSG.GH74.KGroups.L3EpsUniInv

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1L3PkgOut

open Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.KGroups.L3Eps CFSG.GH74.Generic.S3
  CFSG.Assembly.LowTwoRank
open CFSG.GH74.Generic.BProg.B2.PumpupTableOutL3 (lin_graph_centralizer_psl2)
open CFSG.GH74.Generic.BProg.B2.PumpupTableOutU3 (graphData_of_cover_psl2)
open scoped MatrixGroups commutatorElement

theorem exists_psl2_fixed_lin {K : Type} [Group K] {F : Type} [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hFc : Nat.card F = p ^ f) (hf : Odd f) (h2 : (2 : F) ≠ 0)
    (h5 : 5 ≤ Nat.card F) (e : K ≃* projectiveSL 3 F) {c : MulAut K} (hc2 : c * c = 1)
    (hout : c ∉ (MulAut.conj : K →* MulAut K).range) :
    ∃ N : Subgroup K, CFSG.IsQuasisimple ↥N ∧ (∀ n ∈ N, c n = n) ∧
      (∀ x : K, c x = x → ∀ n ∈ N, x * n * x⁻¹ ∈ N) ∧
      Nonempty (↥N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  have hF2 : ringChar F ≠ 2 := fun h => h2 (by
    have : CharP F 2 := h ▸ ringChar.charP F
    exact CharTwo.two_eq_zero)
  have hc2' : conjAutEquiv e c * conjAutEquiv e c = 1 := by
    rw [← conjAutEquiv_mul, hc2, conjAutEquiv_one]
  have hout' : conjAutEquiv e c ∉
      (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range :=
    fun h => hout (conjAutEquiv_mem_inner e h)
  obtain ⟨A, hAs, hA⟩ := lin_involution_form hp hFc hf h2 hc2' hout'
  obtain ⟨N, hq, hfix, hconj, -, ⟨eN⟩⟩ := lin_graph_centralizer_psl2 hF2 (by omega) hAs
  rw [← hA] at hfix hconj
  have hfixK : ∀ x : K, c x = x → conjAutEquiv e c (e x) = e x := fun x hx => by
    rw [conjAutEquiv_apply, hx]
  have hmem : ∀ x : K, x ∈ N.map (e.symm : projectiveSL 3 F →* K) ↔ e x ∈ N := fun x => by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro h
      exact ⟨e x, h, by simp⟩
  refine ⟨N.map (e.symm : projectiveSL 3 F →* K), ?_, ?_, ?_,
    ⟨(MulEquiv.subgroupMap e.symm N).symm.trans eN⟩⟩
  · exact LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupMap e.symm N) hq
  · intro n hn
    rw [hmem] at hn
    apply e.injective
    rw [← conjAutEquiv_apply]
    exact hfix _ hn
  · intro x hx n hn
    rw [hmem] at hn ⊢
    rw [map_mul, map_mul, map_inv]
    exact hconj _ (hfixK x hx) _ hn

theorem exists_psl2_fixed_uni {K : Type} [Group K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ f) (hX : StatedClassicalModel K .PSU 3 p f) {c : MulAut K} (hc2 : c * c = 1)
    (hout : c ∉ (MulAut.conj : K →* MulAut K).range) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (N : Subgroup K), Nat.card k = p ^ f ∧
      CFSG.IsQuasisimple ↥N ∧ (∀ n ∈ N, c n = n) ∧
      (∀ x : K, c x = x → ∀ n ∈ N, x * n * x⁻¹ ∈ N) ∧
      Nonempty (↥N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k) := by
  obtain ⟨hadm, F, _, _, hF, ⟨e₀⟩⟩ := hX
  have hf : 1 ≤ f := hadm.2.1
  have hU : UnitaryFieldData p f F := ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨θ, hθ⟩ := Uni.exists_cover_of_equiv hU e₀
  obtain ⟨N, hGD, ⟨eN⟩⟩ := graphData_of_cover_psl2 hU hp2 h5 hq hθ hc2 hout
  have : Finite F := hU.finite
  exact ⟨hU.fixedField, inferInstance, inferInstance, N, hU.card_fixedField, hGD.quasisimple,
    hGD.fixed, hGD.conj_mem, ⟨eN⟩⟩

theorem exists_psl2_fixed {L : Type} [Group L] [Finite L] (hL : B1.QShape3SD L) {γ : MulAut L}
    (hγ : γ * γ = 1) (hγout : γ ∉ (MulAut.conj : L →* MulAut L).range) :
    ∃ (p f : ℕ) (k : Type) (_ : Field k) (_ : Finite k) (N : Subgroup L),
      p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Nat.card k = p ^ f ∧ CFSG.IsQuasisimple ↥N ∧
      (∀ n ∈ N, γ n = n) ∧ (∀ x : L, γ x = x → ∀ n ∈ N, x * n * x⁻¹ ∈ N) ∧
      Nonempty (↥N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k) := by
  obtain ⟨p, f, hp, hp2, hq, h | h⟩ := hL
  · have h5 : 5 ≤ p ^ f := by omega
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_projectiveSL_equiv (stated_of_lieModel_PSL h.1)
    have hpodd : Odd p := hp.odd_of_ne_two hp2
    have hf : Odd f := odd_of_pow_mod_four_eq_three hpodd h.2
    have hodd : Odd (Nat.card F) := by rw [hF]; exact hpodd.pow
    have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
    obtain ⟨N, hN, hfix, hnorm, hN2⟩ := exists_psl2_fixed_lin hp hF hf h2 (by omega) e hγ hγout
    exact ⟨p, f, F, inferInstance, inferInstance, N, hp, hp2, hf.pos, h5, hF, hN, hfix, hnorm, hN2⟩
  · have h5 : 5 ≤ p ^ f := by omega
    obtain ⟨k, _, _, N, hk, hN, hfix, hnorm, hN2⟩ :=
      exists_psl2_fixed_uni hp hp2 h5 (stated_of_lieModel_PSU h.1) hγ hγout
    have hf : 1 ≤ f := by
      by_contra hf0
      have : f = 0 := by omega
      subst this
      simp at hq
    exact ⟨p, f, k, inferInstance, inferInstance, N, hp, hp2, hf, h5, hk, hN, hfix, hnorm, hN2⟩

end S1L3PkgOut

end CFSG.GH74.Generic.BProg.B3
