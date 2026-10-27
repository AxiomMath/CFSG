module

public import CFSG.ClassicalInvolution.Asc77.WP3SCUNGa
import CFSG.ClassicalInvolution.Asc77.AscT8V11

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Generic
open scoped commutatorElement MatrixGroups Matrix

section Perfect

variable {X : Type*} [Group X]

theorem comm_center_mul_left {c : X} (hc : c ∈ Subgroup.center X) (a b : X) :
    ⁅c * a, b⁆ = ⁅a, b⁆ := by
  exact T8V.comm_center_mul_left hc a b

theorem comm_center_mul_right {c : X} (hc : c ∈ Subgroup.center X) (a b : X) :
    ⁅a, c * b⁆ = ⁅a, b⁆ := by
  exact T8V.comm_center_mul_right hc a b

theorem eq_of_central_ratio (φ : X →* X) {P : Subgroup X} (hP : ⁅P, P⁆ = P)
    (h : ∀ p ∈ P, φ p * p⁻¹ ∈ Subgroup.center X) : ∀ p ∈ P, φ p = p := by
  exact T8V.eq_of_central_ratio φ hP.ge h

end Perfect

section Geom

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem eq_of_eigSpaces_eq (h2 : (2 : F) ≠ 0) {n : ℕ} {L₁ : Subgroup SL(n, F)}
    {i₁ i₂ : SL(n, F)} (hn : 2 ≤ n) (h₁ : IsLongRootSL2 hn L₁ i₁)
    (hm : minusSpace i₁ = minusSpace i₂) (hf : fixSpace i₁ = fixSpace i₂) : i₁ = i₂ := by
  apply Subtype.ext
  apply Matrix.ext_of_mulVec_single
  intro j
  have hc := (h₁.isCompl h2).sup_eq_top
  have hv : (Pi.single j (1 : F) : Fin n → F) ∈ minusSpace i₁ ⊔ fixSpace i₁ := by
    rw [hc]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hv
  have e1 : (i₁ : Matrix (Fin n) (Fin n) F) *ᵥ a = -a := mem_minusSpace.mp ha
  have e2 : (i₁ : Matrix (Fin n) (Fin n) F) *ᵥ b = b := mem_fixSpace.mp hb
  have e3 : (i₂ : Matrix (Fin n) (Fin n) F) *ᵥ a = -a := mem_minusSpace.mp (hm ▸ ha)
  have e4 : (i₂ : Matrix (Fin n) (Fin n) F) *ᵥ b = b := mem_fixSpace.mp (hf ▸ hb)
  rw [← hab, Matrix.mulVec_add, Matrix.mulVec_add, e1, e2, e3, e4]

theorem isLongRootSL2_exists_not_comm (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) {n : ℕ}
    {hn : 2 ≤ n} {L : Subgroup SL(n, F)} {i : SL(n, F)} (h : IsLongRootSL2 hn L i) :
    ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp ((h.isClassicalSL2 h2).isPerfect h4)
  have hbot : ⁅L, L⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcon x hx y hy
  have hi : i ∈ (⊥ : Subgroup SL(n, F)) := by rw [← hbot, hperf]; exact h.mem
  have hi1 : i = 1 := Subgroup.mem_bot.mp hi
  have h2' : orderOf i = 2 := (h.isClassicalSL2 h2).orderOf_eq_two
  rw [hi1, orderOf_one] at h2'
  omega

theorem blockGeom4_longRootSet (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) :
    BlockGeom4 (longRootSet (K := F) (show 2 ≤ 4 by norm_num)) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_natCard hodd
  have h4 : 4 ≤ Nat.card F := by omega
  have hn : 2 ≤ 4 := by norm_num
  have hn3 : 3 ≤ 4 := by norm_num
  refine ⟨?_, ?_⟩
  · intro R hR R₁ hR₁ R₂ hR₂ h1 h2'
    obtain ⟨i, hi⟩ := hR
    obtain ⟨i₁, hi₁⟩ := hR₁
    obtain ⟨i₂, hi₂⟩ := hR₂
    have key : ∀ (R' : Subgroup SL(4, F)) (i' : SL(4, F)), IsLongRootSL2 hn R' i' →
        (∀ r ∈ R, ∀ s ∈ R', r * s = s * r) →
        minusSpace i' = fixSpace i ∧ fixSpace i' = minusSpace i := by
      intro R' i' hi' h
      have hii : i' ≠ i := by
        intro hii
        obtain ⟨x, hx, y, hy, hxy⟩ := isLongRootSL2_exists_not_comm h2 h4 hi
        have e : R' = R := by
          rw [hi'.eq_longRootGroup h2, hi.eq_longRootGroup h2, hii]
        rw [e] at h
        exact hxy (h x hx y hy)
      have hc : Commute i' i := (h i hi.mem i' hi'.mem).symm
      rcases lemma_6_5 h2 hn3 hi' hi hc hii with ⟨-, hV1, hV2, -⟩ | ⟨hnot, -⟩
      · have hd : ∀ (L₀ : Subgroup SL(4, F)) (j : SL(4, F)), IsLongRootSL2 hn L₀ j →
            Module.finrank F (fixSpace j) = 2 := by
          intro L₀ j hj
          have := Submodule.finrank_add_eq_of_isCompl (hj.isCompl h2)
          rw [hj.finrank_minusSpace h2, Module.finrank_fin_fun] at this
          omega
        have f1 : Module.finrank F (minusSpace i') = Module.finrank F (fixSpace i) := by
          rw [hi'.finrank_minusSpace h2, hd R i hi]
        have f2 : Module.finrank F (minusSpace i) = Module.finrank F (fixSpace i') := by
          rw [hi.finrank_minusSpace h2, hd R' i' hi']
        exact ⟨Submodule.eq_of_le_of_finrank_eq hV1 f1,
          (Submodule.eq_of_le_of_finrank_eq hV2 f2).symm⟩
      · exfalso
        exact hnot (Subgroup.mem_centralizer_iff.mpr fun s hs => (h i hi.mem s hs).symm)
    obtain ⟨a1, b1⟩ := key R₁ i₁ hi₁ h1
    obtain ⟨a2, b2⟩ := key R₂ i₂ hi₂ h2'
    have hi12 : i₁ = i₂ := eq_of_eigSpaces_eq h2 hn hi₁ (a1.trans a2.symm) (b1.trans b2.symm)
    rw [hi₁.eq_longRootGroup h2, hi₂.eq_longRootGroup h2, hi12]
  · intro R hR R' hR' r hr hrc hr1 hcen
    obtain ⟨i, hi⟩ := hR
    obtain ⟨i', hi'⟩ := hR'
    have hri : r = i := by
      rcases CFSG.ClassicalInvolution.ModelFacts.eq_one_or_eq_of_isClassicalSL2_center h2
        (hi.isClassicalSL2 h2) hr hrc with h | h
      · exact absurd h hr1
      · exact h
    have hperf' : ⁅R', R'⁆ = R' := Subgroup.isPerfect_iff.mp ((hi'.isClassicalSL2 h2).isPerfect h4)
    have hcomm : ∀ s ∈ R', r * s = s * r := by
      intro s hs
      have := eq_of_central_ratio (MulAut.conj r).toMonoidHom hperf'
        (fun s hs => by simpa using hcen s hs) s hs
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      calc r * s = r * s * r⁻¹ * r := by group
        _ = s * r := by rw [this]
    by_cases hii : i' = i
    · left
      rw [hi'.eq_longRootGroup h2, hi.eq_longRootGroup h2, hii]
    · right
      have hc : Commute i' i := by
        have := hcomm i' hi'.mem
        rw [hri] at this
        exact this.symm
      rcases lemma_6_5 h2 hn3 hi' hi hc hii with ⟨hcm, -⟩ | ⟨hnot, -⟩
      · exact fun s hs s' hs' => hcm s hs s' hs'
      · exfalso
        refine hnot (Subgroup.mem_centralizer_iff.mpr fun s hs => ?_)
        have := hcomm s hs
        rw [hri] at this
        exact this.symm

end Geom

end CFSG.ClassicalInvolution.Asc77
