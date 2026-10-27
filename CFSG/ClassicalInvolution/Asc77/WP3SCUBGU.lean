module

public import CFSG.ClassicalInvolution.Asc77.WP3SCUBGL

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Generic
open scoped commutatorElement MatrixGroups Matrix

section GeomU

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem isLongRootSU2_exists_not_comm (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    (h5 : 5 ≤ p ^ f) {n : ℕ} {hn : 2 ≤ n} {L : Subgroup (Su K p f n)} {i : Su K p f n}
    (h : IsLongRootSU2 K p f hn L i) : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  have h4 : 4 ≤ Nat.card (CFSG.LieType.Steinberg.fixedSubfield K p f) := by
    rw [CFSG.LieType.Steinberg.card_fixedSubfield hK]
    omega
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp ((h.isClassicalSL2 hK hp).isPerfect h4)
  have hbot : ⁅L, L⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcon x hx y hy
  have hi : i ∈ (⊥ : Subgroup (Su K p f n)) := by rw [← hbot, hperf]; exact h.mem
  have hi1 : i = 1 := Subgroup.mem_bot.mp hi
  have h2' : orderOf i = 2 := (h.isClassicalSL2 hK hp).orderOf_eq_two
  rw [hi1, orderOf_one] at h2'
  omega

theorem eq_of_eigSpacesSU_eq (hp : p ≠ 2) {n : ℕ}
    {hn : 2 ≤ n} {L₁ : Subgroup (Su K p f n)} {i₁ i₂ : Su K p f n}
    (h₁ : IsLongRootSU2 K p f hn L₁ i₁) (hm : minusSpaceSU i₁ = minusSpaceSU i₂)
    (hf : fixSpaceSU i₁ = fixSpaceSU i₂) : i₁ = i₂ := by
  apply suMat_injective
  apply Matrix.ext_of_mulVec_single
  intro j
  have hc := (h₁.isCompl hp).sup_eq_top
  have hv : (Pi.single j (1 : K) : Fin n → K) ∈ minusSpaceSU i₁ ⊔ fixSpaceSU i₁ := by
    rw [hc]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hv
  have e1 : suMat i₁ *ᵥ a = -a := mem_minusSpaceSU.mp ha
  have e2 : suMat i₁ *ᵥ b = b := mem_fixSpaceSU.mp hb
  have e3 : suMat i₂ *ᵥ a = -a := mem_minusSpaceSU.mp (hm ▸ ha)
  have e4 : suMat i₂ *ᵥ b = b := mem_fixSpaceSU.mp (hf ▸ hb)
  rw [← hab, Matrix.mulVec_add, Matrix.mulVec_add, e1, e2, e3, e4]

theorem blockGeom4_longRootSetU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (h5 : 5 ≤ p ^ f) :
    BlockGeom4 (longRootSetU (K := K) (p := p) (f := f) (n := 4) (show 2 ≤ 4 by norm_num)) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hcardF : Nat.card (CFSG.LieType.Steinberg.fixedSubfield K p f) = p ^ f :=
    CFSG.LieType.Steinberg.card_fixedSubfield hK
  have h4 : 4 ≤ Nat.card (CFSG.LieType.Steinberg.fixedSubfield K p f) := by
    rw [hcardF]; omega
  have h2F : (2 : CFSG.LieType.Steinberg.fixedSubfield K p f) ≠ 0 :=
    two_ne_zero_of_odd_natCard (odd_natCard_fixedSubfield hK hp)
  have hn : 2 ≤ 4 := by norm_num
  have hn3 : 3 ≤ 4 := by norm_num
  refine ⟨?_, ?_⟩
  · intro R hR R₁ hR₁ R₂ hR₂ h1 h2'
    obtain ⟨i, hi⟩ := hR
    obtain ⟨i₁, hi₁⟩ := hR₁
    obtain ⟨i₂, hi₂⟩ := hR₂
    have key : ∀ (R' : Subgroup (Su K p f 4)) (i' : Su K p f 4), IsLongRootSU2 K p f hn R' i' →
        (∀ r ∈ R, ∀ s ∈ R', r * s = s * r) →
        minusSpaceSU i' = fixSpaceSU i ∧ fixSpaceSU i' = minusSpaceSU i := by
      intro R' i' hi' h
      have hii : i' ≠ i := by
        intro hii
        obtain ⟨x, hx, y, hy, hxy⟩ := isLongRootSU2_exists_not_comm hK hp h5 hi
        have e : R' = R := by
          rw [hi'.eq_longRootGroupSU h2, hi.eq_longRootGroupSU h2, hii]
        rw [e] at h
        exact hxy (h x hx y hy)
      have hc : Commute i' i := (h i hi.mem i' hi'.mem).symm
      rcases lemma_6_5_su hK hp hn3 hi' hi hc hii with ⟨-, hV1, hV2, -⟩ | ⟨hnot, -⟩
      · have hd : ∀ (L₀ : Subgroup (Su K p f 4)) (j : Su K p f 4),
            IsLongRootSU2 K p f hn L₀ j → Module.finrank K (fixSpaceSU j) = 2 := by
          intro L₀ j hj
          have := Submodule.finrank_add_eq_of_isCompl (hj.isCompl hp)
          rw [hj.finrank_minusSpaceSU h2, Module.finrank_fin_fun] at this
          omega
        have f1 : Module.finrank K (minusSpaceSU i') = Module.finrank K (fixSpaceSU i) := by
          rw [hi'.finrank_minusSpaceSU h2, hd R i hi]
        have f2 : Module.finrank K (minusSpaceSU i) = Module.finrank K (fixSpaceSU i') := by
          rw [hi.finrank_minusSpaceSU h2, hd R' i' hi']
        exact ⟨Submodule.eq_of_le_of_finrank_eq hV1 f1,
          (Submodule.eq_of_le_of_finrank_eq hV2 f2).symm⟩
      · exfalso
        exact hnot (Subgroup.mem_centralizer_iff.mpr fun s hs => (h i hi.mem s hs).symm)
    obtain ⟨a1, b1⟩ := key R₁ i₁ hi₁ h1
    obtain ⟨a2, b2⟩ := key R₂ i₂ hi₂ h2'
    have hi12 : i₁ = i₂ := eq_of_eigSpacesSU_eq hp hi₁ (a1.trans a2.symm) (b1.trans b2.symm)
    rw [hi₁.eq_longRootGroupSU h2, hi₂.eq_longRootGroupSU h2, hi12]
  · intro R hR R' hR' r hr hrc hr1 hcen
    obtain ⟨i, hi⟩ := hR
    obtain ⟨i', hi'⟩ := hR'
    have hri : r = i := by
      rcases CFSG.ClassicalInvolution.ModelFacts.eq_one_or_eq_of_isClassicalSL2_center h2F
        (hi.isClassicalSL2 hK hp) hr hrc with h | h
      · exact absurd h hr1
      · exact h
    have hperf' : ⁅R', R'⁆ = R' :=
      Subgroup.isPerfect_iff.mp ((hi'.isClassicalSL2 hK hp).isPerfect h4)
    have hcomm : ∀ s ∈ R', r * s = s * r := by
      intro s hs
      have := eq_of_central_ratio (MulAut.conj r).toMonoidHom hperf'
        (fun s hs => by simpa using hcen s hs) s hs
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      calc r * s = r * s * r⁻¹ * r := by group
        _ = s * r := by rw [this]
    by_cases hii : i' = i
    · left
      rw [hi'.eq_longRootGroupSU h2, hi.eq_longRootGroupSU h2, hii]
    · right
      have hc : Commute i' i := by
        have := hcomm i' hi'.mem
        rw [hri] at this
        exact this.symm
      rcases lemma_6_5_su hK hp hn3 hi' hi hc hii with ⟨hcm, -⟩ | ⟨hnot, -⟩
      · exact fun s hs s' hs' => hcm s hs s' hs'
      · exfalso
        refine hnot (Subgroup.mem_centralizer_iff.mpr fun s hs => ?_)
        have := hcomm s hs
        rw [hri] at this
        exact this.symm

end GeomU

end CFSG.ClassicalInvolution.Asc77
