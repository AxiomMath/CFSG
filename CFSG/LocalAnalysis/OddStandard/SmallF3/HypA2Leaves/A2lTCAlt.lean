module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.AltArm
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig32B
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigPerm

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint Equiv CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.SolMax

theorem a2l_isSimpleChevalleyOver_three_of_alt_six {S : Type} [Group S]
    (h : Nonempty (S ≃* alternatingGroup (Fin 6))) : HarrisLit.IsSimpleChevalleyOver 3 S :=
  ⟨.PSL, 2, 2, Or.inl ⟨by decide,
    CFSG.LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six S h⟩⟩

theorem a2l_eq_six_of_factorial_div_two {k : ℕ} (hk : 5 ≤ k)
    (h : k.factorial / 2 = 360 ∨ k.factorial / 2 = 6048 ∨ k.factorial / 2 = 25920) : k = 6 := by
  by_cases hk10 : 10 ≤ k
  · have h10 : Nat.factorial 10 ≤ k.factorial := Nat.factorial_le hk10
    have h10' : Nat.factorial 10 = 3628800 := by decide
    omega
  · interval_cases k <;> first | rfl | (exfalso; revert h; decide)

theorem a2l_alt_arm {S : Type} [Group S] [Finite S] {m : ℕ} (hm5 : 5 ≤ m)
    (e : S ≃* alternatingGroup (Fin m)) {σ : MulAut S} {P : Subgroup S}
    (hP : CatLeaf.ProperFixedComponent σ P) (hS : TCSmall (↥P ⧸ Open.fusionZStar ↥P)) :
    m = 6 ∨ ∃ m' : ℕ, 4 ≤ m' ∧ m = 2 * m' ∧ ∃ u ∈ P, ∃ p q s t : Fin m, p ≠ q ∧ p ≠ s ∧
      p ≠ t ∧ q ≠ s ∧ q ≠ t ∧ s ≠ t ∧
      ((e u : alternatingGroup (Fin m)) : Perm (Fin m)) = swap p q * swap s t := by
  classical
  by_cases hm6 : m = 6
  · exact Or.inl hm6
  refine Or.inr ?_
  obtain ⟨hP', ⟨f⟩⟩ := hP.map e
  obtain ⟨τ, hτ2, hστ, hdeg, ⟨eA⟩⟩ :=
    CatLeaf.exists_involution_of_properFixedComponent_alternating hm5 hm6 hP'
  have hττ : τ * τ = 1 := by rw [← sq, ← hτ2, pow_orderOf_eq_one]
  have hcardPZ : Nat.card (↥P ⧸ Open.fusionZStar ↥P) =
      (Finset.univ.filter fun x => τ x = x).card.factorial / 2 := by
    have : Nontrivial ↥(Finset.univ.filter fun x => τ x = x) := by
      rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_coe]
      omega
    rw [Nat.card_congr (f.trans eA).toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_coe]
  have hΩ6 : (Finset.univ.filter fun x => τ x = x).card = 6 := by
    refine a2l_eq_six_of_factorial_div_two hdeg ?_
    rw [← hcardPZ]
    exact a2l_card_tcSmall hS
  have hsum : (Finset.univ.filter fun x => τ x = x).card + τ.support.card = m := by
    have hsupp : τ.support = Finset.univ.filter fun x => ¬ τ x = x := rfl
    rw [hsupp, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have hmod := CatFC.parity_of_involution m τ hττ
  have hle : P.map e.toMonoidHom ≤ fixAlt τ := by
    have hPF : P.map e.toMonoidHom ≤
        fixedSubgroup (MulAut.conjNormal (H := alternatingGroup (Fin m)) τ) := by
      rw [← hστ]
      exact hP'.2.1
    have hPc : IsPComponent 2 ((P.map e.toMonoidHom).subgroupOf
        (fixedSubgroup (MulAut.conjNormal (H := alternatingGroup (Fin m)) τ))) := by
      rw [← hστ]
      exact hP'.2.2.1
    intro x hx
    rw [mem_fixAlt]
    intro ω hω
    rw [Finset.mem_compl, Perm.mem_support, not_not]
    by_contra hcon
    exact (Perm.mem_support.mp hω) (support_of_isPComponent_fixed_conj hτ2 hPF hPc x hx ω hcon)
  have hcardfix : Nat.card (fixAlt τ) = 360 := by
    have h6 : m - τ.support.card = 6 := by omega
    rw [card_fixAlt (by omega), h6]
    decide
  have h360 : 360 ≤ Nat.card P := by
    have h1 : Nat.card (↥P ⧸ Open.fusionZStar ↥P) = 360 := by
      rw [hcardPZ, hΩ6]
      decide
    exact h1 ▸ Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have hcardmap : Nat.card (P.map e.toMonoidHom) = Nat.card P :=
    (Nat.card_congr (P.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
  have hP360 : Nat.card P = 360 := by
    have h1 := Subgroup.card_le_of_le hle
    omega
  have hPeq : P.map e.toMonoidHom = fixAlt τ :=
    Subgroup.eq_of_le_of_card_ge hle (by omega)
  obtain ⟨p, q, s, t, hpq, hps, hpt, hqs, hqt, hst, hp, hq, hs, ht⟩ :
      ∃ p q s t : Fin m, p ≠ q ∧ p ≠ s ∧ p ≠ t ∧ q ≠ s ∧ q ≠ t ∧ s ≠ t ∧
        τ p = p ∧ τ q = q ∧ τ s = s ∧ τ t = t := by
    let ι : ↥(Finset.univ.filter fun x => τ x = x) ≃ Fin 6 :=
      Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hΩ6)
    have hfix : ∀ ω : ↥(Finset.univ.filter fun x => τ x = x), τ ω.1 = ω.1 := fun ω =>
      (Finset.mem_filter.mp ω.2).2
    refine ⟨(ι.symm 0).1, (ι.symm 1).1, (ι.symm 2).1, (ι.symm 3).1, ?_, ?_, ?_, ?_, ?_, ?_,
      hfix _, hfix _, hfix _, hfix _⟩ <;>
      exact fun h => absurd (ι.symm.injective (Subtype.ext h)) (by decide)
  have hev : (swap p q * swap s t : Perm (Fin m)) ∈ alternatingGroup (Fin m) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hpq, Perm.sign_swap hst]
    rfl
  obtain ⟨u', hu'def⟩ : ∃ u' : alternatingGroup (Fin m),
      (u' : Perm (Fin m)) = swap p q * swap s t := ⟨⟨swap p q * swap s t, hev⟩, rfl⟩
  have hu' : u' ∈ fixAlt τ := by
    rw [mem_fixAlt]
    intro ω hω
    rw [Finset.mem_compl, Perm.mem_support, not_not]
    by_contra hωτ
    have hωp : ω ≠ p := fun h => hωτ (by rw [h]; exact hp)
    have hωq : ω ≠ q := fun h => hωτ (by rw [h]; exact hq)
    have hωs : ω ≠ s := fun h => hωτ (by rw [h]; exact hs)
    have hωt : ω ≠ t := fun h => hωτ (by rw [h]; exact ht)
    refine (Perm.mem_support.mp hω) ?_
    rw [hu'def, Perm.mul_apply, swap_apply_of_ne_of_ne hωs hωt, swap_apply_of_ne_of_ne hωp hωq]
  have hmod' : m % 2 = (Finset.univ.filter fun x => τ x = x).card % 2 := hmod
  refine ⟨m / 2, by omega, by omega, e.symm u', ?_, p, q, s, t, hpq, hps, hpt, hqs, hqt, hst, ?_⟩
  · have h1 : u' ∈ P.map e.toMonoidHom := by
      rw [hPeq]
      exact hu'
    exact Subgroup.mem_map_equiv.mp h1
  · rw [MulEquiv.apply_symm_apply]
    exact hu'def

end CFSG.OddStandard.SmallF3.HypA2Leaves
