module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpNotLie
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEven
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedHe
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixA
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixB

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem eq_of_factorial_div_two_eq {m k : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k)
    (h : m.factorial / 2 = k.factorial / 2) : m = k := by
  obtain ⟨a, ha⟩ : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) hm
  obtain ⟨b, hb⟩ : 2 ∣ k.factorial := Nat.dvd_factorial (by norm_num) hk
  have hab : m.factorial = k.factorial := by
    rw [ha, hb] at h ⊢
    omega
  exact (Nat.factorial_inj (by omega)).mp hab

theorem le_factorial_div_two {m : ℕ} (hm : 7 ≤ m) : 2520 ≤ m.factorial / 2 := by
  have h := Nat.factorial_le hm
  have h7 : (7 : ℕ).factorial = 5040 := by decide
  omega

theorem alt_outcome_of_alternating {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 5 ≤ n)
    (θ : S ≃* alternatingGroup (Fin n)) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) {m : ℕ} (hm7 : 7 ≤ m)
    (eP : P ⧸ Open.fusionZStar P ≃* alternatingGroup (Fin m)) : m ≤ n ∧ n % 2 = m % 2 := by
  classical
  have hmc := le_factorial_div_two hm7
  by_cases hn6 : n = 6
  · exfalso
    subst hn6
    have h1 := card_dvd_of_fusionZStar_equiv eP.toEquiv
    rw [card_of_mulEquiv_alt (by omega) (MulEquiv.refl _), card_of_mulEquiv_alt (by omega) θ] at h1
    have h2 := Nat.le_of_dvd (by decide) h1
    have h6 : (6 : ℕ).factorial / 2 = 360 := by decide
    omega
  obtain ⟨h', ⟨e⟩⟩ := h.map θ
  obtain ⟨τ, hτ2, -, hdeg, ⟨eA⟩⟩ := exists_involution_of_properFixedComponent_alternating hn hn6 h'
  set Ω := Finset.univ.filter fun x => τ x = x with hΩ
  have eMA : alternatingGroup ↥Ω ≃* alternatingGroup (Fin m) := eA.symm.trans (e.symm.trans eP)
  have hcard : m = Ω.card := by
    have h1 := card_of_mulEquiv_alt (by omega) eMA
    have : Nontrivial ↥Ω := by
      rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_coe]
      omega
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_coe] at h1
    exact (eq_of_factorial_div_two_eq (by omega) (by omega) h1).symm
  have hsupp : τ.support = Finset.univ.filter fun x => ¬ τ x = x := rfl
  have hsum : Ω.card + τ.support.card = n := by
    rw [hsupp, hΩ, Finset.card_filter_add_card_filter_not, Finset.card_univ,
      Fintype.card_fin]
  obtain ⟨k, hk⟩ := Equiv.Perm.cycleType_prime_order (σ := τ) (by rw [hτ2]; exact Nat.prime_two)
  have heven : τ.support.card = 2 * (k + 1) := by
    rw [← Equiv.Perm.sum_cycleType, hk, hτ2, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  omega

theorem false_of_oddLie_alt
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput) {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) (hodd : OddLieType S)
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P) {m : ℕ} (hm : Odd m)
    (hm7 : 7 ≤ m) (eP : P ⧸ Open.fusionZStar P ≃* alternatingGroup (Fin m)) : False := by
  have hσ1 := h.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  set L := P.subgroupOf (fixedSubgroup σ) with hLdef
  have hq : IsQuasisimple L :=
    fixedTwoComponentsQuasisimple_of_oddLieType hna hodd σ hσσ hσ1 L h.2.2.1
  obtain ⟨hcomp, ⟨eZ⟩⟩ := h.fusionZStar_equiv_of_quasisimple hq
  obtain ⟨τ, n, p, f, hp, hp2, hadm, hm'⟩ := hodd
  rcases hGLS S τ n p f hp hp2 hadm hm' σ hσ2 L hcomp with ⟨τ', n', f', hadm', hm''⟩ |
      ⟨-, -, -, h8⟩
  · exact not_lieModel_of_mulEquiv_alt hGLS hO hm hm7 (eZ.symm.trans eP) hadm' hm''
  · have h504 := card_of_lieModel_psl_two_eight hO h8
    have hle : Nat.card (L ⧸ center L) ≤ 504 := by
      rw [← h504]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    rw [card_of_mulEquiv_alt (by omega) (eZ.symm.trans eP)] at hle
    have := le_factorial_div_two hm7
    omega

theorem uList_of_evenLie_alt
    (hEO : EvenLieOuterTwoComponentsInput) (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (heven : EvenLieType S) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) {m : ℕ} (hm : Odd m) (hm7 : 7 ≤ m)
    (eP : P ⧸ Open.fusionZStar P ≃* alternatingGroup (Fin m)) :
    OddLieType S ∨ (∃ n : ℕ, Odd n ∧ 7 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∨
      Nonempty (S ≃* NativeSporadic.He) := by
  have hσ1 := h.ne_one
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by
    rw [sq]; exact MulEquiv.ext fun y => h.1 y) hσ1
  have hmc := le_factorial_div_two hm7
  have hPcard := card_of_mulEquiv_alt (by omega) eP
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout
  ·
    obtain ⟨ht2, hPt, hPc, -⟩ := h.inner hna ht
    rcases oddCore_eq_bot_or_uList_of_evenLieType hna heven ht2 with hcore | hU
    · exfalso
      have hq := Sporadic.HeldB.pComponent_quasisimple_of_oddCore_eq_bot hcore _ hPc
      exact involutionCentralizersComponentFree_of_evenLieType heven t ht2 _
        ⟨hq, hPc.choose_spec.2.1⟩
    rcases hU with ho | hA | hL | hH
    · exact .inl ho
    · exact .inr (.inl hA)
    · exfalso
      obtain ⟨-, h64, -⟩ :=
        PSL3Four.excludes_alternating_models_stated.{0} S (statedClassicalModel_of_lieModel_psl hL)
      have h1 : Nat.card (P ⧸ Open.fusionZStar P) ∣ Nat.card (centralizer ({t} : Set S)) :=
        (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hPt)
      rw [h64 t ht2, hPcard] at h1
      have h2 := Nat.le_of_dvd (by norm_num) h1
      omega
    · exact .inr (.inr hH)
  ·
    exfalso
    obtain ⟨τ, n, f, hadm, hm'⟩ := heven
    obtain ⟨eL⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe h.2.1)
    rcases hEO S τ n f hadm hm' σ hσ2 hout _ h.2.2.1 with ⟨τ', n', f', hadm', hm''⟩ | ⟨⟨eA⟩⟩ |
        hU
    · exact not_lieModel_of_mulEquiv_alt hGLS hO hm hm7 (eL.trans eP) hadm' hm''
    · have h1 := card_of_mulEquiv_alt (by omega) (eA.symm.trans (eL.trans eP))
      have h6 : (6 : ℕ).factorial / 2 = 360 := by decide
      have h2 := card_of_mulEquiv_alt (by omega) (MulEquiv.refl (alternatingGroup (Fin 6)))
      omega
    · have hadm3 : StatedLieAdmissible .PSU 3 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
      exact not_lieModel_of_mulEquiv_alt hGLS hO hm hm7 (eL.trans eP) hadm3 hU

theorem eq_seven_of_held
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (eS : S ≃* NativeSporadic.He) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) {m : ℕ} (hm : Odd m) (hm7 : 7 ≤ m)
    (eP : P ⧸ Open.fusionZStar P ≃* alternatingGroup (Fin m)) : m = 7 := by
  have hPcard := card_of_mulEquiv_alt (by omega) eP
  rcases GrSLit.simpleFixedComponents_held GrSLit.HeldFix.isL34Type_of_isPComponent_centralizer_heA0
      GrSLit.HeldFix.not_isPComponent_centralizer_heT1P S
      inferInstance hna ⟨eS⟩ σ h.1 P h.2.1 h.2.2.1 h.2.2.2 with hL | ⟨⟨eA⟩⟩
  · exfalso
    have h1 := card_of_isL34Type hL
    rw [hPcard] at h1
    have h8 : m = 8 := eq_of_factorial_div_two_eq (by omega) (by norm_num)
      (h1.trans (by decide))
    obtain ⟨r, rfl⟩ := hm
    omega
  · have h1 := card_of_mulEquiv_alt (by norm_num) eA
    rw [hPcard] at h1
    exact eq_of_factorial_div_two_eq (by omega) (by norm_num) h1

end CFSG.ComponentClassification.SolMax
