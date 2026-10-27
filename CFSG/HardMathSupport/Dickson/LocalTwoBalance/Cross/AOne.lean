module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Split
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearFamily
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinTwoField

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG CFSG.GorensteinWalter CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.GH74.GLS.IVK

section Model

variable {F : Type} [Field F] [Finite F]

theorem four_le_card_fixedField_odd {p : ℕ} (hp : p.Prime) (hp35 : p = 3 ∨ p = 5)
    (hF8 : p = 3 → Nat.card F ≠ 8) {σ : F ≃+* F}
    (hσ : orderOf σ = p) (hpF : ¬ p ∣ Nat.card (fixedField σ)) (k : PSL2 F)
    (hk : psl2FieldAut F σ k = k) (hko : orderOf k = p) : 4 ≤ Nat.card (fixedField σ) := by
  have hp2 : p ≠ 2 := by omega
  have hodd : Odd (orderOf σ) := by rw [hσ]; exact hp.odd_of_ne_two hp2
  have hkJ : k ∈ (pslIncl σ).range := (mem_range_pslIncl_iff σ hodd k).2 hk
  have hdvdJ : p ∣ Nat.card (pslIncl σ).range := by
    have : orderOf (⟨k, hkJ⟩ : (pslIncl σ).range) = p := by
      rw [Subgroup.orderOf_mk]; exact hko
    rw [← this]; exact orderOf_dvd_natCard _
  have hcardJ : Nat.card (pslIncl σ).range = Nat.card (PSL2 (fixedField σ)) :=
    (Nat.card_congr (MonoidHom.ofInjective (pslIncl_injective σ)).toEquiv).symm
  have hdvdSL : Nat.card (PSL2 (fixedField σ)) ∣
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)) := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)))
    exact Dvd.intro _ this.symm
  have hdiv : p ∣ Nat.card (fixedField σ) * (Nat.card (fixedField σ) ^ 2 - 1) := by
    rw [← sl2_card_formula (fixedField σ)]
    rw [hcardJ] at hdvdJ
    exact hdvdJ.trans hdvdSL
  have hF := fixedField_card_pow σ
  rw [hσ] at hF
  by_contra hlt
  push Not at hlt
  have h2 : 2 ≤ Nat.card (fixedField σ) := Finite.one_lt_card
  generalize Nat.card (fixedField σ) = q₀ at hdiv hlt h2 hpF hF
  interval_cases q₀
  · rcases hp35 with rfl | rfl
    · exact hF8 rfl (hF.symm.trans (by norm_num))
    · norm_num at hdiv
  · rcases hp35 with rfl | rfl
    · exact hpF (by norm_num)
    · norm_num at hdiv

theorem fieldCoreAt_of_outer_odd {p : ℕ} (hp : p.Prime) (hp35 : p = 3 ∨ p = 5)
    (hF8 : p = 3 → Nat.card F ≠ 8) (hpF : ¬ p ∣ Nat.card F)
    (hinj : Function.Injective (MulAut.conj : PSL2 F →* MulAut (PSL2 F)))
    {D : Subgroup (MulAut (PSL2 F))} (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 2)
    (hDin : ¬ D ≤ innerAut (PSL2 F)) :
    ∃ x ∈ D, x ∉ innerAut (PSL2 F) ∧ FieldCoreAt p x := by
  classical
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hDfin : Finite D :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  let Ψ : PGammaL2 F ≃* MulAut (PSL2 F) := semilinearEquivAut F
  have : IsCyclic (F ≃+* F) := fieldAut_isCyclic F
  let α : D →* (F ≃+* F) :=
    ((SemidirectProduct.rightHom : PGammaL2 F →* (F ≃+* F)).comp Ψ.symm.toMonoidHom).comp
      D.subtype
  have hle := card_le_mul_card_ker' hp (fun h : D => Subtype.ext (hD.2 h h.2)) α
  obtain ⟨y, hyker, hy1⟩ : ∃ y ∈ α.ker, y ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : α.ker = ⊥ := eq_bot_iff.2 fun z hz => (Subgroup.mem_bot).2 (hno z hz)
    rw [hbot, Subgroup.card_bot, hcard] at hle
    have : p ^ 2 = p * p := by ring
    have := hp.two_le
    nlinarith
  have hyp : (y : MulAut (PSL2 F)) ^ p = 1 := hD.2 y y.2
  have hy1' : (y : MulAut (PSL2 F)) ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hyin : (y : MulAut (PSL2 F)) ∈ innerAut (PSL2 F) :=
    mem_innerAut_of_right_eq_one hp hp2 hyp (MonoidHom.mem_ker.1 hyker)
  obtain ⟨x, hxD, hxin⟩ := IsConcreteLE.not_le_iff_exists.1 hDin
  obtain ⟨σ, h, hσ, hxh⟩ := exists_outer_data hp hp2 (hD.2 x hxD) hxin
  have hcomm : (y : MulAut (PSL2 F)) * x = x * y :=
    congrArg Subtype.val (hD.1.is_comm.comm y ⟨x, hxD⟩)
  have hodd : Odd (orderOf σ) := by rw [hσ]; exact hp.odd_of_ne_two hp2
  have hδp : orderOf (psl2FieldAut F σ) = p := by rw [orderOf_psl2FieldAut, hσ]
  have hpF0 : ¬ p ∣ Nat.card (fixedField σ) := fun hd =>
    hpF (by
      rw [← fixedField_card_pow σ, hσ]
      exact dvd_pow hd hp.ne_zero)
  obtain ⟨k, hkδ, hkord⟩ := exists_fixed_orderOf_of_canonical_conj hp hinj hxh hyin hy1' hyp hcomm
  have h4 := four_le_card_fixedField_odd hp hp35 hF8 hσ hpF0 k hkδ hkord
  have : Fintype (fixedField σ) := Fintype.ofFinite _
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (fixedField σ))) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
  have hsimple := CFSG.LinearGroups.linear_projective_simple (n := 2) (K := fixedField σ)
    (by norm_num) (Or.inr ⟨s, hs⟩)
  have hperf := (CFSG.LinearGroups.linear_projective_perfect (n := 2) (K := fixedField σ)
    (by norm_num) (Or.inr ⟨s, hs⟩)).commutator_eq_top
  have := hsimple.1
  have := hsimple.2.1
  let eJ : PSL2 (fixedField σ) ≃* (pslIncl σ).range :=
    MonoidHom.ofInjective (pslIncl_injective σ)
  have : IsSimpleGroup ((pslIncl σ).range) := eJ.symm.isSimpleGroup
  have hJq : CFSG.IsQuasisimple ((pslIncl σ).range) := by
    refine isQuasisimple_of_simple_nonabelian ?_
    intro hc
    refine not_comm_of_commutator_eq_top hperf fun a b => ?_
    apply eJ.injective
    have := hc (eJ a) (eJ b)
    simpa [map_mul] using this
  refine ⟨x, hxD, hxin, ?_⟩
  exact fieldCoreAt_of_canonical_conj hp hinj hδp hJq
    (fun g => mem_range_pslIncl_iff σ hodd g)
    (fun β hβ => mem_zpowers_of_fixes_range σ hodd β hβ) hxh hyin hy1' hyp hcomm

theorem innerPlaneBalance_psl_two_odd {p : ℕ} (hp : p.Prime) (hp35 : p = 3 ∨ p = 5)
    (hF4 : 4 ≤ Nat.card F) (hpF : ¬ p ∣ Nat.card F)
    (hinj : Function.Injective (MulAut.conj : PSL2 F →* MulAut (PSL2 F))) :
    InnerPlaneBalance p (PSL2 F) := by
  intro E hEin hE hEc H hH
  have hE₁ : (E.comap (MulAut.conj : PSL2 F →* MulAut (PSL2 F))).map
      (MulAut.conj : PSL2 F →* MulAut (PSL2 F)) = E :=
    Subgroup.map_comap_eq_self hEin
  have hE₁el := isElemAbelian_comap _ hinj hE
  have hE₁c : Nat.card (E.comap (MulAut.conj : PSL2 F →* MulAut (PSL2 F))) = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hE₁, hEc]
  rw [← hE₁]
  have hp4 : 3 < p ∨ 4 ≤ Nat.card F := by omega
  by_cases hs : p ∣ Nat.card F - 1
  · exact localDeltaIn_eq_bot_psl_split (n := 2) hp (by omega) hs
      (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega) (by norm_num) hinj _ hE₁el hE₁c hH
  · exact localDeltaIn_eq_bot_psl_nonsplit (n := 2) hp hp4 hpF hs (by norm_num)
      hinj _ hE₁el hE₁c hH

theorem isLocallyBalancedAbs_two_psl_two_odd {p : ℕ} (hp : p.Prime) (hp35 : p = 3 ∨ p = 5)
    (hF8 : p = 3 → Nat.card F ≠ 8) (hF4 : 4 ≤ Nat.card F) (hpF : ¬ p ∣ Nat.card F) :
    IsLocallyBalancedAbs p 2 (PSL2 F) := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hF4)
  have hsimple := CFSG.LinearGroups.linear_projective_simple (n := 2) (K := F) (by norm_num)
    (Or.inr ⟨s, hs⟩)
  have hperf := (CFSG.LinearGroups.linear_projective_perfect (n := 2) (K := F) (by norm_num)
    (Or.inr ⟨s, hs⟩)).commutator_eq_top
  have := hsimple.2.1
  have hinj := CFSG.LieType.SeitzGeneration.conj_injective_of_simple_perfect hperf
  have : Finite (PSL2 F) := hsimple.2.2 inferInstance
  exact isLocallyBalancedAbs_two_of_planes_and_fields hp hinj
    (innerPlaneBalance_psl_two_odd hp hp35 hF4 hpF hinj)
    (fun D hD hc hDin => fieldCoreAt_of_outer_odd hp hp35 hF8 hpF hinj hD hc hDin)

end Model

@[expose] def regimeAOne (p : ℕ) (idx : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, idx.1 = .A 1 q ∧ (p = 3 → q.card ≠ 8)

theorem localTwoCrossFamAt_A_one (p : ℕ) (hp : p = 3 ∨ p = 5) :
    LocalTwoCrossFamAt p .A (regimeAOne p) := by
  rintro ⟨d, hv⟩ _ ⟨q, hd, hq8⟩ hc _
  change d = _ at hd
  subst hd
  have hp' : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have h4 : 4 ≤ q.card := hrange.2 (by omega)
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hpF : ¬ p ∣ Nat.card (GaloisField q.p q.exponent) := by
    rw [hcardF, TauCeti.PrimePower.card_def]
    intro hdvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp' q.prime_p).mp (hp'.dvd_of_dvd_pow hdvd))
  let e := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_two_psl_two_odd (F := GaloisField q.p q.exponent) hp' hp
      (fun h => by rw [hcardF]; exact hq8 h) (by rw [hcardF]; exact h4) hpF)

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
