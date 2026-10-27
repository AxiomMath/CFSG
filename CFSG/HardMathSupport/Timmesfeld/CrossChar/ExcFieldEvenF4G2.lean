module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldOrders
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldEntrywise
public import CFSG.LieType.SeitzGeneration.ExcPlaneG2
public import CFSG.RankThree.Chevalley.SteinbergCFOddInnerFieldLocalCore
public import CFSG.RankThree.Chevalley.SteinbergBTEvenF4Noninner
public import CFSG.RankThree.Chevalley.SteinbergBMG2NoninnerLocalCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge CFSG.RankThree.Chevalley
  CFSG.LieType.Ree CFSG.RankThree.Chevalley.SteinbergBT
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)

section EvenF4


theorem fieldCoreAt_F4_even {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : ∀ σ : K ≃+* K, orderOf σ = p →
      ¬ Nat.Coprime p (Nat.card (adjointGroup ReeTag.F4.tag (fixSubfield σ))))
    {x : MulAut (adjointGroup ReeTag.F4.tag K)} (hxp : orderOf x = p)
    (hxo : x ∉ (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
      MulAut (adjointGroup ReeTag.F4.tag K)).range) :
    FieldCoreAt p x := by
  classical
  obtain ⟨-, hNF, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨y, k⟩, hyk, -⟩ := hNF x
  have hαp : orderOf (⟨x, Subgroup.mem_top x⟩ :
      (⊤ : Subgroup (MulAut (adjointGroup ReeTag.F4.tag K)))) = p := by
    rw [Subgroup.orderOf_mk]
    exact hxp
  obtain ⟨-, -, ⟨σ, hσ⟩, hmain, -⟩ :=
    even_F4_noninner_odd_prime_field_descent_and_local_core_trivial hf hK hp hp2 ⊤ le_top
      ⟨x, Subgroup.mem_top x⟩ hxo hαp y k k.isLt hyk
  obtain ⟨hσp, ψ, hψ⟩ := hmain σ hσ
  obtain ⟨-, hJC, hsimple, hnc, -, -, -, hNδ, hnormal, hcent, -⟩ :=
    even_F4_canonical_field_centralizer_all_orders hf hK σ
  exact fieldCoreAt_of_conj (fieldCoreAt_entrywise_of_data hσp hJC hsimple hnc hNδ hnormal hcent
    (hdvd σ hσp)) ψ hψ

theorem isLocallyBalancedAbs_adjointF4_fieldEven {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K)
    (hcnt : degCount Tag.F4 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 2) :
    IsLocallyBalancedAbs p 3 (adjointGroup Tag.F4 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K ReeTag.F4.prime := by
    rw [show ReeTag.F4.prime = 2 from rfl]
    exact finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hnd : ¬ p ∣ Nat.card K ^ 2 - 1 := by
    intro h
    have h2 := orderOf_dvd_two_of_dvd_sq_sub_one hpK h
    rcases degCount_F4_eq_two hcnt with h3 | h3 | h3 <;> rw [h3] at h2 <;> omega
  refine isLocallyBalancedAbs_adjoint_of_fieldCore K hp
    (rankLE2_adjointGroup_F4 K hp hp2 hpK hnd) fun x hxp hxo => ?_
  refine fieldCoreAt_F4_even hf K hK hp hp2
    (fun σ hσp => not_coprime_card_adjointF4 (fixSubfield σ) hp ?_) hxp hxo
  rw [card_fixSubfield_cast Nat.prime_two hf hK hp hσp]
  exact hcnt

end EvenF4

section EvenG2


theorem fieldCoreAt_G2_even {f : ℕ} (hf : 2 ≤ f) (K : Type) [Field K] (hK : Nat.card K = 2 ^ f)
    {p : ℕ} (hp : p.Prime)
    (hk3 : ∀ σ : K ≃+* K, orderOf σ = p → 3 ≤ Nat.card (fixSubfield σ))
    (hdvd : ∀ σ : K ≃+* K, orderOf σ = p →
      ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.G2 (fixSubfield σ))))
    {x : MulAut (adjointGroup Tag.G2 K)} (hxp : orderOf x = p)
    (hxo : x ∉ (MulAut.conj : adjointGroup Tag.G2 K →* MulAut (adjointGroup Tag.G2 K)).range) :
    FieldCoreAt p x := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hNF := conj_normalForm_of_pointwise
    (CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form hf K
      hK).1
  obtain ⟨⟨y, σ⟩, hyσ, -⟩ := hNF x
  have hαp : orderOf (⟨x, Subgroup.mem_top x⟩ :
      (⊤ : Subgroup (MulAut (adjointGroup Tag.G2 K)))) = p := by
    rw [Subgroup.orderOf_mk]
    exact hxp
  obtain ⟨hσp, -, ⟨h, hh⟩, -⟩ := even_G2_noninner_prime_local_core_trivial hf hK hp ⊤ le_top
    ⟨x, Subgroup.mem_top x⟩ hxo hαp y σ hyσ
  obtain ⟨-, -, hJC, -, -, -, -, hNδ, hnormal, -, hcent, -, -⟩ :=
    even_G2_canonical_field_centralizer_all_orders hf hK σ
  have hq : CFSG.IsQuasisimple (fixedFieldImage Tag.G2 σ) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (fixedFieldImageEquiv σ)
      (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card (fixSubfield σ)
        (hk3 σ hσp))
  exact fieldCoreAt_of_conj (fieldCoreAt_entrywise_of_quasisimple hσp hJC hq hNδ hnormal hcent
    (hdvd σ hσp)) (MulAut.conj h) hh

theorem three_le_of_dvd_sq_sub_one {p a : ℕ} (hp5 : 5 ≤ p) (ha : 2 ≤ a) (hd : p ∣ a ^ 2 - 1) :
    3 ≤ a := by
  by_contra h
  have h2 : a = 2 := by omega
  subst h2
  have := Nat.le_of_dvd (by norm_num) hd
  omega

theorem isLocallyBalancedAbs_adjointG2_fieldEven {f : ℕ} (hf : 2 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (hd : p ∣ Nat.card K ^ 2 - 1) : IsLocallyBalancedAbs p 3 (adjointGroup Tag.G2 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hK1 : 1 ≤ Nat.card K := Nat.card_pos
  refine isLocallyBalancedAbs_adjoint_of_fieldCore K hp
    (rankLE2_adjointGroup_G2 K hp hp5 hpK) fun x hxp hxo => ?_
  have hdf : ∀ σ : K ≃+* K, orderOf σ = p → p ∣ Nat.card (fixSubfield σ) ^ 2 - 1 := fun σ hσp =>
    dvd_sq_sub_one_of_cast_eq hK1 Nat.card_pos
      (card_fixSubfield_cast Nat.prime_two (by omega) hK hp hσp).symm hd
  exact fieldCoreAt_G2_even hf K hK hp
    (fun σ hσp => three_le_of_dvd_sq_sub_one hp5 Finite.one_lt_card (hdf σ hσp))
    (fun σ hσp => not_coprime_card_adjointG2 (fixSubfield σ) hp (hdf σ hσp)) hxp hxo

end EvenG2

section FamilyEvenF4G2


@[expose] def regimeG2FieldEven (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ q : TauCeti.PrimePower, idx.1 = .G2 q ∧ 5 ≤ p ∧ p ∣ q.card ^ 2 - 1 ∧ p ∣ q.exponent ∧
    q.p = 2

theorem crossCharFamAt_F4_fieldEven :
    CrossCharFamAt .F4 (regimeExcFieldEven TauCeti.LieTypeIndex.F4 (degCount Tag.F4)) := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hcnt, hpf, hq2⟩
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  obtain ⟨K, _, _, hK, _, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at hcnt
  have hK2 : Nat.card K = 2 ^ q.exponent := by
    rw [hK, TauCeti.PrimePower.card_def, hq2]
  exact IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_adjointF4_fieldEven
    q.exponent_pos K hK2 hp hp2 hpK hcnt)

theorem crossCharFamAt_G2_fieldEven : CrossCharFamAt .G2 regimeG2FieldEven := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hp5, hdq, hpf, hq2⟩
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  obtain ⟨K, _, _, hK, _, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at hdq
  have hK2 : Nat.card K = 2 ^ q.exponent := by
    rw [hK, TauCeti.PrimePower.card_def, hq2]
  have hf2 : 2 ≤ q.exponent := by
    have := Nat.le_of_dvd q.exponent_pos hpf
    omega
  exact IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_adjointG2_fieldEven hf2 K hK2
    hp hp5 hpK hdq)

end FamilyEvenF4G2

end CFSG.HardMathSupport.Timmesfeld.CrossChar
