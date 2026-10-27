module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldOrders
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldEntrywise
public import CFSG.RankThree.Chevalley.SteinbergCFOddInnerFieldLocalCore
public import CFSG.RankThree.Chevalley.SteinbergBTEvenE7E8Noninner
public import CFSG.RankThree.Chevalley.SteinbergBTEvenE6Noninner
public import CFSG.RankThree.PartOne.S11c.Sec66Exc

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.Sec66T
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)

section EvenE78


theorem fieldCoreAt_E78_even (τ : Tag) (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime)
    (hdvd : ∀ σ : K ≃+* K, orderOf σ = p →
      ¬ Nat.Coprime p (Nat.card (adjointGroup τ (fixSubfield σ))))
    {x : MulAut (adjointGroup τ K)} (hxp : orderOf x = p)
    (hxo : x ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range) :
    FieldCoreAt p x := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hNF := conj_normalForm_of_pointwise
    (even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ).1
  obtain ⟨⟨y, σ⟩, hyσ, -⟩ := hNF x
  have hαp : orderOf (⟨x, Subgroup.mem_top x⟩ :
      (⊤ : Subgroup (MulAut (adjointGroup τ K)))) = p := by
    rw [Subgroup.orderOf_mk]
    exact hxp
  obtain ⟨hσp, -, ⟨ψ, hψ⟩, -⟩ := even_E7_E8_noninner_prime_field_descent_and_local_core_trivial τ hτ
    hf K hK hp ⊤ le_top ⟨x, Subgroup.mem_top x⟩ hxo hαp y σ hyσ
  obtain ⟨-, hJC, hsimple, hnc, -, -, -, hNδ, hnormal, hcent, -⟩ :=
    even_E7_E8_canonical_field_centralizer_all_orders τ hτ hf K hK σ
  exact fieldCoreAt_of_conj (fieldCoreAt_entrywise_of_data hσp hJC hsimple hnc hNδ hnormal hcent
    (hdvd σ hσp)) ψ hψ

theorem isLocallyBalancedAbs_adjointE8_fieldEven {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime)
    (hcnt : degCount Tag.E8 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 2) :
    IsLocallyBalancedAbs p 3 (adjointGroup Tag.E8 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  refine isLocallyBalancedAbs_adjoint_of_fieldCore K hp
    (rankLE2_E8_of_degCount_eq_two K hp hcnt) fun x hxp hxo => ?_
  refine fieldCoreAt_E78_even Tag.E8 (Or.inr rfl) hf K hK hp
    (fun σ hσp => not_coprime_card_adjointE8 (fixSubfield σ) hp ?_) hxp hxo
  rw [card_fixSubfield_cast Nat.prime_two hf hK hp hσp]
  exact hcnt

theorem isLocallyBalancedAbs_adjointE7_fieldEven {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime)
    (hcnt : degCount Tag.E7 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 2) :
    IsLocallyBalancedAbs p 3 (adjointGroup Tag.E7 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  refine isLocallyBalancedAbs_adjoint_of_fieldCore K hp
    (rankLE2_E7_of_degCount_eq_two K hp hcnt) fun x hxp hxo => ?_
  refine fieldCoreAt_E78_even Tag.E7 (Or.inl rfl) hf K hK hp
    (fun σ hσp => not_coprime_card_adjointE7 (fixSubfield σ) hp ?_) hxp hxo
  rw [card_fixSubfield_cast Nat.prime_two hf hK hp hσp]
  exact hcnt

end EvenE78

section EvenE6


theorem fieldCoreAt_E6_even {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hdvd : ∀ σ : K ≃+* K, orderOf σ = p →
      ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.E6 (fixSubfield σ))))
    {x : MulAut (adjointGroup Tag.E6 K)} (hxp : orderOf x = p)
    (hxo : x ∉ (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)).range) :
    FieldCoreAt p x := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨Θ, -, hΘ, -⟩ := ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  have hαp : orderOf (⟨x, Subgroup.mem_top x⟩ :
      (⊤ : Subgroup (MulAut (adjointGroup Tag.E6 K)))) = p := by
    rw [Subgroup.orderOf_mk]
    exact hxp
  obtain ⟨⟨σ, -, hσp, ψ, hψ⟩, ⟨f', hff'⟩, -⟩ :=
    even_E6_noninner_large_prime_field_descent_and_local_core_trivial hf K hK Θ hΘ hp hp3 ⊤ le_top
      ⟨x, Subgroup.mem_top x⟩ hxo hαp
  have hf'1 : 1 ≤ f' := by
    rcases Nat.eq_zero_or_pos f' with h0 | h0
    · rw [h0, mul_zero] at hff'
      omega
    · exact h0
  obtain ⟨σ₀, hσ₀, hzp⟩ := exists_canonical_generator hf hK hσp hp.pos hff'
  have hσ₀ord : orderOf σ₀ = p := by
    rw [← Nat.card_zpowers, ← hzp, Nat.card_zpowers, hσp]
  have hK' : Nat.card K = 2 ^ (f' * p) := by rw [hK, hff', mul_comm]
  obtain ⟨-, -, -, hJC, hsimple, hnc, -, hNδ, hnormal, hcent, -⟩ :=
    even_E6_canonical_field_derived_subgroup_and_pointwise_centralizer hf'1 hp.two_le K hK' σ₀ hσ₀
  have hcore := fieldCoreAt_entrywise_of_data hσ₀ord hJC hsimple hnc hNδ hnormal hcent
    (hdvd σ₀ hσ₀ord)
  have hz : Subgroup.zpowers (entrywiseAdjointAut Tag.E6 σ) =
      Subgroup.zpowers (entrywiseAdjointAut Tag.E6 σ₀) := by
    have h1 := MonoidHom.map_zpowers (entrywiseAdjointAutHom (τ := Tag.E6) (K := K)) σ
    have h2 := MonoidHom.map_zpowers (entrywiseAdjointAutHom (τ := Tag.E6) (K := K)) σ₀
    rw [hzp] at h1
    exact h1.symm.trans h2
  exact fieldCoreAt_of_conj (FieldCoreAt.of_zpowers_eq hz.symm hcore) ψ hψ

theorem isLocallyBalancedAbs_adjointE6_fieldEven {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hcnt : degCount Tag.E6 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 2) :
    IsLocallyBalancedAbs p 3 (adjointGroup Tag.E6 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  refine isLocallyBalancedAbs_adjoint_of_fieldCore K hp
    (rankLE2_E6_of_degCount_eq_two K hp hcnt) fun x hxp hxo => ?_
  refine fieldCoreAt_E6_even hf K hK hp hp3
    (fun σ hσp => not_coprime_card_adjointE6 (fixSubfield σ) hp ?_) hxp hxo
  rw [card_fixSubfield_cast Nat.prime_two hf hK hp hσp]
  exact hcnt

end EvenE6

section FamilyEven


theorem crossCharFamAt_E8_fieldEven :
    CrossCharFamAt .E8 (regimeExcFieldEven TauCeti.LieTypeIndex.E8 (degCount Tag.E8)) := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hcnt, hpf, hq2⟩
  change d = _ at hd
  subst hd
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  rw [← hK] at hcnt
  have hK2 : Nat.card K = 2 ^ q.exponent := by
    rw [hK, TauCeti.PrimePower.card_def, hq2]
  exact IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_adjointE8_fieldEven
    q.exponent_pos K hK2 hp hcnt)

theorem crossCharFamAt_E7_fieldEven :
    CrossCharFamAt .E7 (regimeExcFieldEven TauCeti.LieTypeIndex.E7 (degCount Tag.E7)) := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hcnt, hpf, hq2⟩
  change d = _ at hd
  subst hd
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  rw [← hK] at hcnt
  have hK2 : Nat.card K = 2 ^ q.exponent := by
    rw [hK, TauCeti.PrimePower.card_def, hq2]
  exact IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_adjointE7_fieldEven
    q.exponent_pos K hK2 hp hcnt)

theorem crossCharFamAt_E6_fieldEven :
    CrossCharFamAt .E6 (regimeExcFieldEven TauCeti.LieTypeIndex.E6 (degCount Tag.E6)) := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hcnt, hpf, hq2⟩
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hp5 := five_le_of_count_le (k := 2) (by decide) hp hp2 (not_dvd_card_of_ne hp hpq) hcnt.le
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  rw [← hK] at hcnt
  have hK2 : Nat.card K = 2 ^ q.exponent := by
    rw [hK, TauCeti.PrimePower.card_def, hq2]
  exact IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_adjointE6_fieldEven
    q.exponent_pos K hK2 hp (by omega) hcnt)

end FamilyEven

end CFSG.HardMathSupport.Timmesfeld.CrossChar
