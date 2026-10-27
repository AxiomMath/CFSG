module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.FixPlaneStd
public import CFSG.LieType.SeitzGeneration.InnerSymplectic
public import CFSG.RankThree.PartOne.CTP.SeitzMaxSp

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

open Matrix CFSG.Open CFSG.LieType.SeitzGeneration CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.RankThree.PartOne.KCSpComm CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.RankThree.PartOne.CTP
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

theorem fixPlaneGen_projectiveSp_of_inner {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K]
    {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hp2 : p ≠ 2)
    (hinner : ∀ σ : K ≃+* K, orderOf σ = p →
      ∀ E₁ : Subgroup (StatedProj (StatedSp r (descentField σ))), IsElemAbelian p E₁ →
        Nat.card E₁ = p ^ 2 →
        Subgroup.closure {k | ∃ x ∈ E₁, x ≠ 1 ∧ k * x = x * k} = ⊤) :
    FixPlaneGen (StatedProj (StatedSp r K)) p := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero r := ⟨by omega⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have O : SpOuter ℓ f r K := spOuter hℓ hf hr hK
  have hdesc : ∀ α : MulAut (StatedProj (StatedSp r K)), IsOuterOfOrder p α →
      ∃ d ∈ spLinearAutGroup r K, ∃ g ∈ {g | ∃ σ : K ≃+* K, orderOf σ = p ∧ g = fieldAut r K σ},
        α = d * g * d⁻¹ := by
    intro α hα
    obtain ⟨hord, hout⟩ := hα
    have hαp : α ^ p = 1 := hord ▸ pow_orderOf_eq_one α
    have hαE : α ∈ spSemilinearAutGroup r K :=
      mem_of_odd_orderOf_of_index_dvd_two _ O.index_dvd (hord ▸ hpodd)
    have hαD : α ∉ spLinearAutGroup r K := fun hD => by
      obtain ⟨g, hg⟩ := mem_of_pow_eq_one_of_relIndex_dvd_two
        (O.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)) hp hp2 hD hαp
      exact hout g hg.symm
    obtain ⟨-, σ, hσord, h, hhD, hαh⟩ := O.descent p hp α hαE hαD hord
    exact ⟨h, hhD, fieldAut r K σ, ⟨σ, hσord, rfl⟩, hαh⟩
  by_cases hex : ∃ σ0 : K ≃+* K, orderOf σ0 = p
  · obtain ⟨σ0, hσ0⟩ := hex
    have hσ0p : σ0 ^ p = 1 := hσ0 ▸ pow_orderOf_eq_one σ0
    refine fixPlaneGen_of_standard (spLinearAutGroup r K)
      {g | ∃ σ : K ≃+* K, orderOf σ = p ∧ g = fieldAut r K σ} hdesc
      (fixedSubgroup (fieldAut r K σ0)) ?_ ?_
    · rintro _ ⟨σ, hσ, rfl⟩
      have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
      have hfield : descentField σ = descentField σ0 := fixedField_eq_of_orderOf hℓ hf hK hσ hσ0
      rw [fixedSubgroup_fieldAut_eq_range_sp hpodd hσp, fixedSubgroup_fieldAut_eq_range_sp hpodd hσ0p,
        range_subfieldProj_eq_map, range_subfieldProj_eq_map, hfield]
    · rw [fixedSubgroup_fieldAut_eq_range_sp hpodd hσ0p, ← range_subfieldInj]
      exact planeGenIn_range (subfieldInj (r := r) σ0) (subfieldInj_injective σ0)
        (hinner σ0 hσ0)
  · refine fixPlaneGen_of_standard (spLinearAutGroup r K)
      {g | ∃ σ : K ≃+* K, orderOf σ = p ∧ g = fieldAut r K σ} hdesc ⊥ ?_ ?_
    · rintro _ ⟨σ, hσ, rfl⟩
      exact absurd ⟨σ, hσ⟩ hex
    · intro A hA _ _
      exact bot_le

theorem fixPlaneGen_projectiveSp_five {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K]
    {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) :
    FixPlaneGen (StatedProj (StatedSp r K)) p := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  refine fixPlaneGen_projectiveSp_of_inner hr hℓ hf hK hp hp2 ?_
  intro σ0 hσ0 E₁ hE₁ hc₁
  have hpf : p ∣ f ∧ Nat.card (descentField σ0) = ℓ ^ (f / p) :=
    CFSG.RankThree.PartOne.card_semilinearFixedSubfield hℓ hf hK hσ0
  have hf' : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf.1) hp.pos
  have : CFSG.IsElementaryAbelian p E₁ :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E₁).mpr hE₁
  refine closure_centralizers_psp_elementary hℓ hf' hpf.2 hp hp5 hpℓ hr ?_ E₁ hc₁
  rintro ⟨hr2, hq2⟩
  have hk2 : Nat.card (descentField σ0) = 2 := by rw [hpf.2]; exact hq2
  have hfin : Finite (descentField σ0) := inferInstance
  have h1 : p ^ 2 ∣ Nat.card (StatedProj (StatedSp r (descentField σ0))) := by
    rw [← hc₁]; exact Subgroup.card_subgroup_dvd_card E₁
  have h2 : Nat.card (StatedProj (StatedSp r (descentField σ0))) ∣
      Nat.card (StatedSp r (descentField σ0)) :=
    Subgroup.card_dvd_of_surjective (f := proj r (descentField σ0)) proj_surjective
  subst hr2
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp 2, hk2,
    show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)] at h2
  have h3 : p ^ 2 ∣ 720 := by simpa using h1.trans h2
  have h4 : p ^ 2 ≤ 720 := Nat.le_of_dvd (by norm_num) h3
  have h5 : p ≤ 26 := by nlinarith
  interval_cases p <;> first | omega | (exfalso; revert hp; norm_num)

theorem fixPlaneGen_symplectic_index_five {d : TauCeti.ValidLieTypeIndex}
    (hd : IsSymplecticIndex d.1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpd : p ≠ d.1.characteristic) : FixPlaneGen (Cat d) p := by
  obtain ⟨d, hv⟩ := d
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  rcases hd with ⟨q, rfl⟩ | ⟨r, q, rfl, hr3, hq2⟩ | ⟨r, q, rfl⟩
  ·
    have hq : p ≠ q.p := by simpa using hpd
    exact FixPlaneGen.of_mulEquiv (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv) hp
      (fixPlaneGen_projectiveSp_five le_rfl q.prime_p q.exponent_pos
        (CFSG.RankThree.PartOne.CTP.card_fixedField_B 2 q hv) hp hp5 hq)
  ·
    have hq : p ≠ q.p := by simpa using hpd
    exact FixPlaneGen.of_mulEquiv
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq2 hr3) hp
      (fixPlaneGen_projectiveSp_five (r := r) (by omega) q.prime_p q.exponent_pos
        (CFSG.RankThree.PartOne.CTP.card_fixedField_B r q hv) hp hp5 hq)
  ·
    have hq : p ≠ q.p := by simpa using hpd
    have hr3 : 3 ≤ r := hrange.1
    exact FixPlaneGen.of_mulEquiv (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv) hp
      (fixPlaneGen_projectiveSp_five (r := r) (by omega) q.prime_p q.exponent_pos (card_fixedField_C r q hv) hp hp5 hq)

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
