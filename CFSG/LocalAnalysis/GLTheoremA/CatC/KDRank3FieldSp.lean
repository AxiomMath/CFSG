module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3Field

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartTwo.Census CFSG.Assembly.RankThreeEven TauCeti
open KDRank3FieldAux

namespace KDRank3FieldAux

theorem dvd_exponent_of_dvd_outer_PSp_two {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (h : p ∣ Nat.card (Outer (StatedProj (StatedSp 2 K)))) : p ∣ f := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hchar : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have h1 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff K p] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1)
  obtain ⟨hgen, -⟩ := CFSG.RankThree.PartOne.AUTSL.SpTwo.automorphism_generation_two (K := K) h2
  obtain ⟨hID, -, hDnormE, -, -, -⟩ := standard_outer_quotient (K := K) (r := 2) (by omega)
  have hDN : (spLinearAutGroup 2 K).Normal :=
    ⟨fun d hd x => by
      have := hDnormE.conj_mem ⟨d, hgen ▸ Subgroup.mem_top d⟩ (Subgroup.mem_subgroupOf.2 hd)
        ⟨x, hgen ▸ Subgroup.mem_top x⟩
      exact Subgroup.mem_subgroupOf.1 this⟩
  have hDE : spLinearAutGroup 2 K ≤ spSemilinearAutGroup 2 K :=
    spLinearAutGroup_le_spSemilinearAutGroup
  have hE2 : ¬ p ∣ (spSemilinearAutGroup 2 K).index := by
    rw [hgen, Subgroup.index_top]; exact hp.not_dvd_one
  have hDI : ¬ p ∣ (inner (StatedProj (StatedSp 2 K))).relIndex (spLinearAutGroup 2 K) := by
    intro hd
    have h1 := hd.trans (relIndex_inner_spLinearAutGroup_dvd
      (r := 2) hp hf hK)
    have h3 : p ∣ 2 := h1.trans (Nat.gcd_dvd_left 2 _)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3)
  have hED : (spLinearAutGroup 2 K).relIndex (spSemilinearAutGroup 2 K) ∣ f := by
    set D := spLinearAutGroup 2 K
    set E := spSemilinearAutGroup 2 K
    haveI : (D.subgroupOf E).Normal := inferInstance
    let Φ : (K ≃+* K) →* ↥E ⧸ D.subgroupOf E :=
      (QuotientGroup.mk' (D.subgroupOf E)).comp
        ((fieldAut 2 K).codRestrict E fun σ => fieldAut_mem_spSemilinearAutGroup σ)
    have hΦ : Function.Surjective Φ := by
      intro y
      obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨A, σ, rfl⟩ := mem_spSemilinearAutGroup_iff.1 hx
      refine ⟨σ, ?_⟩
      change QuotientGroup.mk _ = QuotientGroup.mk _
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have := hDN.conj_mem _ (conjAut_mem_spLinearAutGroup (r := 2) (K := K) A)
        (fieldAut 2 K σ)⁻¹
      simpa [mul_assoc] using this
    have h1 : D.relIndex E = Nat.card (↥E ⧸ D.subgroupOf E) := rfl
    rw [h1, ← card_ringEquiv_eq hp hf hK]
    exact Subgroup.card_dvd_of_surjective hΦ
  exact dvd_of_dvd_index_chain hID hDE hp hDI hED hE2 h

end KDRank3FieldAux

theorem kdRank3Field_B2 (q : PrimePower) (hv : (LieTypeIndex.B 2 q).Valid) :
    KDRank3FieldAt ⟨.B 2 q, hv⟩ := by
  intro p hp hp2 S _ _ ⟨e⟩ hchar hrank hout
  set d : ValidLieTypeIndex := ⟨.B 2 q, hv⟩ with hd
  haveI hfin := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  haveI hFact : Fact p.Prime := ⟨hp⟩
  have hchar' : d.characteristic = p := hchar
  have hKc : Nat.card ↥d.fixedField = p ^ q.exponent := by
    rw [ValidLieTypeIndex.card_fixedField, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      hchar']
    have he : d.fieldExponent = q.exponent := LieTypeIndex.fieldExponent_B 2 q
    rw [he]
  haveI hcp : CharP ↥d.fixedField p := by
    haveI := Fintype.ofFinite ↥d.fixedField
    exact charP_of_card_eq_prime_pow (f := q.exponent)
      (by rw [← Nat.card_eq_fintype_card]; exact hKc)
  let e1 := e.trans (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)
  have hout' : p ∣ Nat.card (Outer (StatedProj (StatedSp 2 ↥d.fixedField))) := by
    rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e1).toEquiv]
    exact hout
  have hpf : p ∣ q.exponent :=
    dvd_exponent_of_dvd_outer_PSp_two hp hp2 q.exponent_pos hKc hout'
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hf3 : 3 ≤ q.exponent := hp3.trans (Nat.le_of_dvd q.exponent_pos hpf)
  exfalso
  have h1 := le_gla_of_carrier e1 hp (le_localRank_PSp_two hp2 hKc)
  omega


theorem kdRank3Field_C (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.C r q).Valid) :
    KDRank3FieldAt ⟨.C r q, hv⟩ := by
  intro p hp hp2 S _ _ ⟨e⟩ hchar hrank hout
  have hr : 3 ≤ r := ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).1
  set d : ValidLieTypeIndex := ⟨.C r q, hv⟩ with hd
  haveI hfin := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  haveI hFact : Fact p.Prime := ⟨hp⟩
  have hchar' : d.characteristic = p := hchar
  have hKc : Nat.card ↥d.fixedField = p ^ q.exponent := by
    rw [ValidLieTypeIndex.card_fixedField, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      hchar']
    have he : d.fieldExponent = q.exponent := LieTypeIndex.fieldExponent_C r q
    rw [he]
  haveI hcp : CharP ↥d.fixedField p := by
    haveI := Fintype.ofFinite ↥d.fixedField
    exact charP_of_card_eq_prime_pow (f := q.exponent)
      (by rw [← Nat.card_eq_fintype_card]; exact hKc)
  let e1 := e.trans (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv)
  exfalso
  have h1 := le_gla_of_carrier e1 hp (le_localRank_PSp (r := r) hp2 hKc hr)
  have := q.exponent_pos
  nlinarith

end CFSG.LocalAnalysis.GLTheoremA
