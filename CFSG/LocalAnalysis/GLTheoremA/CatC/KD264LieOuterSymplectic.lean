module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterInnerPrime
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.OrthOuterThree
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.OrthOuterThreeAux.SympPrimeSubfieldOdd
public import CFSG.Adapters.TauCetiLieModels

public section

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Timmesfeld.LocalTwo
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.RankThree.CASymplecticSubfield
open CFSG.RankThree.PartOne.KCSpComm CFSG.RankThree.PartOne.KCSpFull
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

theorem fieldCoreAt_fieldAut_psp {ℓ f r p : ℕ} {K : Type} [Field K] [Finite K]
    (hℓ : ℓ.Prime) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hf : 1 ≤ f) (hr : 2 ≤ r)
    (hK : Nat.card K = ℓ ^ f) {σ : K ≃+* K} (hσ : orderOf σ = p)
    (hk : ∃ k ∈ subfieldFixedGroup K r σ, orderOf k = p) :
    FieldCoreAt p (fieldAut r K σ) := by
  obtain ⟨-, -, -, -, -, hJfix, -, hJs, -, hfixing, hzp, hzcard, -, -⟩ :=
    symplectic_prime_subfield_fixed_group_and_full_centralizer_odd (K := K) hℓ hp hp2 hpℓ hf hr
      hK σ hσ
  have hδp : orderOf (fieldAut r K σ) = p := by rw [← Nat.card_zpowers, hzcard]
  by_cases hex : r = 2 ∧ ℓ ^ (f / p) = 2
  · obtain ⟨rfl, hexc⟩ := hex
    exact fieldCoreAt_fieldAut_sp_two_exc hℓ hp hp2 hpℓ hf hK σ hσ hexc hk
  · obtain ⟨hJsimple, hJnc⟩ := hJs hex
    have hJq : CFSG.IsQuasisimple (subfieldFixedGroup K r σ) :=
      isQuasisimple_of_simple_nonabelian (fun hc => by
        obtain ⟨a, b, hab⟩ := hJnc
        exact hab (hc a b))
    have hJp : ¬ Nat.Coprime p (Nat.card (subfieldFixedGroup K r σ)) := by
      obtain ⟨k, hk, hkord⟩ := hk
      have hdvd : p ∣ Nat.card (subfieldFixedGroup K r σ) := by
        have h1 : orderOf (⟨k, hk⟩ : subfieldFixedGroup K r σ) = p := by
          rw [Subgroup.orderOf_mk]
          exact hkord
        rw [← h1]
        exact orderOf_dvd_natCard _
      exact fun hc => (Nat.Prime.coprime_iff_not_dvd hp).1 hc hdvd
    refine fieldCoreAt_of_fixSub_eq hδp hJq hJfix ?_ hJp
    intro β hβ
    have hβmem : β ∈ fixingSubgroup (MulAut (StatedProj (StatedSp r K)))
        ((subfieldFixedGroup K r σ : Subgroup (StatedProj (StatedSp r K))) :
          Set (StatedProj (StatedSp r K))) :=
      (mem_fixingSubgroup_iff _).2 fun u hu => hβ u hu
    rw [hfixing, hzp] at hβmem
    exact hβmem

theorem exists_conj_fieldAut_psp {ℓ f r p : ℕ} {K : Type} [Field K] [Finite K]
    (hℓ : ℓ.Prime) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hf : 1 ≤ f) (hr : 2 ≤ r)
    (hK : Nat.card K = ℓ ^ f) (hrq : ¬ (r = 2 ∧ ℓ ^ f = 2))
    {a : MulAut (StatedProj (StatedSp r K))} (hap : a ^ p = 1)
    (haH : a ∉ inner (StatedProj (StatedSp r K)))
    (hpdvd : p ∣ Nat.card (StatedProj (StatedSp r K))) :
    ∃ (σ : K ≃+* K) (h : MulAut (StatedProj (StatedSp r K))),
      orderOf σ = p ∧ h ∈ spLinearAutGroup r K ∧
        a = h * fieldAut r K σ * h⁻¹ ∧
        ∃ k ∈ subfieldFixedGroup K r σ, orderOf k = p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have O : SpOuter ℓ f r K := spOuter hℓ hf hr hK
  have hinj : Function.Injective (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))) := spConj_injective hℓ hf hK hr hrq
  have haE : a ∈ spSemilinearAutGroup r K :=
    mem_of_odd_orderOf_of_index_dvd_two _ O.index_dvd
      (Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hap))
  have haD : a ∉ spLinearAutGroup r K := by
    haveI := inner_normal (StatedProj (StatedSp r K))
    exact fun hD => haH (mem_of_pow_eq_one_of_relIndex_dvd_two
      (H := inner (StatedProj (StatedSp r K))) (D := spLinearAutGroup r K)
      (O.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)) hp hp2 hD hap)
  have ha1 : a ≠ 1 := fun h => haH (h ▸ one_mem _)
  obtain ⟨-, σ, hσ, h, hh, hxh⟩ := O.descent p hp a haE haD (orderOf_eq_prime hap ha1)
  obtain ⟨y, hy, hy1, hyp, hcomm⟩ := exists_innerAut_orderOf_prime_commute hp hinj hap hpdvd
  obtain ⟨t, rfl⟩ := hy
  obtain ⟨k, hkσ, hkord⟩ := exists_fixed_orderOf_of_canonical_conj hp hinj hxh ⟨t, rfl⟩ hy1 hyp
    hcomm
  obtain ⟨-, -, -, -, -, hJfix, -, -, -, -, -, -, -⟩ :=
    symplectic_prime_subfield_fixed_group_and_full_centralizer_odd (K := K) hℓ hp hp2 hpℓ hf hr
      hK σ hσ
  exact ⟨σ, h, hσ, hh, hxh, k, (hJfix k).2 hkσ, hkord⟩

theorem fieldCoreAt_psp_of_outer {ℓ f r p : ℕ} {K : Type} [Field K] [Finite K]
    (hℓ : ℓ.Prime) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hf : 1 ≤ f) (hr : 2 ≤ r)
    (hK : Nat.card K = ℓ ^ f) (hrq : ¬ (r = 2 ∧ ℓ ^ f = 2))
    {a : MulAut (StatedProj (StatedSp r K))} (hap : a ^ p = 1)
    (haH : a ∉ inner (StatedProj (StatedSp r K)))
    (hpdvd : p ∣ Nat.card (StatedProj (StatedSp r K))) : FieldCoreAt p a := by
  obtain ⟨σ, h, hσ, -, hxh, hk⟩ :=
    exists_conj_fieldAut_psp hℓ hp hp2 hpℓ hf hr hK hrq hap haH hpdvd
  have hδ : FieldCoreAt p (fieldAut r K σ) :=
    fieldCoreAt_fieldAut_psp hℓ hp hp2 hpℓ hf hr hK hσ hk
  exact fieldCoreAt_of_conj hδ h⁻¹ (by rw [hxh]; group)

theorem outerPLayerAt_psp {ℓ f r p : ℕ} {K : Type} [Field K] [Finite K]
    (hℓ : ℓ.Prime) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hf : 1 ≤ f) (hr : 2 ≤ r)
    (hK : Nat.card K = ℓ ^ f) (hrq : ¬ (r = 2 ∧ ℓ ^ f = 2))
    {S : Type} [Group S] [Finite S] (e : S ≃* StatedProj (StatedSp r K))
    (hpdvd : p ∣ Nat.card S) : OuterPLayerAt p S := by
  refine outerPLayerAt_of_mulEquiv_of_fieldCoreAt hp e fun x hxp hxo => ?_
  have hxH : x ∉ inner (StatedProj (StatedSp r K)) := fun h => hxo (inner_le_innAutDerived _ h)
  have hpdvdM : p ∣ Nat.card (StatedProj (StatedSp r K)) := by
    rw [← Nat.card_congr e.toEquiv]
    exact hpdvd
  exact fieldCoreAt_psp_of_outer hℓ hp hp2 hpℓ hf hr hK hrq hxp hxH hpdvdM

theorem outerPLayerAt_of_statedClassicalModel_PSp {p r ℓ f : ℕ} {S : Type} [Group S] [Finite S]
    (hp : p.Prime) (hp2 : p ≠ 2) (h : CFSG.Open.StatedClassicalModel S .PSp r ℓ f)
    (hpℓ : p ≠ ℓ) (hpdvd : p ∣ Nat.card S) : OuterPLayerAt p S := by
  obtain ⟨hadm, K, _, _, hK, ⟨eK⟩⟩ := h
  have hrq : ¬ (r = 2 ∧ ℓ ^ f = 2) := by
    rintro ⟨rfl, h2⟩
    exact hadm.2.2.2 (by rw [h2])
  exact outerPLayerAt_psp hadm.1 hp hp2 hpℓ hadm.2.1 hadm.2.2.1 hK hrq eK hpdvd

theorem outerPLayerAt_C {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {r : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.C r q).Valid)
    {S : Type} [Group S] [Finite S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.C r q, hv⟩).Group)
    (hnot : ¬ CFSG.Yardstones.Md0ec50421ce4.IsChevSimple p S) (hpdvd : p ∣ Nat.card S) :
    OuterPLayerAt p S := by
  have hpq : q.p ≠ p := by
    have h := characteristic_ne_of_not_isChevSimple hv ⟨e⟩ hnot
    rwa [TauCeti.LieTypeIndex.characteristic_C] at h
  have hr2 : 2 ≤ r := (CFSG.Models.lieModel_C r q hv e).1.2.2.1
  have hSC : CFSG.Open.StatedClassicalModel S .PSp r q.p q.exponent := by
    rcases (CFSG.Models.lieModel_C r q hv e).2 with h | ⟨hr0, -⟩
    · exact h
    · omega
  exact outerPLayerAt_of_statedClassicalModel_PSp hp hp2 hSC hpq.symm hpdvd

theorem outerPLayerAt_of_lieModel_B_PSp {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {r : ℕ} {q : TauCeti.PrimePower} {S : Type} [Group S] [Finite S]
    (h : CFSG.Models.LieModel S .PSp r q.p q.exponent)
    (hpq : q.p ≠ p) (hpdvd : p ∣ Nat.card S) : OuterPLayerAt p S := by
  have hr2 : 2 ≤ r := h.1.2.2.1
  exact outerPLayerAt_of_statedClassicalModel_PSp hp hp2
    (by rcases h.2 with h' | ⟨hr0, -⟩
        · exact h'
        · omega) hpq.symm hpdvd

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
