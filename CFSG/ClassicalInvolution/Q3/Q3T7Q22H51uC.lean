module

public import CFSG.ClassicalInvolution.Q3.Q3NFPair
public import CFSG.ClassicalInvolution.Q3.Q3T6DH51Facts

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement


section Exact

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {c : G} {ι : Type}

theorem natCard_modOdd3 (hΦ : SecData3 c Φ)
    (D : LieSystemData3 ι (↥(centralizingLayer Φ {c}) ⧸
      classicalInvolutionOddCore ↥(centralizingLayer Φ {c}))
      (oddQuotientFamily (restrictFamily (centralizingMembers Φ {c})
        (centralizingLayer Φ {c}))))
    {M : Subgroup G} (hM : M ∈ Φ) : Nat.card (modOdd c M) = 24 := by
  have hN := normalizesLayer_of_secData3 hΦ
  have hMc : M ∈ centMembers Φ c := ⟨hM, hΦ.le M hM⟩
  have hMY : M ≤ centralizingLayer Φ {c} := le_centLayer hMc
  have hfam : modOddIn (centralizingLayer Φ {c}) M ∈ oddQuotientFamily
      (restrictFamily (centralizingMembers Φ {c}) (centralizingLayer Φ {c})) :=
    ⟨_, ⟨_, hMc, hMY, rfl⟩, rfl⟩
  have h1 : Nat.card (modOdd c M) = Nat.card (modOddIn (centralizingLayer Φ {c}) M) := by
    rw [← map_sectionQuotientHom_modOddIn hN hMc]
    exact Subgroup.card_map_of_injective (sectionQuotientHom_injective hN)
  rw [h1]
  exact D.card_eq _ hfam

theorem oddCoreIn_le_layer3 (hΦ : SecData3 c Φ)
    (D : LieSystemData3 ι (↥(centralizingLayer Φ {c}) ⧸
      classicalInvolutionOddCore ↥(centralizingLayer Φ {c}))
      (oddQuotientFamily (restrictFamily (centralizingMembers Φ {c})
        (centralizingLayer Φ {c}))))
    {M : Subgroup G} (hM : M ∈ Φ) : oddCoreIn M ≤ oddCoreIn (centralizingLayer Φ {c}) := by
  have hMc : M ∈ centMembers Φ c := ⟨hM, hΦ.le M hM⟩
  have hMY : M ≤ centralizingLayer Φ {c} := le_centLayer hMc
  have hfam : modOddIn (centralizingLayer Φ {c}) M ∈ oddQuotientFamily
      (restrictFamily (centralizingMembers Φ {c}) (centralizingLayer Φ {c})) :=
    ⟨_, ⟨_, hMc, hMY, rfl⟩, rfl⟩
  obtain ⟨z, hz⟩ := hΦ.member M hM
  obtain ⟨e⟩ := hz.nonempty_equiv
  refine Q3NF.oddCoreIn_le_of_card_modOddIn hMY ?_
  rw [D.card_eq _ hfam, Nat.card_congr e.toEquiv, natCard_sl2Three]

theorem oddQuotMk_eq_one_of_mem_oddCoreIn_layer3 (hΦ : SecData3 c Φ) {x : G}
    (hx : x ∈ oddCoreIn (centralizingLayer Φ {c}))
    (hxC : x ∈ Subgroup.centralizer ({c} : Set G)) : oddQuotMk c ⟨x, hxC⟩ = 1 := by
  obtain ⟨d, hd, rfl⟩ := hx
  have hN := normalizesLayer_of_secData3 hΦ
  exact MonoidHom.mem_ker.mp ((ker_layerToOddQuot_of_normalizes hN).ge hd)

theorem oddQuotMk_comm_of_commutator_mem3 (hΦ : SecData3 c Φ)
    (D : LieSystemData3 ι (↥(centralizingLayer Φ {c}) ⧸
      classicalInvolutionOddCore ↥(centralizingLayer Φ {c}))
      (oddQuotientFamily (restrictFamily (centralizingMembers Φ {c})
        (centralizingLayer Φ {c}))))
    {M : Subgroup G} (hM : M ∈ Φ) {a b : G} (ha : a ∈ Subgroup.centralizer ({c} : Set G))
    (hb : b ∈ Subgroup.centralizer ({c} : Set G)) (h : ⁅a, b⁆ ∈ oddCoreIn M) :
    oddQuotMk c ⟨a, ha⟩ * oddQuotMk c ⟨b, hb⟩ = oddQuotMk c ⟨b, hb⟩ * oddQuotMk c ⟨a, ha⟩ := by
  have hO := oddCoreIn_le_layer3 hΦ D hM h
  have hC : ⁅a, b⁆ ∈ Subgroup.centralizer ({c} : Set G) := by
    rw [commutatorElement_def]
    exact (Subgroup.centralizer ({c} : Set G)).mul_mem
      ((Subgroup.centralizer ({c} : Set G)).mul_mem
        ((Subgroup.centralizer ({c} : Set G)).mul_mem ha hb)
        ((Subgroup.centralizer ({c} : Set G)).inv_mem ha))
      ((Subgroup.centralizer ({c} : Set G)).inv_mem hb)
  have h1 := oddQuotMk_eq_one_of_mem_oddCoreIn_layer3 hΦ hO hC
  have h2 : oddQuotMk c ⟨⁅a, b⁆, hC⟩ =
      ⁅oddQuotMk c ⟨a, ha⟩, oddQuotMk c ⟨b, hb⟩⁆ := by
    have : (⟨⁅a, b⁆, hC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) =
        ⁅(⟨a, ha⟩ : ↥(Subgroup.centralizer ({c} : Set G))), ⟨b, hb⟩⁆ := rfl
    rw [this, map_commutatorElement]
  rw [h2] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem eq_one_of_isPGroup_of_oddQuotMk_eq_one3 {P : Subgroup G} (hP : IsPGroup 2 P)
    {x : ↥(Subgroup.centralizer ({c} : Set G))} (hxP : (x : G) ∈ P) (h : oddQuotMk c x = 1) :
    x = 1 := by
  have hmem := oddQuotMk_eq_one_iff.mp h
  have hdvd : orderOf x ∣ Nat.card (componentClassificationOddCore
      ↥(Subgroup.centralizer ({c} : Set G))) := Subgroup.orderOf_dvd_natCard _ hmem
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨(x : G), hxP⟩
  have hk' : orderOf x = 2 ^ k := by
    rw [← Subgroup.orderOf_coe x]
    exact (Subgroup.orderOf_coe (⟨(x : G), hxP⟩ : ↥P)).trans hk
  rcases k with _ | k
  · exact orderOf_eq_one_iff.mp (by simpa using hk')
  · exfalso
    rw [hk'] at hdvd
    have h2 : 2 ∣ Nat.card (componentClassificationOddCore
        ↥(Subgroup.centralizer ({c} : Set G))) :=
      (Dvd.intro_left (2 ^ k) (by ring)).trans hdvd
    exact (Nat.not_even_iff_odd.mpr
      (OddCore.odd_card ↥(Subgroup.centralizer ({c} : Set G)))) (even_iff_two_dvd.mpr h2)

theorem natCard_modOdd_of_isPGroup3 {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPC : P ≤ Subgroup.centralizer ({c} : Set G)) : Nat.card (modOdd c P) = Nat.card P := by
  set φ : ↥P →* OddQuot c := (oddQuotMk c).comp (Subgroup.inclusion hPC) with hφ
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : Subgroup.inclusion hPC x = 1 :=
      eq_one_of_isPGroup_of_oddQuotMk_eq_one3 hP (x := Subgroup.inclusion hPC x) x.2 hx
    exact Subgroup.inclusion_injective hPC (h1.trans (map_one _).symm)
  have hrange : φ.range = modOdd c P := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Subgroup.inclusion hPC y, y.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem le_of_modOdd_eq_of_commutes3 (hΦ : SecData3 c Φ)
    (D : LieSystemData3 ι (↥(centralizingLayer Φ {c}) ⧸
      classicalInvolutionOddCore ↥(centralizingLayer Φ {c}))
      (oddQuotientFamily (restrictFamily (centralizingMembers Φ {c})
        (centralizingLayer Φ {c}))))
    {M M' : Subgroup G} (hM : M ∈ Φ) (hM' : M' ∈ Φ) (heq : modOdd c M = modOdd c M')
    {P P' : Subgroup G} (hPM : P ≤ M) (hP'M' : P' ≤ M') (hP : IsPGroup 2 P) (hP' : IsPGroup 2 P')
    (hcomm : Commutes P P') (h8 : 8 ≤ Nat.card P) : P' ≤ P := by
  have hMC := hΦ.le M hM
  have hM'C := hΦ.le M' hM'
  have hPC : P ≤ Subgroup.centralizer ({c} : Set G) := hPM.trans hMC
  have hP'C : P' ≤ Subgroup.centralizer ({c} : Set G) := hP'M'.trans hM'C
  have hT : IsPGroup 2 ↥(P ⊔ P') :=
    hP.to_sup_of_normal_right' hP' (Asc77.T7A.le_normalizer_of_commutes hcomm.symm)
  have hTC : P ⊔ P' ≤ Subgroup.centralizer ({c} : Set G) := sup_le hPC hP'C
  have hle : modOdd c (P ⊔ P') ≤ modOdd c M := by
    rintro _ ⟨k, hk, rfl⟩
    have hk' : (k : G) ∈ P ⊔ P' := Subgroup.mem_subgroupOf.mp hk
    have h1 := Q3T6D.oddQuotMk_mem_sup3 hMC hM'C (sup_le_sup hPM hP'M' hk') k.2
    rw [← heq, sup_idem] at h1
    exact h1
  have hcard : Nat.card ↥(P ⊔ P') ∣ 24 := by
    rw [← natCard_modOdd3 hΦ D hM, ← natCard_modOdd_of_isPGroup3 hT hTC]
    exact Subgroup.card_dvd_of_le hle
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  have h2k : Nat.card ↥(P ⊔ P') ≤ 8 := by
    rw [hk] at hcard ⊢
    have hle24 : 2 ^ k ≤ 24 := Nat.le_of_dvd (by norm_num) hcard
    have hk5 : k < 5 := by
      by_contra hcon
      have : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hcon)
      omega
    interval_cases k <;> first | (exfalso; revert hcard; decide) | norm_num
  have hPT : P = P ⊔ P' := Subgroup.eq_of_le_of_card_ge le_sup_left (h2k.trans h8)
  rw [hPT]
  exact le_sup_right

end Exact

end CFSG.ClassicalInvolution.Q3.Q3T7
